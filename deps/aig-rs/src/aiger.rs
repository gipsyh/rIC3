//! Native AIGER 1.9 codec. Binary ANDs are decoded directly into `AigNode`s.
use crate::{Aig, AigLatch, AigNode};
use giputils::hash::GHashMap;
use logicrs::{Lit, Var};
use std::{
    fmt, fs,
    io::{self, Write},
    path::Path,
};

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn edge(lit: u32) -> Lit {
    Lit::new(Var(lit / 2), lit & 1 == 0)
}

struct Decoder<'a> {
    bytes: &'a [u8],
    pos: usize,
    maxvar: u32,
}

impl<'a> Decoder<'a> {
    fn error(&self, message: &str) -> io::Error {
        invalid(format!("AIGER byte {}: {message}", self.pos))
    }

    fn line(&mut self) -> io::Result<&'a [u8]> {
        let start = self.pos;
        let len = self.bytes[start..]
            .iter()
            .position(|&b| b == b'\n')
            .ok_or_else(|| self.error("missing newline / truncated file"))?;
        self.pos += len + 1;
        Ok(&self.bytes[start..start + len])
    }

    fn number(&self, bytes: &[u8]) -> io::Result<u32> {
        if bytes.is_empty() {
            return Err(self.error("expected unsigned integer"));
        }
        let mut n = 0u32;
        for &b in bytes {
            if !b.is_ascii_digit() {
                return Err(self.error("invalid unsigned integer"));
            }
            n = n
                .checked_mul(10)
                .and_then(|n| n.checked_add((b - b'0') as u32))
                .ok_or_else(|| self.error("integer overflow"))?;
        }
        Ok(n)
    }

    fn row<const N: usize>(&mut self, min: usize) -> io::Result<[u32; N]> {
        let line = self.line()?;
        let mut result = [0; N];
        let mut count = 0;
        for token in line.split(|&b| b == b' ') {
            if count == N {
                return Err(self.error("too many fields"));
            }
            result[count] = self.number(token)?;
            count += 1;
        }
        if count < min {
            return Err(self.error("missing fields"));
        }
        Ok(result)
    }

    fn literal(&self, lit: u32) -> io::Result<Lit> {
        if lit == u32::MAX {
            return Err(self.error("literal is reserved for Lit::NONE"));
        }
        if lit / 2 > self.maxvar {
            return Err(self.error("literal exceeds maximum variable"));
        }
        Ok(edge(lit))
    }

    fn edges(&mut self, count: u32) -> io::Result<Vec<Lit>> {
        self.check_count(count as u64, 2)?;
        (0..count)
            .map(|_| {
                let [lit] = self.row::<1>(1)?;
                self.literal(lit)
            })
            .collect()
    }

    fn check_count(&self, count: u64, min_bytes: usize) -> io::Result<()> {
        if count > ((self.bytes.len() - self.pos) / min_bytes) as u64 {
            return Err(self.error("section count exceeds remaining data"));
        }
        Ok(())
    }

    #[inline]
    fn delta(&mut self) -> io::Result<u32> {
        let mut value = 0;
        for shift in (0..35).step_by(7) {
            let b = *self
                .bytes
                .get(self.pos)
                .ok_or_else(|| self.error("truncated binary delta"))?;
            self.pos += 1;
            if shift == 28 && b > 15 {
                return Err(self.error("binary delta overflow"));
            }
            value |= ((b & 127) as u32) << shift;
            if b < 128 {
                return Ok(value);
            }
        }
        Err(self.error("invalid binary delta"))
    }
}

impl Aig {
    /// Read binary `.aig` or ASCII `.aag` directly into Rust storage.
    ///
    /// Binary IDs are preserved; ASCII IDs are compacted into input/latch/AND order,
    /// with a topological sort when needed. Only input and latch names are retained;
    /// other symbol names and comments are discarded.
    pub fn read_aiger(bytes: &[u8]) -> io::Result<Self> {
        let mut d = Decoder {
            bytes,
            pos: 0,
            maxvar: 0,
        };
        let header = d.line()?;
        let binary = match header.get(..4) {
            Some(b"aig ") => true,
            Some(b"aag ") => false,
            _ => return Err(d.error("expected 'aig ' or 'aag ' header")),
        };
        let mut counts = [0u32; 9];
        let mut fields = 0;
        for token in header[4..].split(|&b| b == b' ') {
            if fields == 9 {
                return Err(d.error("too many header fields"));
            }
            counts[fields] = d.number(token)?;
            fields += 1;
        }
        if fields < 5 {
            return Err(d.error("incomplete header"));
        }
        let [m, i, l, o, a, b, c, j, f] = counts;
        d.maxvar = m;
        if m > u32::MAX / 2 {
            return Err(d.error("maximum variable exceeds literal range"));
        }
        let defined = i as u64 + l as u64 + a as u64;
        if defined > m as u64 || (binary && defined != m as u64) {
            return Err(d.error("inconsistent maximum variable / node counts"));
        }
        // Bound allocation using bytes that must exist in each encoded section.
        d.check_count(
            a as u64 + l as u64 + o as u64 + b as u64 + c as u64 + j as u64 + f as u64,
            2,
        )?;
        if !binary {
            d.check_count(i as u64, 2)?;
        }
        let mut aig = Self::new();
        aig.nodes
            .try_reserve_exact(defined as usize)
            .map_err(io::Error::other)?;
        let mut ids = GHashMap::default();
        let mut define = |aig: &mut Aig, lit: u32, node: AigNode| -> io::Result<Var> {
            if lit == 0 || lit & 1 != 0 || lit / 2 > m {
                return Err(invalid("invalid input, latch, or AND definition"));
            }
            let id = Var::new(aig.nodes.len());
            if !binary && ids.insert((lit / 2) as usize, id).is_some() {
                return Err(invalid("duplicate variable definition"));
            }
            aig.nodes.push(node);
            Ok(id)
        };
        for n in 0..i {
            let lit = if binary {
                2 * (n + 1)
            } else {
                d.row::<1>(1)?[0]
            };
            let id = define(&mut aig, lit, AigNode::LEAF)?;
            aig.inputs.push(id);
        }
        for n in 0..l {
            let (lit, next, reset) = if binary {
                let [next, reset] = d.row::<2>(1)?;
                (2 * (i + n + 1), next, reset)
            } else {
                let [lit, next, reset] = d.row::<3>(2)?;
                (lit, next, reset)
            };
            let next = d.literal(next)?;
            let init = match reset {
                0 | 1 => Some(edge(reset)),
                r if r == lit => None,
                _ => return Err(d.error("latch reset must be 0, 1, or its own literal")),
            };
            let input = define(&mut aig, lit, AigNode::LEAF)?;
            aig.latchs.push(AigLatch { input, next, init });
        }
        aig.outputs = d.edges(o)?;
        aig.bads = d.edges(b)?;
        aig.constraints = d.edges(c)?;
        let mut sizes = Vec::new();
        for _ in 0..j {
            sizes.push(d.row::<1>(1)?[0]);
        }
        for size in sizes {
            aig.justice.push(d.edges(size)?);
        }
        aig.fairness = d.edges(f)?;
        if binary {
            for id in (i as usize + l as usize + 1)..=m as usize {
                let lhs = (id as u32) * 2;
                let rhs0 = lhs
                    .checked_sub(d.delta()?)
                    .ok_or_else(|| d.error("invalid first delta"))?;
                let rhs1 = rhs0
                    .checked_sub(d.delta()?)
                    .ok_or_else(|| d.error("invalid second delta"))?;
                if rhs0 / 2 >= id as u32 {
                    return Err(d.error("AND is not topologically ordered"));
                }
                aig.nodes.push(AigNode::new_and(edge(rhs0), edge(rhs1)));
            }
        } else {
            for _ in 0..a {
                let [lhs, rhs0, rhs1] = d.row::<3>(3)?;
                let node = AigNode::new_and(d.literal(rhs0)?, d.literal(rhs1)?);
                define(&mut aig, lhs, node)?;
            }
            // AAG permits sparse IDs and forward references; compact without allocating M slots.
            let remap = |e: Lit| -> io::Result<Lit> {
                if usize::from(e.var()) == 0 {
                    return Ok(e);
                }
                ids.get(&usize::from(e.var()))
                    .map(|&id| Lit::from(id).not_if(!e.polarity()))
                    .ok_or_else(|| invalid("reference to undefined variable"))
            };
            for node in aig.nodes.iter_mut() {
                if node.is_and() {
                    let (x, y) = node.fanin();
                    *node = AigNode::new_and(remap(x)?, remap(y)?);
                }
            }
            aig.map_references(&remap)?;
        }
        // Only input/latch symbols have storage in Aig, matching the former C bridge.
        let mut seen = GHashMap::default();
        while d.pos < bytes.len() {
            let line = d.line()?;
            if line == b"c" {
                if d.pos < bytes.len() && bytes.last() != Some(&b'\n') {
                    return Err(d.error("missing newline after comment"));
                }
                break;
            }
            let sep = line
                .iter()
                .position(|&b| b == b' ')
                .ok_or_else(|| d.error("invalid symbol"))?;
            if sep < 2 {
                return Err(d.error("missing symbol index"));
            }
            let index = d.number(&line[1..sep])? as usize;
            let (count, id) = match line[0] {
                b'i' => (aig.inputs.len(), aig.inputs.get(index).copied()),
                b'l' => (aig.latchs.len(), aig.latchs.get(index).map(|l| l.input)),
                b'o' => (o as usize, None),
                b'b' => (b as usize, None),
                b'c' => (c as usize, None),
                b'j' => (j as usize, None),
                b'f' => (f as usize, None),
                _ => return Err(d.error("unknown symbol kind")),
            };
            if index >= count || seen.insert((line[0], index), ()).is_some() {
                return Err(d.error("out-of-range or duplicate symbol"));
            }
            if let Some(id) = id {
                let name = std::str::from_utf8(&line[sep + 1..])
                    .map_err(|_| d.error("symbol is not UTF-8"))?;
                if name.contains('\0') {
                    return Err(d.error("NUL in symbol"));
                }
                aig.symbols.insert(id, name.to_owned());
            }
        }
        if !binary
            && aig
                .nodes
                .iter()
                .enumerate()
                .filter(|(_, n)| n.is_and())
                .any(|(id, n)| {
                    usize::from(n.fanin0().var()) >= id || usize::from(n.fanin1().var()) >= id
                })
        {
            let order = aig.gate_order()?;
            aig = aig.reordered(&order);
        }
        Ok(aig)
    }

    fn map_references(&mut self, map: &impl Fn(Lit) -> io::Result<Lit>) -> io::Result<()> {
        for l in &mut self.latchs {
            l.next = map(l.next)?;
        }
        for e in self
            .outputs
            .iter_mut()
            .chain(&mut self.bads)
            .chain(&mut self.constraints)
            .chain(self.justice.iter_mut().flatten())
            .chain(&mut self.fairness)
        {
            *e = map(*e)?;
        }
        Ok(())
    }

    /// Fallible file API. Errors include the offending byte offset where available.
    pub fn try_from_file<P: AsRef<Path>>(path: P) -> io::Result<Self> {
        Self::read_aiger(&fs::read(path)?)
    }

    /// Backwards-compatible convenience API; panics on invalid input or I/O failure.
    pub fn from_file<P: AsRef<Path>>(path: P) -> Self {
        Self::try_from_file(&path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.as_ref().display()))
    }

    // Iterative postorder traversal also handles arbitrarily deep AAGs without recursion.
    fn gate_order(&self) -> io::Result<Vec<usize>> {
        let mut state = vec![0u8; self.nodes.len()];
        let mut order = Vec::new();
        let mut stack = Vec::new();
        for (id, _) in self.nodes.iter().enumerate().filter(|(_, n)| n.is_and()) {
            stack.push((id, false));
            while let Some((id, exit)) = stack.pop() {
                let node = self
                    .nodes
                    .get(id)
                    .ok_or_else(|| invalid("undefined fanin"))?;
                if !node.is_and() || state[id] == 2 {
                    continue;
                }
                if exit {
                    state[id] = 2;
                    order.push(id);
                } else {
                    if state[id] == 1 {
                        return Err(invalid("combinational cycle"));
                    }
                    state[id] = 1;
                    stack.push((id, true));
                    stack.push((usize::from(node.fanin1().var()), false));
                    stack.push((usize::from(node.fanin0().var()), false));
                }
            }
        }
        Ok(order)
    }

    fn reordered(&self, order: &[usize]) -> Self {
        let mut map = vec![Var::CONST; self.nodes.len()];
        for (index, id) in self
            .inputs
            .iter()
            .copied()
            .chain(self.latchs.iter().map(|l| l.input))
            .chain(order.iter().copied().map(Var::new))
            .enumerate()
        {
            map[usize::from(id)] = Var::new(index + 1);
        }
        let mut result = Self::new();
        result.nodes.reserve(self.nodes.len() - 1);
        for &id in &self.inputs {
            let input = result.new_leaf_node();
            result.inputs.push(input);
            debug_assert_eq!(map[usize::from(id)], Var::new(result.nodes.len() - 1));
        }
        for l in &self.latchs {
            let input = result.new_leaf_node();
            result.latchs.push(AigLatch {
                input,
                next: l.next.map_var(|id| map[usize::from(id)]),
                init: l.init,
            });
        }
        for &id in order {
            let n = &self.nodes[id];
            result.nodes.push(AigNode::new_and(
                n.fanin0().map_var(|id| map[usize::from(id)]),
                n.fanin1().map_var(|id| map[usize::from(id)]),
            ));
        }
        result.outputs = self
            .outputs
            .iter()
            .map(|e| e.map_var(|id| map[usize::from(id)]))
            .collect();
        result.bads = self
            .bads
            .iter()
            .map(|e| e.map_var(|id| map[usize::from(id)]))
            .collect();
        result.constraints = self
            .constraints
            .iter()
            .map(|e| e.map_var(|id| map[usize::from(id)]))
            .collect();
        result.justice = self
            .justice
            .iter()
            .map(|j| {
                j.iter()
                    .map(|e| e.map_var(|id| map[usize::from(id)]))
                    .collect()
            })
            .collect();
        result.fairness = self
            .fairness
            .iter()
            .map(|e| e.map_var(|id| map[usize::from(id)]))
            .collect();
        result.symbols = self
            .symbols
            .iter()
            .filter_map(|(&id, s)| {
                map.get(usize::from(id))
                    .filter(|&&v| v != 0)
                    .map(|&v| (v, s.clone()))
            })
            .collect();
        result
    }

    /// Validate public graph storage before emitting a file. Returns whether binary IDs are canonical.
    fn validate_aiger(&self) -> io::Result<bool> {
        if self.nodes.is_empty()
            || !self.nodes[0usize].is_leaf()
            || self.nodes.len() > (u32::MAX / 2) as usize + 1
        {
            return Err(invalid("invalid constant node or graph size"));
        }
        let mut defined = vec![false; self.nodes.len()];
        defined[0] = true;
        let mut canonical = true;
        for (index, id) in self
            .inputs
            .iter()
            .copied()
            .chain(self.latchs.iter().map(|l| l.input))
            .enumerate()
        {
            if id >= self.nodes.len()
                || defined[usize::from(id)]
                || !self.nodes[usize::from(id)].is_leaf()
            {
                return Err(invalid("duplicate or invalid input/latch"));
            }
            defined[usize::from(id)] = true;
            canonical &= id == index + 1;
        }
        let valid_edge = |e: Lit| -> io::Result<()> {
            if e.is_none() || usize::from(e.var()) >= self.nodes.len() {
                Err(invalid("reference outside graph"))
            } else {
                Ok(())
            }
        };
        let mut next = self.inputs.len() + self.latchs.len() + 1;
        let mut topological = true;
        for (id, node) in self.nodes.iter().enumerate() {
            if node.is_and() {
                let (x, y) = node.fanin();
                valid_edge(x)?;
                valid_edge(y)?;
                topological &= usize::from(x.var()) < id && usize::from(y.var()) < id;
                canonical &= id == next;
                next += 1;
                defined[id] = true;
            }
        }
        if defined.contains(&false) {
            return Err(invalid("unregistered leaf or constant node"));
        }
        for l in &self.latchs {
            valid_edge(l.next)?;
            if l.init
                .is_some_and(|e| e.is_none() || !e.var().is_constant())
            {
                return Err(invalid("latch initialization must be constant or None"));
            }
        }
        for e in self
            .outputs
            .iter()
            .chain(&self.bads)
            .chain(&self.constraints)
            .chain(self.justice.iter().flatten())
            .chain(&self.fairness)
        {
            valid_edge(*e)?;
        }
        for id in self
            .inputs
            .iter()
            .copied()
            .chain(self.latchs.iter().map(|l| l.input))
        {
            if self
                .symbols
                .get(&id)
                .is_some_and(|s| s.contains(['\n', '\0']))
            {
                return Err(invalid("newline or NUL in symbol"));
            }
        }
        if !topological {
            self.gate_order()?;
        }
        Ok(canonical && topological)
    }

    /// Encode AIGER 1.9. Binary export renumbers noncanonical graphs without mutating `self`.
    pub fn write_aiger<W: Write>(&self, mut writer: W, ascii: bool) -> io::Result<()> {
        writer.write_all(&self.encode_aiger(ascii)?)
    }

    fn encode_aiger(&self, ascii: bool) -> io::Result<Vec<u8>> {
        let canonical = self.validate_aiger()?;
        if !ascii && !canonical {
            return self.reordered(&self.gate_order()?).encode_aiger(false);
        }
        let count = self.nodes.iter().filter(|n| n.is_and()).count();
        let mut out = Vec::with_capacity(count.saturating_mul(if ascii { 24 } else { 3 }));
        out.extend_from_slice(if ascii { b"aag " } else { b"aig " });
        let counts = [
            self.nodes.len() - 1,
            self.inputs.len(),
            self.latchs.len(),
            self.outputs.len(),
            count,
            self.bads.len(),
            self.constraints.len(),
            self.justice.len(),
            self.fairness.len(),
        ];
        let last = (5..9).rev().find(|&i| counts[i] != 0).unwrap_or(4);
        for (i, &n) in counts[..=last].iter().enumerate() {
            decimal(&mut out, n as u32);
            out.push(if i == last { b'\n' } else { b' ' });
        }
        if ascii {
            for &id in &self.inputs {
                number_line(&mut out, u32::from(id) * 2);
            }
        }
        for l in &self.latchs {
            if ascii {
                decimal(&mut out, u32::from(l.input) * 2);
                out.push(b' ');
            }
            decimal(&mut out, literal(l.next));
            let reset = l.init.map(literal).unwrap_or(u32::from(l.input) * 2);
            if reset != 0 {
                out.push(b' ');
                decimal(&mut out, reset);
            }
            out.push(b'\n');
        }
        for e in self
            .outputs
            .iter()
            .chain(&self.bads)
            .chain(&self.constraints)
        {
            number_line(&mut out, literal(*e));
        }
        for j in &self.justice {
            number_line(&mut out, j.len() as u32);
        }
        for e in self.justice.iter().flatten().chain(&self.fairness) {
            number_line(&mut out, literal(*e));
        }
        for (id, node) in self.nodes.iter().enumerate().filter(|(_, n)| n.is_and()) {
            let lhs = (id as u32) * 2;
            let x = literal(node.fanin1());
            let y = literal(node.fanin0());
            if ascii {
                decimal(&mut out, lhs);
                out.push(b' ');
                decimal(&mut out, x);
                out.push(b' ');
                number_line(&mut out, y);
            } else {
                let (hi, lo) = (x.max(y), x.min(y));
                delta(&mut out, lhs - hi);
                delta(&mut out, hi - lo);
            }
        }
        for (kind, ids) in [
            (b'i', self.inputs.clone()),
            (b'l', self.latchs.iter().map(|l| l.input).collect()),
        ] {
            for (index, id) in ids.into_iter().enumerate() {
                if let Some(name) = self.symbols.get(&id).filter(|s| !s.is_empty()) {
                    out.push(kind);
                    decimal(&mut out, index as u32);
                    out.push(b' ');
                    out.extend_from_slice(name.as_bytes());
                    out.push(b'\n');
                }
            }
        }
        Ok(out)
    }

    pub fn try_to_file<P: AsRef<Path>>(&self, path: P, ascii: bool) -> io::Result<()> {
        // Encode before creating/truncating the destination so invalid graphs leave it intact.
        fs::write(path, self.encode_aiger(ascii)?)
    }

    pub fn to_file<P: AsRef<Path>>(&self, path: P, ascii: bool) {
        self.try_to_file(&path, ascii)
            .unwrap_or_else(|e| panic!("write {}: {e}", path.as_ref().display()));
    }
}

fn literal(e: Lit) -> u32 {
    e.into()
}

fn decimal(out: &mut Vec<u8>, mut n: u32) {
    let mut buffer = [0u8; 10];
    let mut start = 10;
    loop {
        start -= 1;
        buffer[start] = b'0' + (n % 10) as u8;
        n /= 10;
        if n == 0 {
            break;
        }
    }
    out.extend_from_slice(&buffer[start..]);
}
fn number_line(out: &mut Vec<u8>, n: u32) {
    decimal(out, n);
    out.push(b'\n');
}
fn delta(out: &mut Vec<u8>, mut n: u32) {
    while n >= 128 {
        out.push((n as u8 & 127) | 128);
        n >>= 7;
    }
    out.push(n as u8);
}

impl fmt::Display for Aig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bytes = self.encode_aiger(true).map_err(|_| fmt::Error)?;
        f.write_str(std::str::from_utf8(&bytes).map_err(|_| fmt::Error)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXTENDED: &[u8] = b"aag 6 2 2 2 2 1 1 2 1\n2\n4\n6 10\n8 13 8\n10\n13\n11\n2\n2\n0\n4\n13\n6\n10 8 3\n12 10 4\ni0 first input\ni1 second\nl0 state\nl1 unknown\no0 ignored output name\nb0 bad\nc0 constraint\nj0 justice\nf0 fairness\nc\na comment\n";

    fn assert_graph_eq(a: &Aig, b: &Aig) {
        assert_eq!(a.inputs, b.inputs);
        assert_eq!(a.outputs, b.outputs);
        assert_eq!(a.bads, b.bads);
        assert_eq!(a.constraints, b.constraints);
        assert_eq!(a.justice, b.justice);
        assert_eq!(a.fairness, b.fairness);
        assert_eq!(a.symbols, b.symbols);
        assert_eq!(a.latchs.len(), b.latchs.len());
        for (x, y) in a.latchs.iter().zip(&b.latchs) {
            assert_eq!((x.input, x.next, x.init), (y.input, y.next, y.init));
        }
        assert_eq!(a.nodes.len(), b.nodes.len());
        for (x, y) in a.nodes.iter().zip(b.nodes.iter()) {
            assert_eq!((x.is_and(), x.is_leaf()), (y.is_and(), y.is_leaf()));
            if x.is_and() {
                let mut xs = [literal(x.fanin0()), literal(x.fanin1())];
                let mut ys = [literal(y.fanin0()), literal(y.fanin1())];
                xs.sort();
                ys.sort();
                assert_eq!(xs, ys);
            }
        }
    }

    #[test]
    fn extended_roundtrip() {
        let a = Aig::read_aiger(EXTENDED).unwrap();
        assert_eq!(a.latchs[0].init, Some(Lit::constant(false)));
        assert_eq!(a.latchs[1].init, None);
        assert_eq!(a.justice, vec![vec![edge(4), edge(13)], vec![]]);
        assert_eq!(a.symbols[&Var::new(1)], "first input");
        for ascii in [false, true] {
            let bytes = a.encode_aiger(ascii).unwrap();
            assert_graph_eq(&a, &Aig::read_aiger(&bytes).unwrap());
        }
        let mut a = a;
        a.latchs[0].init = Some(Lit::constant(true));
        assert_graph_eq(
            &a,
            &Aig::read_aiger(&a.encode_aiger(false).unwrap()).unwrap(),
        );
        assert!(a.to_string().starts_with("aag 6 2 2 2 2 1 1 2 1\n"));
    }

    #[test]
    fn sparse_forward_ascii_is_compacted_and_topological() {
        // A huge M with just three definitions must not allocate M node slots.
        let a = Aig::read_aiger(
            b"aag 1000000000 1 0 1 2\n2000000000\n4\n4 6 2000000000\n6 2000000000 1\ni0 input\n",
        )
        .unwrap();
        assert_eq!(a.nodes.len(), 4);
        assert_eq!(a.inputs, vec![1]);
        assert_eq!(a.outputs, vec![edge(6)]);
        assert_eq!(a.nodes[2usize].fanin(), (edge(1), edge(2)));
        assert_eq!(a.nodes[3usize].fanin(), (edge(2), edge(4)));
        assert_graph_eq(
            &a,
            &Aig::read_aiger(&a.encode_aiger(false).unwrap()).unwrap(),
        );
    }

    #[test]
    fn malformed_inputs_return_errors() {
        let cases: &[&[u8]] = &[
            b"",
            b"aig 0 0 0 0 0",
            b"aig 1 0 0 0 0\n",
            b"aag 0 0 0 0 0 0 0 0 0 0\n",
            b"aag 4294967296 0 0 0 0\n",
            b"aag 1 0 0 1 0\n2\n",
            b"aag 1 1 0 0 0\n3\n",
            b"aag 2 2 0 0 0\n2\n2\n",
            b"aag 1 0 1 0 0\n2 0 3\n",
            b"aag 1 0 0 0 1\n2 2 0\n",
            b"aag 2 0 0 0 2\n2 4 0\n4 2 0\n",
            b"aag 0 0 0 0 0\ni0 bad\n",
            b"aag 1 1 0 0 0\n2\ni0 x\ni0 y\n",
            b"aag 0 0 0 0 0\nc\nno newline",
            b"aig 1 0 0 0 1\n\x80",
            b"aig 1 0 0 0 1\n\x80\x80\x80\x80\x10\x00",
            b"aig 1 0 0 0 1\n\x00\x00",
            b"aig 1 0 0 0 1\n\x03\x00",
            b"aig 1 0 0 0 1\n\x02\x01",
            b"aig 0 0 0 0 0 0 0 1\n4294967295\n",
        ];
        for bytes in cases {
            assert!(Aig::read_aiger(bytes).is_err(), "accepted {bytes:?}");
        }
    }

    #[test]
    fn binary_delta_boundaries() {
        for n in [
            0,
            1,
            127,
            128,
            16383,
            16384,
            (1 << 21) - 1,
            1 << 21,
            (1 << 28) - 1,
            1 << 28,
            u32::MAX,
        ] {
            let mut bytes = Vec::new();
            delta(&mut bytes, n);
            let mut d = Decoder {
                bytes: &bytes,
                pos: 0,
                maxvar: 0,
            };
            assert_eq!(d.delta().unwrap(), n);
            assert_eq!(d.pos, bytes.len());
        }
    }

    #[test]
    fn invalid_graph_does_not_truncate_destination() {
        let path = std::env::temp_dir().join(format!("aiger-invalid-{}.aig", std::process::id()));
        fs::write(&path, b"keep existing contents").unwrap();
        let mut a = Aig::new();
        a.outputs.push(Var::new(123).lit());
        assert!(a.try_to_file(&path, false).is_err());
        assert_eq!(fs::read(&path).unwrap(), b"keep existing contents");
        fs::remove_file(path).unwrap();
        a.outputs.clear();
        let e = a.trivial_new_and_node(edge(0), edge(1));
        a.nodes[usize::from(e.var())].set_fanin0(e);
        assert!(a.encode_aiger(false).is_err());
        assert!(a.encode_aiger(true).is_err());
    }

    #[test]
    fn truncated_binary_body_is_rejected() {
        let mut a = Aig::new();
        let i = a.new_input().into();
        let mut e = i;
        for _ in 0..200 {
            e = a.trivial_new_and_node(e, !i);
        }
        a.outputs.push(e);
        let bytes = a.encode_aiger(false).unwrap();
        for end in 0..bytes.len() {
            assert!(Aig::read_aiger(&bytes[..end]).is_err(), "prefix {end}");
        }
    }

    #[test]
    fn writer_handles_interleaved_leaves_and_io_errors() {
        let mut a = Aig::new();
        let i = a.new_input().into();
        let x = a.trivial_new_and_node(i, !i);
        let j = a.new_input().into();
        let y = a.trivial_new_and_node(x, j);
        a.outputs.push(y);
        let b = Aig::read_aiger(&a.encode_aiger(false).unwrap()).unwrap();
        assert_eq!(b.inputs, vec![1, 2]);
        assert_eq!(b.nodes[3usize].fanin(), (edge(3), edge(2)));
        assert_eq!(b.outputs, vec![edge(8)]);
        struct Fail;
        impl Write for Fail {
            fn write(&mut self, _: &[u8]) -> io::Result<usize> {
                Err(io::Error::other("test failure"))
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }
        assert!(a.write_aiger(Fail, false).is_err());
        a.outputs.push(Var::new(999).lit());
        assert!(a.encode_aiger(false).is_err());
    }

    #[test]
    fn reserved_edges_are_rejected() {
        assert!(Aig::read_aiger(b"aag 2147483647 0 0 1 0\n4294967295\n").is_err());
        assert!(Aig::read_aiger(b"aag 2147483647 0 0 0 1\n2 4294967295 0\n").is_err());
        let mut a = Aig::new();
        a.outputs.push(Lit::NONE);
        assert!(a.encode_aiger(false).is_err());
        a.outputs.clear();
        a.new_latch(edge(0), Some(Lit::NONE));
        assert!(a.encode_aiger(false).is_err());
        a.latchs[0].init = None;
        a.nodes.push(AigNode {
            fanin0: edge(0),
            fanin1: Lit::NONE,
        });
        assert!(a.encode_aiger(false).is_err());
    }

    #[test]
    fn generated_graphs_roundtrip() {
        let mut graphs = vec![Aig::new(), Aig::read_aiger(EXTENDED).unwrap()];
        let mut rng = 42u64;
        for _ in 0..32 {
            let mut a = Aig::new();
            for n in 0..4 {
                let id = a.new_input();
                a.set_symbol(id, &format!("input {n}"));
            }
            for n in 0..3 {
                a.new_latch(edge(0), [Some(edge(0)), Some(edge(1)), None][n]);
            }
            for _ in 0..200 {
                rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1);
                let x = rng as usize % a.nodes.len();
                let y = (x + 1 + (rng >> 32) as usize % (a.nodes.len() - 1)) % a.nodes.len();
                let e = a.trivial_new_and_node(
                    Lit::new(Var::new(x), rng & 1 == 0),
                    Lit::new(Var::new(y), rng & 2 == 0),
                );
                a.outputs.push(e);
            }
            for (n, l) in a.latchs.iter_mut().enumerate() {
                l.next = a.outputs[n];
            }
            a.bads.push(!a.outputs[0]);
            a.constraints.push(edge(2));
            a.justice.push(vec![a.outputs[1], edge(1)]);
            a.justice.push(vec![]);
            a.fairness.push(a.outputs[2]);
            graphs.push(a);
        }
        for a in graphs {
            for ascii in [false, true] {
                let bytes = a.encode_aiger(ascii).unwrap();
                assert_graph_eq(&a, &Aig::read_aiger(&bytes).unwrap());
            }
        }
    }
}
