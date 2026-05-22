#!/usr/bin/env python3
import argparse
import json
import re
import subprocess
from pathlib import Path

from shadowlib import (
    build_btor,
    load_project_config,
    print_generated,
    print_link_notes,
    print_linked_bads,
    project_out_dir,
    require_file,
    run,
)

BTOR_NODE_RE = re.compile(r"^(\d+)\s+(\S+)(?:\s+(.*))?$")


def parse_btor(path: Path):
    nodes = {}
    symbols = {}
    node_symbols = {}
    sorts = {}
    max_id = 0
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith(";"):
            continue
        m = BTOR_NODE_RE.match(line)
        if not m:
            continue
        node_id = int(m.group(1))
        op = m.group(2)
        rest = m.group(3) or ""
        max_id = max(max_id, node_id)
        nodes[node_id] = (op, rest, raw)
        tokens = rest.split()
        if op == "sort":
            sorts[node_id] = rest
        elif op in ("input", "state") and len(tokens) >= 2:
            sym = tokens[1]
            if sym and not sym.startswith(";"):
                symbols[sym] = node_id
                node_symbols[node_id] = sym
        elif op not in ("sort", "init", "next", "bad", "constraint") and tokens:
            sym = None
            if ";" in tokens:
                semi = tokens.index(";")
                if semi > 0:
                    sym = tokens[semi - 1]
            if sym and not sym.startswith(";"):
                symbols[sym] = node_id
                node_symbols[node_id] = sym
    return nodes, symbols, node_symbols, sorts, max_id


def bitvec_width(sort_desc: str) -> int | None:
    m = re.fullmatch(r"bitvec\s+(\d+)", sort_desc)
    return int(m.group(1)) if m else None


def rewrite_signed_ref(tok: str, repl: dict[str, int]) -> str:
    neg = tok.startswith("-")
    key = tok[1:] if neg else tok
    if key in repl:
        val = repl[key]
        return f"-{val}" if neg else str(val)
    return tok


def link_btor(
    core: Path, monitor: Path, link_map_path: Path, linked: Path
) -> list[str]:
    core_nodes, core_syms, _, core_sorts, core_max = parse_btor(core)
    mon_nodes, _, mon_node_syms, mon_sorts, _ = parse_btor(monitor)
    link_map = json.loads(link_map_path.read_text())["ports"]
    core_sort_by_desc = {desc: node_id for node_id, desc in core_sorts.items()}

    repl = {}
    append = []
    added_sorts = {}
    link_notes = []
    next_id = core_max

    def alloc(op: str, rest: str) -> int:
        nonlocal next_id
        next_id += 1
        append.append(f"{next_id} {op} {rest}")
        return next_id

    def get_sort(desc: str) -> int:
        if desc in core_sort_by_desc:
            return core_sort_by_desc[desc]
        if desc in added_sorts:
            return added_sorts[desc]
        sid = alloc("sort", desc)
        added_sorts[desc] = sid
        return sid

    def build_memory_concat(
        prefix: str, sort_desc: str, indices: list[int]
    ) -> tuple[int, int, int] | None:
        target_width = bitvec_width(sort_desc)
        elems = []
        for idx in indices:
            sym = f"{prefix}[{idx}]"
            if sym not in core_syms:
                return None
            elems.append(core_syms[sym])
        if not elems or target_width is None:
            return None

        first_op, first_rest, _ = core_nodes[elems[0]]
        if first_op not in ("state", "input"):
            return None
        first_sort = int(first_rest.split()[0])
        elem_width = bitvec_width(core_sorts[first_sort])
        if elem_width is None or elem_width * len(elems) != target_width:
            return None

        cur = elems[0]
        cur_width = elem_width
        for elem in elems[1:]:
            cur_width += elem_width
            sort_id = get_sort(f"bitvec {cur_width}")
            cur = alloc("concat", f"{sort_id} {cur} {elem}")
        return cur, len(elems), elem_width

    def replacement_for_symbol(
        sym: str, sort_desc: str | None = None
    ) -> tuple[int, str] | None:
        entry = link_map.get(sym)
        if entry is None and sym in core_syms:
            entry = {"path": sym, "memory": False, "indices": []}
        if entry is None:
            return None

        target = entry["path"]
        if target in core_syms:
            return (
                core_syms[target],
                f"{sym} -> {target} (core node {core_syms[target]})",
            )
        if entry.get("memory") and sort_desc is not None:
            aggregate = build_memory_concat(target, sort_desc, entry["indices"])
            if aggregate:
                aggregate_node, depth, elem_width = aggregate
                return (
                    aggregate_node,
                    f"{sym} -> concat core {target}[{entry['indices'][0]}:{entry['indices'][-1]}] "
                    f"({depth} x {elem_width}-bit)",
                )
        return None

    for node_id in sorted(mon_nodes):
        op, rest, _ = mon_nodes[node_id]
        if op == "sort":
            repl[str(node_id)] = get_sort(rest)
            continue
        sym = mon_node_syms.get(node_id)
        if sym:
            sort_desc = None
            toks = rest.split()
            if toks:
                sort_tok = rewrite_signed_ref(toks[0], repl)
                if sort_tok.lstrip("-").isdigit():
                    sort_id = abs(int(sort_tok))
                    sort_desc = mon_sorts.get(sort_id) or core_sorts.get(sort_id)
            replacement = replacement_for_symbol(sym, sort_desc)
            if replacement:
                repl[str(node_id)], note = replacement
                link_notes.append(note)
                continue
        if op == "input":
            toks = rest.split()
            sym = toks[1] if len(toks) >= 2 else ""
            entry = link_map.get(sym, {"path": sym, "memory": False, "indices": []})
            target = entry["path"]
            if entry.get("memory") and len(toks) >= 2:
                aggregate = build_memory_concat(
                    target, mon_sorts[int(toks[0])], entry["indices"]
                )
                if aggregate:
                    aggregate_node, depth, elem_width = aggregate
                    repl[str(node_id)] = aggregate_node
                    link_notes.append(
                        f"{sym} -> concat core {target}[{entry['indices'][0]}:{entry['indices'][-1]}] "
                        f"({depth} x {elem_width}-bit)"
                    )
                else:
                    toks[0] = rewrite_signed_ref(toks[0], repl)
                    repl[str(node_id)] = alloc("input", " ".join(toks))
                    link_notes.append(
                        f"{sym} -> fresh monitor input (missing core memory {target})"
                    )
            elif sym in core_syms:
                repl[str(node_id)] = core_syms[sym]
                link_notes.append(f"{sym} -> {sym} (core node {core_syms[sym]})")
            else:
                toks[0] = rewrite_signed_ref(toks[0], repl)
                repl[str(node_id)] = alloc("input", " ".join(toks))
                link_notes.append(f"{sym} -> fresh monitor input")
            continue
        if op == "output":
            continue
        if op == "bad":
            toks = rest.split()
            toks[0] = rewrite_signed_ref(toks[0], repl)
            alloc("bad", " ".join(toks))
            continue

        toks = rest.split()
        rewritten = [rewrite_signed_ref(t, repl) for t in toks]
        repl[str(node_id)] = alloc(op, " ".join(rewritten))

    core_lines = [
        line
        for line in core.read_text().splitlines()
        if not line.strip().startswith("; end of yosys output")
    ]
    linked.write_text(
        "\n".join(core_lines + append + ["; end of shadow link output"]) + "\n"
    )
    return link_notes


def link_invariants(
    project,
    out_dir: Path,
    check: bool = False,
) -> tuple[Path, Path, list[str]]:
    if project.invariants is None:
        raise RuntimeError("cannot detect invariants file; pass --invariants")

    shadow = out_dir / "shadow.sv"
    link_map_path = out_dir / "link_map.json"
    core = out_dir / "core.btor"
    require_file(shadow, "missing prepared shadow; run shadow_prepare.py first")
    require_file(link_map_path, "missing link map; run shadow_prepare.py first")
    require_file(core, "missing core BTOR; run shadow_prepare.py first")

    monitor = out_dir / "monitor.btor"
    linked = out_dir / "linked.btor"
    build_btor(
        project.project_dir,
        project.top,
        [shadow, project.invariants],
        project.defines,
        project.reset,
        out_dir / "monitor.info",
        monitor,
    )
    notes = link_btor(core, monitor, link_map_path, linked)
    if check:
        run(["ric3", "check", str(linked), "ic3"], project.project_dir)
    return monitor, linked, notes


def parse_args(argv=None):
    parser = argparse.ArgumentParser(
        description="Compile invariants against a prepared shadow DUT and link with core BTOR."
    )
    parser.add_argument("--config", type=Path, default=Path("ric3.toml"))
    parser.add_argument("--invariants", type=Path, default=None)
    parser.add_argument("--out", type=Path, default=Path("shadow_link"))
    parser.add_argument(
        "--check",
        action="store_true",
        help="run `ric3 check linked.btor ic3` after linking",
    )
    return parser.parse_args(argv)


def main(argv=None) -> int:
    args = parse_args(argv)
    project = load_project_config(
        args.config, invariants_arg=args.invariants, require_invariants=True
    )
    out_dir = project_out_dir(project, args.out)
    monitor, linked, notes = link_invariants(project, out_dir, check=args.check)
    print_generated(
        project.project_dir,
        "Generated invariant artifacts",
        [out_dir / "monitor.info", monitor, linked],
    )
    print_link_notes(notes)
    print_linked_bads(project.project_dir, linked)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except subprocess.CalledProcessError as exc:
        raise SystemExit(exc.returncode)
