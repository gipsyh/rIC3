use giputils::hash::GHashMap;
use logicrs::fol::Sort;
use std::fmt::{self, Display};

fn simple_sv_ident(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$')
}

fn sv_ident(name: &str) -> String {
    if simple_sv_ident(name) {
        name.to_string()
    } else {
        format!("\\{name} ")
    }
}

fn sv_type(sort: Sort, name: &str) -> String {
    match sort {
        Sort::Bv(1) => format!("logic {name}"),
        Sort::Bv(width) => format!("logic [{}:0] {name}", width - 1),
        Sort::Array(index, width) => format!(
            "logic [{}:0] {} [{}:0]",
            width - 1,
            name,
            1usize.checked_shl(index as u32).unwrap() - 1
        ),
    }
}

pub struct SvModule {
    name: String,
    input: GHashMap<String, Sort>,
    pub ext_body: Vec<String>,
    children: GHashMap<String, SvModule>,
    pub outside: Vec<String>,
}

impl SvModule {
    pub fn new(name: impl AsRef<str>) -> Self {
        Self {
            name: name.as_ref().to_string(),
            input: GHashMap::new(),
            ext_body: Vec::new(),
            children: GHashMap::new(),
            outside: Vec::new(),
        }
    }

    pub fn add_input(&mut self, name: impl AsRef<str>, sort: Sort) {
        assert!(self.input.insert(name.as_ref().to_string(), sort).is_none());
    }

    pub fn add_ext_body(&mut self, body: String) {
        self.ext_body.push(body);
    }

    #[allow(unused)]
    pub fn get_children_mut(&mut self, path: &str) -> Option<&mut SvModule> {
        let mut module = self;
        for name in path.split('.').filter(|name| !name.is_empty()) {
            module = module.children.get_mut(name)?;
        }
        Some(module)
    }

    pub fn children_entry(
        &mut self,
        path: impl IntoIterator<Item = impl AsRef<str>>,
    ) -> &mut SvModule {
        let mut module = self;
        let path: Vec<_> = path.into_iter().map(|s| s.as_ref().to_string()).collect();
        let full_name = path.join("_");
        for name in path.iter() {
            module = module
                .children
                .entry(name.clone())
                .or_insert_with(|| SvModule::new(&full_name));
        }
        module
    }
}

impl Display for SvModule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "module {}", sv_ident(&self.name))?;

        if self.input.is_empty() {
            writeln!(f, ";")?;
        } else {
            writeln!(f, " (")?;
            let input = self
                .input
                .iter()
                .map(|(name, sort)| {
                    let name = sv_ident(name);
                    format!("    input {}", sv_type(*sort, &name))
                })
                .collect::<Vec<_>>();
            write!(f, "{}", input.join(",\n"))?;
            writeln!(f, "\n);")?;
        }

        for body in &self.ext_body {
            writeln!(f, "    {body}")?;
        }

        for (inst, child) in self.children.iter() {
            writeln!(f, "    {} {}();", sv_ident(&child.name), sv_ident(inst))?;
        }

        writeln!(f, "endmodule\n")?;

        for child in self.children.values() {
            writeln!(f, "{child}")?;
        }

        Ok(())
    }
}
