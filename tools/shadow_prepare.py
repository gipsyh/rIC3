#!/usr/bin/env python3
import argparse
import json
import re
import shlex
import shutil
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

from shadowlib import (
    ProjectConfig,
    build_btor,
    load_project_config,
    print_generated,
    project_out_dir,
)

SIMPLE_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_$]*$")


@dataclass
class Signal:
    name: str
    sv_type: str
    is_memory: bool = False
    unpacked: str | None = None
    indices: list[int] = field(default_factory=list)


@dataclass
class DeclaredSignal:
    signal: Signal
    rel_path: tuple[str, ...]
    concrete_signal: Signal


@dataclass
class InstanceInfo:
    name: str
    scope: "Scope"
    param_connections: list[tuple[str, str]] = field(default_factory=list)


@dataclass
class Scope:
    module_name: str
    body_name: str
    path: tuple[str, ...]
    params: list[str]
    declared_signals: list[DeclaredSignal]
    instances: list[InstanceInfo]
    shared: bool = False


@dataclass
class ScopeBuild:
    scope: Scope
    link_signals: list[DeclaredSignal]


def sv_ident(name: str) -> str:
    if SIMPLE_IDENT_RE.fullmatch(name):
        return name
    return "\\" + name + " "


def sanitize(name: str) -> str:
    text = re.sub(r"[^A-Za-z0-9_$]+", "_", name)
    text = re.sub(r"_+", "_", text).strip("_")
    if not text or text[0].isdigit():
        text = "_" + text
    return text


def parse_sv_range(text: str) -> tuple[int, int]:
    m = re.fullmatch(r"\[\s*(-?\d+)\s*:\s*(-?\d+)\s*\]", text)
    if not m:
        raise ValueError(f"unsupported unpacked range {text!r}")
    return int(m.group(1)), int(m.group(2))


def range_indices(text: str) -> list[int]:
    left, right = parse_sv_range(text)
    step = 1 if right >= left else -1
    return list(range(left, right + step, step))


def pyslang_integral_type_to_sv(ty) -> str:
    width = int(getattr(ty, "bitWidth", 0))
    if width <= 1:
        return "logic"
    signed = " signed" if getattr(ty, "isSigned", False) else ""
    try:
        rng = str(ty.fixedRange)
    except Exception:
        rng = f"[{width - 1}:0]"
    return f"logic{signed} {rng}"


def normalize_sv_type(sv_type: str) -> str:
    sv_type = sv_type.strip()
    sv_type = re.sub(r"\breg\b", "logic", sv_type)
    sv_type = re.sub(r"\bwire\b", "logic", sv_type)
    sv_type = re.sub(r"\bbit\b", "logic", sv_type)
    sv_type = re.sub(r"\s+", " ", sv_type).strip()
    if sv_type.startswith("["):
        sv_type = f"logic {sv_type}"
    return sv_type or "logic"


def cleanup_syntax_text(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def syntax_json_text(obj) -> str:
    if isinstance(obj, dict):
        if "text" in obj:
            return str(obj["text"])
        parts = []
        for key, value in obj.items():
            if key in ("kind", "trivia"):
                continue
            parts.append(syntax_json_text(value))
        return "".join(parts)
    if isinstance(obj, list):
        return "".join(syntax_json_text(item) for item in obj)
    return ""


def syntax_to_json(node) -> dict:
    data = node.to_json()
    if isinstance(data, str):
        return json.loads(data)
    return data


def declared_type_syntax(member) -> str | None:
    declared = getattr(member, "declaredType", None)
    if not declared:
        return None
    syntax = getattr(declared, "typeSyntax", None)
    if not syntax:
        return None
    text = cleanup_syntax_text(str(syntax))
    return text or None


def unpacked_syntax(member) -> str | None:
    syntax = getattr(member, "syntax", None)
    if not syntax:
        return None
    dims = getattr(syntax, "dimensions", None)
    if dims:
        text = cleanup_syntax_text(str(dims))
        return text or None

    text = cleanup_syntax_text(str(syntax))
    name = getattr(member, "name", "")
    if name and text.startswith(name):
        suffix = text[len(name) :].strip()
        return suffix or None
    return None


def pyslang_type_to_template_signal(name: str, member, concrete: Signal) -> Signal:
    sv_type = declared_type_syntax(member)
    if not sv_type:
        sv_type = concrete.sv_type
    signal = Signal(
        name=name,
        sv_type=normalize_sv_type(sv_type),
        is_memory=concrete.is_memory,
        unpacked=concrete.unpacked,
        indices=concrete.indices,
    )
    if signal.is_memory:
        signal.unpacked = unpacked_syntax(member) or signal.unpacked
    return signal


def pyslang_type_to_signal(name: str, ty) -> Signal:
    unpacked_ranges = []
    cur = ty
    while getattr(cur, "isUnpackedArray", False):
        unpacked_ranges.append(str(cur.range))
        cur = cur.elementType

    if unpacked_ranges:
        return Signal(
            name=name,
            sv_type=pyslang_integral_type_to_sv(cur),
            is_memory=True,
            unpacked=" ".join(unpacked_ranges),
            indices=range_indices(unpacked_ranges[0]),
        )

    if getattr(cur, "isIntegral", False):
        return Signal(name=name, sv_type=pyslang_integral_type_to_sv(cur))

    sv_type = str(cur)
    sv_type = sv_type.replace("reg", "logic").replace("bit", "logic")
    return Signal(name=name, sv_type=sv_type)


def internal_signal_decl(signal: Signal) -> str:
    name = sv_ident(signal.name)
    if signal.is_memory:
        return f"    {signal.sv_type} {name} {signal.unpacked};"
    return f"    {signal.sv_type} {name};"


def param_decl_pyslang(member) -> str:
    kw = "localparam" if member.isLocalParam else "parameter"
    name = sv_ident(member.name)
    declared_type = declared_type_syntax(member)
    if declared_type:
        sv_type = normalize_sv_type(declared_type)
    elif member.isLocalParam:
        try:
            sv_type = pyslang_integral_type_to_sv(member.type)
        except Exception:
            sv_type = "int"
    else:
        sv_type = ""

    syntax = getattr(member, "syntax", None)
    init = None
    if syntax is not None:
        parts = str(syntax).split("=", 1)
        if len(parts) == 2:
            init = cleanup_syntax_text(parts[1])
    if init is None:
        init = str(member.value)

    type_part = f" {sv_type}" if sv_type else ""
    return f"    {kw}{type_part} {name} = {init}"


def module_name(top: str, path: tuple[str, ...], body_name: str) -> str:
    if not path:
        return top
    parts = [top, *path, body_name]
    return "__shadow_" + "_".join(sanitize(part) for part in parts)


def scope_key(instance, top: str, path: tuple[str, ...]) -> tuple[str, str]:
    if not path:
        return ("instance", top)
    return ("definition", instance.body.definition.hierarchicalPath)


def param_overrides(instance) -> list[tuple[str, str]]:
    syntax = getattr(instance, "syntax", None)
    parent = getattr(syntax, "parent", None)
    params = getattr(parent, "parameters", None)
    if not params:
        return []

    result = []
    for item in syntax_to_json(params).get("parameters", []):
        if item.get("kind") != "NamedParamAssignment":
            continue
        name = item["name"]["text"]
        expr = cleanup_syntax_text(syntax_json_text(item.get("expr", {})))
        result.append((name, expr))
    return result


def build_scope_pyslang(
    instance,
    top: str,
    path: tuple[str, ...],
    modules: list[Scope],
    scope_cache: dict[tuple[str, str], Scope],
) -> ScopeBuild:
    from pyslang.ast import SymbolKind

    key = scope_key(instance, top, path)

    body = instance.body
    shared = bool(path)
    params = []
    declared_signals = []
    link_signals = []
    instances = []
    port_names = set()
    seen_signals = set()
    decl_members = {}

    cached_scope = scope_cache.get(key)

    for member in body:
        kind = member.kind
        name = getattr(member, "name", "")
        if name and kind in (SymbolKind.Net, SymbolKind.Variable):
            decl_members.setdefault(name, member)

    def add_signal(name: str, concrete_member, template_member) -> None:
        concrete = pyslang_type_to_signal(name, concrete_member.type)
        sig = (
            pyslang_type_to_template_signal(name, template_member, concrete)
            if shared
            else concrete
        )
        declared = DeclaredSignal(sig, (name,), concrete)
        if cached_scope is None:
            declared_signals.append(declared)
        link_signals.append(declared)

    for member in body:
        kind = member.kind
        name = getattr(member, "name", "")
        if not name:
            continue
        if kind == SymbolKind.Parameter:
            params.append(param_decl_pyslang(member))
        elif kind == SymbolKind.Port:
            template_member = decl_members.get(name, member)
            add_signal(name, member, template_member)
            port_names.add(name)
            seen_signals.add(name)
        elif kind in (SymbolKind.Net, SymbolKind.Variable):
            if name in port_names or name in seen_signals:
                continue
            if name.startswith("$"):
                continue
            add_signal(name, member, member)
            seen_signals.add(name)

    for member in body:
        if member.kind != SymbolKind.Instance:
            continue
        child_name = member.name
        child_build = build_scope_pyslang(
            member, top, (*path, child_name), modules, scope_cache
        )
        for declared in child_build.link_signals:
            rel_path = (child_name, *declared.rel_path)
            link_signals.append(
                DeclaredSignal(
                    declared.concrete_signal, rel_path, declared.concrete_signal
                )
            )
        if cached_scope is None:
            instances.append(
                InstanceInfo(child_name, child_build.scope, param_overrides(member))
            )

    if cached_scope is not None:
        return ScopeBuild(cached_scope, link_signals)

    scope = Scope(
        module_name=module_name(top, path, body.name) if not shared else body.name,
        body_name=body.name,
        path=path,
        params=params,
        declared_signals=declared_signals,
        instances=instances,
        shared=shared,
    )
    scope_cache[key] = scope
    modules.append(scope)
    return ScopeBuild(scope, link_signals)


def emit_scope(scope: Scope) -> str:
    lines = []
    lines.append(f"module {sv_ident(scope.module_name)}")
    if scope.params:
        lines.append("#(")
        lines.append(",\n".join(scope.params))
        lines.append(")")
    lines.append(";")
    for declared in scope.declared_signals:
        lines.append(internal_signal_decl(declared.signal))
    for inst in scope.instances:
        lines.append("")
        if inst.param_connections:
            lines.append(f"    {sv_ident(inst.scope.module_name)} #(")
            params = [
                f"        .{sv_ident(name)}({expr})"
                for name, expr in inst.param_connections
            ]
            lines.append(",\n".join(params))
            lines.append(f"    ) {sv_ident(inst.name)} ();")
        else:
            lines.append(
                f"    {sv_ident(inst.scope.module_name)} {sv_ident(inst.name)} ();"
            )
    lines.append("endmodule")
    return "\n".join(lines)


def write_shadow_outputs(
    top: str, link_signals: list[DeclaredSignal], modules: list[Scope], out_dir: Path
) -> tuple[Path, Path]:
    shadow = out_dir / "shadow.sv"
    text = [
        "// Auto-generated by tools/shadow_prepare.py.",
        "// The modules below preserve elaborated hierarchy and names for bind invariants.",
        "",
    ]
    for scope in reversed(modules):
        text.append(emit_scope(scope))
        text.append("")
    shadow.write_text("\n".join(text))

    link_map = {}
    for declared in link_signals:
        full_path = ".".join(declared.rel_path)
        link_map[full_path] = {
            "path": full_path,
            "memory": declared.concrete_signal.is_memory,
            "indices": declared.concrete_signal.indices,
        }
    link_map_path = out_dir / "link_map.json"
    link_map_path.write_text(
        json.dumps({"top": top, "ports": link_map}, indent=2) + "\n"
    )
    return shadow, link_map_path


def generate_shadow(
    top: str, files: list[Path], defines: dict[str, str], out_dir: Path
) -> tuple[Path, Path]:
    from pyslang import DiagnosticEngine
    from pyslang.driver import CommandLineOptions, Driver

    print("+ pyslang shadow elaboration", flush=True)
    driver = Driver()
    driver.addStandardArgs()
    args = ["slang", "--top", top, "-D", "FORMAL", "-D", "YOSYS_SLANG"]
    for name, value in sorted(defines.items()):
        args += ["-D", name if value == "" else f"{name}={value}"]
    args += [str(path) for path in files]

    if not driver.parseCommandLine(shlex.join(args), CommandLineOptions()):
        raise RuntimeError("pyslang failed to parse command line")
    if not driver.processOptions() or not driver.parseAllSources():
        raise RuntimeError("pyslang failed to parse sources")

    comp = driver.createCompilation()
    diags = comp.getAllDiagnostics()
    if any(diags[i].isError() for i in range(len(diags))):
        raise RuntimeError(DiagnosticEngine.reportAll(comp.sourceManager, diags))

    matches = [inst for inst in comp.getRoot().topInstances if inst.name == top]
    if len(matches) != 1:
        raise RuntimeError(
            f"expected one top instance named {top!r}, got {len(matches)}"
        )

    modules = []
    top_build = build_scope_pyslang(matches[0], top, (), modules, {})
    return write_shadow_outputs(top, top_build.link_signals, modules, out_dir)


def prepare_dut(project: ProjectConfig, out_dir: Path) -> tuple[Path, Path, Path]:
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True)

    shadow, link_map_path = generate_shadow(
        project.top, project.dut_files, project.defines, out_dir
    )
    core = out_dir / "core.btor"
    build_btor(
        project.project_dir,
        project.top,
        project.dut_files,
        project.defines,
        project.reset,
        out_dir / "core.info",
        core,
    )
    return shadow, link_map_path, core


def parse_args(argv=None):
    parser = argparse.ArgumentParser(
        description="Prepare stable DUT artifacts for shadow invariant linking."
    )
    parser.add_argument("--config", type=Path, default=Path("ric3.toml"))
    parser.add_argument(
        "--invariants",
        type=Path,
        default=None,
        help="invariants file to exclude from DUT files; auto-detected when named invariants.sv",
    )
    parser.add_argument("--out", type=Path, default=Path("shadow_link"))
    return parser.parse_args(argv)


def main(argv=None) -> int:
    args = parse_args(argv)
    project = load_project_config(
        args.config, invariants_arg=args.invariants, require_invariants=False
    )
    out_dir = project_out_dir(project, args.out)
    shadow, link_map_path, core = prepare_dut(project, out_dir)
    print_generated(
        project.project_dir,
        "Prepared DUT artifacts",
        [shadow, link_map_path, out_dir / "core.info", core],
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except subprocess.CalledProcessError as exc:
        raise SystemExit(exc.returncode)
