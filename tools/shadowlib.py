#!/usr/bin/env python3
import subprocess
import tomllib
from dataclasses import dataclass
from pathlib import Path


@dataclass
class ProjectConfig:
    config_path: Path
    project_dir: Path
    top: str
    reset: str | None
    defines: dict[str, str]
    all_files: list[Path]
    invariants: Path | None
    dut_files: list[Path]


def run(cmd: list[str], cwd: Path) -> None:
    print("+", " ".join(str(c) for c in cmd), flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def define_args(defines: dict[str, str]) -> list[str]:
    args = []
    for name, value in sorted(defines.items()):
        if value == "":
            args.append(f"-D {name}")
        else:
            args.append(f"-D {name}={value}")
    return args


def yosys_flow(
    top: str,
    files: list[Path],
    defines: dict[str, str],
    reset: str | None,
    info: Path,
    btor: Path,
) -> str:
    read = "read_slang -Wnone -D FORMAL -D YOSYS_SLANG"
    for define in define_args(defines):
        read += f" {define}"
    for file in files:
        read += f" {file}"
    cmds = [
        read,
        f"prep -flatten -top {top}",
        "hierarchy -smtcheck -nokeep_prints",
        "scc -select; simplemap; select -clear",
        "memory_nordff",
    ]
    if reset:
        if reset.startswith("!"):
            cmds.append(f"fminit -seq {reset[1:]} 0,1")
        else:
            cmds.append(f"fminit -seq {reset} 1,0")
    cmds += [
        "chformal -cover -remove",
        "chformal -early",
        "async2sync",
        "formalff -clk2ff -ff2anyinit -hierarchy -assume",
        "memory_map -formal",
        "dffunmap",
        "setundef -undriven -anyseq",
        "opt -fast",
        "opt_clean",
        "delete -output",
        "rename -witness",
        "check",
        f"write_btor -i {info} {btor}",
    ]
    return "; ".join(cmds)


def build_btor(
    project_dir: Path,
    top: str,
    files: list[Path],
    defines: dict[str, str],
    reset: str | None,
    info: Path,
    btor: Path,
) -> None:
    script = yosys_flow(top, files, defines, reset, info, btor)
    run(["yosys", "-m", "slang", "-p", script], project_dir)


def load_config(path: Path) -> dict:
    with path.open("rb") as f:
        return tomllib.load(f)


def detect_invariants(files: list[Path]) -> Path | None:
    matches = [path for path in files if path.name == "invariants.sv"]
    return matches[0] if len(matches) == 1 else None


def resolve_project_path(project_dir: Path, path: Path) -> Path:
    return path.resolve() if path.is_absolute() else (project_dir / path).resolve()


def relative_to_project(path: Path, project_dir: Path) -> str:
    try:
        return str(path.relative_to(project_dir))
    except ValueError:
        return str(path)


def load_project_config(
    config: Path,
    invariants_arg: Path | None = None,
    require_invariants: bool = True,
) -> ProjectConfig:
    config_path = config.resolve()
    project_dir = config_path.parent
    cfg = load_config(config_path)
    dut = cfg["dut"]
    top = dut["top"]
    reset = dut.get("reset")
    defines = dut.get("defines", {})
    all_files = [resolve_project_path(project_dir, Path(path)) for path in dut["files"]]
    invariants = (
        resolve_project_path(project_dir, invariants_arg)
        if invariants_arg is not None
        else detect_invariants(all_files)
    )
    if require_invariants and invariants is None:
        raise RuntimeError("cannot detect invariants file; pass --invariants")
    dut_files = [path for path in all_files if invariants is None or path != invariants]
    if not dut_files:
        raise RuntimeError("no stable DUT files left after removing invariants")
    return ProjectConfig(
        config_path=config_path,
        project_dir=project_dir,
        top=top,
        reset=reset,
        defines=defines,
        all_files=all_files,
        invariants=invariants,
        dut_files=dut_files,
    )


def project_out_dir(project: ProjectConfig, out: Path) -> Path:
    return resolve_project_path(project.project_dir, out)


def require_file(path: Path, message: str) -> None:
    if not path.exists():
        raise RuntimeError(f"{message}: {path}")


def print_generated(project_dir: Path, title: str, paths: list[Path]) -> None:
    print(f"\n{title}:", flush=True)
    for path in paths:
        print(" ", relative_to_project(path, project_dir), flush=True)


def print_link_notes(notes: list[str]) -> None:
    print("\nLinked monitor signals:", flush=True)
    for note in notes:
        print(" ", note, flush=True)


def print_linked_bads(project_dir: Path, linked: Path) -> None:
    print("\nLinked bads:", flush=True)
    subprocess.run(["rg", "-n", "bad", str(linked)], cwd=project_dir, check=False)
