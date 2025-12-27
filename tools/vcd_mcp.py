from __future__ import annotations

import os
from bisect import bisect_right
from typing import Dict, List, Sequence, Tuple
from mcp.server.fastmcp import FastMCP
from vcdvcd import VCDVCD


def _require_file(path: str) -> None:
    if not path:
        raise ValueError("vcd_path is required")
    if not os.path.exists(path):
        raise FileNotFoundError(f"VCD not found: {path}")
    if not os.path.isfile(path):
        raise ValueError(f"Not a file: {path}")


def _load_vcd_signals(vcd_path: str) -> List[str]:
    _require_file(vcd_path)
    vcd = VCDVCD(vcd_path, only_sigs=True)
    return sorted(getattr(vcd, "signals", []))


def _resolve_signal_name(available: Sequence[str], name: str) -> str:
    if name in available:
        return name
    if name.startswith("/") and name[1:] in available:
        return name[1:]
    if not name.startswith("/") and ("/" + name) in available:
        return "/" + name

    lower_map = {sig.lower(): sig for sig in available}
    if name.lower() in lower_map:
        return lower_map[name.lower()]

    raise ValueError(f"Signal not found: {name}")


def _expand_signal_names(
    available: Sequence[str], requested: Sequence[str]
) -> List[str]:
    resolved: List[str] = []
    for name in requested:
        try:
            resolved.append(_resolve_signal_name(available, name))
            continue
        except ValueError:
            pass

        # Suffix match, like the reference script (e.g. "clock" matches "uut.clock")
        # Prefer '.' hierarchy but also accept '/' separators.
        suffix_matches = [
            sig
            for sig in available
            if sig.endswith("." + name) or sig.endswith("/" + name)
        ]
        if not suffix_matches:
            raise ValueError(f"Signal not found: {name}")

        # Deterministic order, while still respecting the user's requested ordering.
        resolved.extend(sorted(suffix_matches))

    # De-duplicate while preserving order.
    seen: set[str] = set()
    out: List[str] = []
    for s in resolved:
        if s in seen:
            continue
        seen.add(s)
        out.append(s)
    return out


def _extract_time_markers(vcd_path: str) -> List[int]:
    """Return all VCD time markers (#<time>) in file order, after $enddefinitions."""
    _require_file(vcd_path)
    times: List[int] = []
    start_parsing = False
    with open(vcd_path, "r", encoding="utf-8", errors="replace") as f:
        for raw in f:
            line = raw.strip()
            if not start_parsing:
                if line.startswith("$enddefinitions"):
                    start_parsing = True
                continue

            if line.startswith("#"):
                try:
                    times.append(int(line[1:]))
                except ValueError:
                    # Ignore malformed time markers.
                    continue
    return times


def _sample_times(vcd_path: str) -> List[int]:
    times = _extract_time_markers(vcd_path)
    if not times:
        raise ValueError("No timepoints found in VCD")
    return times


def _build_tv_index(tv: Sequence[Tuple[int, str]]) -> Tuple[List[int], List[str]]:
    times: List[int] = []
    values: List[str] = []
    for t, v in tv:
        times.append(int(t))
        values.append(v)
    return times, values


def _value_at(times: Sequence[int], values: Sequence[str], t: int) -> str:
    # Rightmost index where times[idx] <= t
    idx = bisect_right(times, t) - 1
    if idx < 0:
        return "x"
    return values[idx]


def _format_hex(val: str) -> str:
    if val is None or val == "x":
        return "X"

    s = str(val).strip()
    if not s:
        return s

    # vcdvcd may return vectors as "0101" or "b0101"; normalize.
    if (s.startswith("b") or s.startswith("B")) and len(s) > 1:
        s_bits = s[1:]
    elif s.startswith("0b") or s.startswith("0B"):
        s_bits = s[2:]
    else:
        s_bits = s

    # If there are any unknown/high-impedance bits, keep it as a binary bitstring.
    # (Do not attempt hex conversion, since hex would be ambiguous.)
    lowered = s_bits.lower()
    if any(c in lowered for c in ("x", "z")):
        return "0b_" + s_bits

    if s_bits and all(c in "01" for c in s_bits):
        h = hex(int(s_bits, 2))
        if h.startswith("0x"):
            return "0x_" + h[2:]
        return h

    return s


def _steps_markdown_table(
    vcd_path: str,
    signals: Sequence[str],
) -> str:
    _require_file(vcd_path)
    if not signals:
        raise ValueError("signals must be a non-empty list")

    vcd = VCDVCD(vcd_path, only_sigs=False)
    available = sorted(getattr(vcd, "signals", []))
    signal_names = _expand_signal_names(available, signals)
    step_times = _sample_times(vcd_path)

    if not step_times:
        raise ValueError("No steps found (no sampled timepoints)")

    sig_indexes: Dict[str, Tuple[List[int], List[str]]] = {}
    for s in signal_names:
        tv = getattr(vcd[s], "tv", None)
        if tv is None:
            raise ValueError(f"No data for signal: {s}")
        sig_indexes[s] = _build_tv_index(tv)

    step_headers = [str(i) for i in range(len(step_times))]
    header = "| signal | " + " | ".join(step_headers) + " |"
    sep = "| --- | " + " | ".join(["---"] * len(step_times)) + " |"

    lines: List[str] = [header, sep]
    for s in signal_names:
        times, values = sig_indexes[s]
        row_vals = [_format_hex(_value_at(times, values, t)) for t in step_times]
        lines.append("| " + s + " | " + " | ".join(row_vals) + " |")

    return "\n".join(lines)


mcp = FastMCP("vcd-tools")


@mcp.tool(
    name="list_signals",
    description="List all signals in a VCD file.",
)
def list_signals(vcd_path: str) -> List[str]:
    return _load_vcd_signals(vcd_path)


@mcp.tool(
    name="signal_values",
    description=(
        "Given selected signals, return their values as a Markdown table (signals as rows, steps as columns)."
    ),
)
def signal_values(
    vcd_path: str,
    signals: List[str],
) -> str:
    return _steps_markdown_table(
        vcd_path,
        signals,
    )


if __name__ == "__main__":
    mcp.run()
