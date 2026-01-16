from __future__ import annotations

import re
from bisect import bisect_right
from typing import Dict, List, Sequence, Tuple, Union
from mcp.server.fastmcp import FastMCP
from vcdvcd import VCDVCD


def _strip_end_prefix(name: str) -> str:
    """Remove '$end.' prefix from signal name if present."""
    if name.startswith("$end."):
        return name[5:]
    return name


def _load_vcd_signals(vcd_path: str) -> List[str]:
    vcd = VCDVCD(vcd_path, only_sigs=True)
    signals = [_strip_end_prefix(s) for s in getattr(vcd, "signals", [])]
    return sorted(signals)


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
) -> Tuple[List[str], List[str]]:
    """Returns (resolved_signals, not_found_signals)."""
    resolved: List[str] = []
    not_found: List[str] = []
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
            not_found.append(name)
            continue

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
    return out, not_found


def _extract_time_markers(vcd_path: str) -> List[int]:
    """Return all VCD time markers (#<time>) in file order, after $enddefinitions."""
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
    times = times[:-1]
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


def _steps_json(
    vcd_path: str,
    signals: Sequence[str],
) -> Dict[str, Union[List[str], str]]:
    if not signals:
        raise ValueError("signals must be a non-empty list")

    vcd = VCDVCD(vcd_path, only_sigs=False)
    raw_signals = getattr(vcd, "signals", [])
    stripped_to_raw: Dict[str, str] = {_strip_end_prefix(s): s for s in raw_signals}
    available = sorted(stripped_to_raw.keys())
    signal_names, not_found = _expand_signal_names(available, signals)
    step_times = _sample_times(vcd_path)

    if not step_times:
        raise ValueError("No steps found (no sampled timepoints)")

    sig_indexes: Dict[str, Tuple[List[int], List[str]]] = {}
    for s in signal_names:
        raw_name = stripped_to_raw[s]
        tv = getattr(vcd[raw_name], "tv", None)
        if tv is None:
            raise ValueError(f"No data for signal: {s}")
        sig_indexes[s] = _build_tv_index(tv)

    result: Dict[str, Union[List[str], str]] = {}
    for s in signal_names:
        times, values = sig_indexes[s]
        row_vals = [_format_hex(_value_at(times, values, t)) for t in step_times]
        result[s] = row_vals

    # Add placeholder for signals that were not found
    for s in not_found:
        result[s] = "<SIGNAL NOT FOUND OR IRRELEVANT>"

    return result


mcp = FastMCP("vcd-tools")


@mcp.tool(
    name="search_signals",
    description="Search signals in a VCD file by regex pattern. Returns matching signal names. The vcd_path must be an absolute path.",
)
def search_signals(vcd_path: str, pattern: str) -> List[str]:
    signals = _load_vcd_signals(vcd_path)
    regex = re.compile(pattern)
    return [s for s in signals if regex.search(s)]


@mcp.tool(
    name="signal_values",
    description=(
        "Returns the values of selected signals as a JSON object. Keys are signal names, "
        "and values are arrays representing the signal state at each step. "
        "The vcd_path must be an absolute path."
    ),
)
def signal_values(
    vcd_path: str,
    signals: List[str],
) -> Dict[str, Union[List[str], str]]:
    return _steps_json(
        vcd_path,
        signals,
    )


if __name__ == "__main__":
    mcp.run()
