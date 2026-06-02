## Core Concepts
- Correctness: An assertion is correct if it holds for all states reachable from the initial state. A correct assertion is referred to as an invariant. If an assertion is incorrect, a Counterexample (CEX) exists.
- Inductiveness: An assertion is inductive if, assuming it holds for state $S$, it implies it holds for state $S'$.
- K-Induction: If it holds for steps $0$ to $K-1$, it implies it holds for step $K$.
- CTI (Counterexample to Induction): A trace segment where the assertion holds for the first $K$ steps (from $0$ to $K-1$) but fails at step $K$. A CTI is a proof artifact, not necessarily a reachable CEX. If an invariant is correct but not inductive, its CTIs must be unreachable from the initial state.

## Objective
Your goal is to prove the correctness of the original assertions. You may introduce invariants (helper assertions) to make a non-inductive assertion provable. Specifically, you can eliminate its CTIs by strengthening the proof with helper assertions such that any CTI violates at least one helper assertion. If all helper assertions are inductive, and they enable the original assertion to become inductive as well, then the proof is successful. Therefore, it is strongly recommended to write an **inductive helper assertion**. Nevertheless, it is acceptable for a helper assertion to be temporarily non-inductive; you can introduce additional helper assertions to strengthen it until it becomes inductive.

**Note:** Please reason about the DUT and the potential CTIs as a whole, and prefer more generalized helper assertions that invalidate as many CTIs as possible, as this leads to a more efficient proof. Do not overfit to a single state; instead, generalize from the CTI to a strong and essential invariant. If the helper assertion does not capture the most critical invariant, it may result in an endless stream of CTIs that cannot be fully blocked. 

## `ric3 cill`
You can use it to check whether the assertions are inductive and generate CTI.
- `ric3 cill check`: Performs the following steps automatically:
  1. Correctness Checking: Performs bounded correctness checking for helper assertions by Bounded Model Checking. If a CEX is found, it is saved to `ric3proj/cill/cex.strace`, and the violated assertion is reported. You should analyze the CEX and fix the incorrect assertion. If no CEX is found, this does not prove correctness. It only allows the inductiveness workflow to continue.
  2. Inductiveness Check: CIll first attempts to prove assertions using IC3; if IC3 times out, CIll falls back to 3-induction with *local proof*. Under local proof, when verifying a set of $n$ properties, we prove a target property $P_t$ while assuming the remaining properties hold as invariants, using them as additional constraints. Formally, the $k$-induction check is: for any path $s_0,\ldots,s_k$, $\left(\bigwedge_{i=0}^{k-1}\ \bigwedge_{j=0}^{n-1} P_j(s_i)\ \land\ \bigwedge_{i=0}^{k-1} T(s_i, s_{i+1}) \right) \Rightarrow P_t(s_k)$. The inductiveness result of each assertions is printed.
     - Generates a symbolic CTI trace for each non-inductive property at `ric3proj/cill/cti/<prop>.strace`. Analyze the `.strace` file with the trace MCP tools. The CTI trace consists of 4 steps: the first 3 steps satisfy all assertions, while the final step violates the selected assertion. The `ric3proj/cill/cti/` directory is refreshed on each `ric3 cill check`, so it only contains CTIs from the latest run.

- `ric3 cill abort`: Discards the current CTI context. Use this if you delete the assertion that generated the CTI, or if you decide not to block the current CTI.

- If `ric3` is not available in the current environment, it may be available through Docker. In that case, use `docker run -v $HOME:$HOME -w $PWD -it --rm ric3 cill <command>`.

## `ric3_trace_tools` (MCP):
- `search_signals(path, pattern)`: Search signal names in a `.strace` file by regex `pattern`. Pass the `.strace` path reported by `ric3 cill check`. It is not recommended to list all signals at once, as this may produce many irrelevant results. Instead, search for the signals you need.
- `signal_values(path, signals=[...])`: Inspect selected signal values in a `.strace` file. Signal names must match exactly (no fuzzy matching or regex).

## Operational Constraints (CRITICAL)
- Strictly **ONLY** add, modify, or delete code in `invariants.sv`.
- All helper assertions and auxiliary registers must be named `h_*`.
- **NO** `assume` statements allowed.
- Do not read files in `ric3proj/` other than the specified `.strace` files.
- You can only use the two `ric3 cill` commands listed above; no other `ric3` commands are permitted.

## NOTE
- Because we rely on IC3 and local proof, the inductiveness results can be **unstable** (i.e., may fluctuate across iterations). However, by iteratively generating helper assertions that invalidate the CTIs, we increase the overall likelihood of eventually establishing inductiveness.
- Variable assignments in each new CTI/CEX are independent of those in previous ones; signal values may be completely different from earlier cases and must be re-examined each time.
- A CTI should be blocked by adding invariants that exclude unreachable states. Do not change DUT behavior merely to match a CTI.
- The generated `.strace` may omit irrelevant signals or mark irrelevant bits as `'x'`/`'X'`. It may also contain extra symbols. Derive helper assertions from the stable, non-`X` values that are relevant to the failed transition.
- `ric3` uses Yosys-Slang as the DUT parser and does not include a Verific frontend. Please avoid SVA constructs (e.g., `|->`), but `$past(signal, cycle)` is supported. It is recommended to write assertions in the following format:
    ```systemverilog
    always @(posedge clk) begin
        if (<condition>)
            h_*: assert();
    end
    ```
- Submodule signals can be accessed using '.' notation.
- `ric3` restricts reset to be active only at cycle 0 (step 0 in CEX, not CTI), with no resets afterward. During cycle 0, register values may be non-deterministic. Therefore, make sure invariants are checked only post-reset.
- SystemVerilog has no built-in quantifiers. A common workaround is to unroll the assertion with a `generate` loop. However, we try to avoid `generate` because it replicates the assertion `W` times and can slow down model checking. Instead, we emulate quantification with a symbolic index:
```systemverilog
/// Not recommended:
genvar i;
generate
  for (i = 0; i < W; i++) begin
    h_*: assert (array[i] > 0);
  end
endgenerate
/// Recommended:
wire [$clog2(W)-1:0] h_any;
always @(posedge clk) begin
  h_array_positive: assert (array[h_any] > 0);
end
```
- If you need an anyconst value (a random value that stays stable during each cycle), write it like this:
```systemverilog
reg [W-1:0] h_anyconst_reg;
always @(posedge clk) begin
  h_anyconst_reg <= h_anyconst_reg;
end
```
