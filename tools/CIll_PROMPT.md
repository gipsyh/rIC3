## Core Concepts
- Correctness: An assertion is correct if it holds for all states reachable from the initial state. A correct assertion is referred to as an invariant. If an assertion is incorrect, a Counterexample (CEX) exists.
- Induction: An assertion is inductive if, assuming it holds for state $S$, it implies it holds for state $S'$.
- K-Induction: If it holds for steps $0$ to $K-1$, it implies it holds for step $K$.
- CTI (Counterexample to Induction): A trace segment where the assertion holds for the first $K$ steps (from $0$ to $K-1$) but fails at step $K$. If an invariant is not inductive, its CTIs must be unreachable from the initial state.

## Objective
Your goal is to prove the correctness of the original assertions. You may introduce helper assertions to make a non-inductive assertion provable. Specifically, you can eliminate its CTIs by strengthening the proof with helper assertions such that any CTI violates at least one helper assertion. If all helper assertions are inductive, and they enable the original assertion to become inductive as well, then the proof is successful. Therefore, it is strongly recommended to write an **inductive helper assertion**. Nevertheless, it is acceptable for a helper assertion to be temporarily non-inductive; you can introduce additional helper assertions to strengthen it until it becomes inductive.

**Note:** Please reason about the DUT and the potential CTIs as a whole, and prefer more generalized helper assertions that invalidate as many CTIs as possible, as this leads to a more efficient proof. Do not overfit to a single state; instead, generalize from the CTI to a strong and essential invariant. If the helper assertion does not capture the most critical invariant, it may result in an endless stream of CTIs that cannot be fully blocked. 

## `ric3 cill`
You can use it to check whether the assertions are inductive and generate CTI.
- `ric3 cill check`: Performs the following steps automatically:
  1. Bounded Model Checking: Checks the correctness of helper assertions. If a CEX is found, it is saved to `ric3proj/cill/cex.vcd`, and the violated assertion is reported. You should analyze the CEX and fix the incorrect assertion.
  2. **Induction Check:** Each assertion is assigned a temporary `<ID>`, and its inductiveness result is printed. CIll first attempts to prove assertions using IC3; if IC3 times out, CIll falls back to 3-induction with *local proof*. Under local proof, when verifying a set of $n$ properties, we prove a target property $P_t$ while assuming the remaining properties hold as invariants, using them as additional constraints. Formally, the $k$-induction check is: for any path $s_0,\ldots,s_k$, $\left(\bigwedge_{i=0}^{k-1}\ \bigwedge_{j=0}^{n-1} P_j(s_i)\ \land\ \bigwedge_{i=0}^{k-1} T(s_i, s_{i+1}) \right) \Rightarrow P_t(s_k)$.
  3. CTI Validation: If a CTI was generated previously, this step checks whether the new helper assertions successfully block it. If the CTI is not blocked, indicating that the assertion may need further refinement.

- `ric3 cill select <ID>`: Selects a non-inductive assertion to generate CTI. It must be used after `ric3 cill check` reports non-inductive assertions. Only one assertion can be selected at a time. Selecting another one will clear the current selection.
  * Output: Generates a CTI to `ric3proj/cill/cti.vcd`. The CTI contains only the signals relevant to the induction failure; irrelevant signals are either omitted or marked with `'x'`/`'X'`. The CTI trace consists of 4 steps: the first 3 steps satisfy all assertions, while the final step violates the selected assertion.

- `ric3 cill abort`: Discards the current CTI context. Use this if you delete the assertion that generated the CTI, or if you decide not to block the current CTI.

## `vcd-tools` (MCP):
- `vcd.search_signals(vcd_path, pattern)`: Return signals matching the regex `pattern`. It is not recommended to list all signals at once, as this may produce many irrelevant results. Instead, search for the signals you need.
- `vcd.signal_values(vcd_path, signals=[...])`: Inspect signal values. signal names must match exactly (no fuzzy matching / regex).

## Operational Constraints (CRITICAL)
- **Editing Limits**: strictly **ONLY** add, modify, or delete code between `/// Helper Assertion Begin` and `/// Helper Assertion End`.
- All helper assertions and auxiliary registers must be named `h_*`.
- **Prohibitions**:
  * **NO** `assume` statements allowed.
  * **NO** modifying the original DUT logic or `o_*` assertions.
  * **NO** creating new `/// Helper Assertion Begin/End` blocks.
- Do not read files in `ric3proj/` other than the specified `.vcd` files.
- You can only use the three `ric3 cill` commands listed above; no other `ric3` commands are permitted.

## NOTE
- Because we rely on IC3 and local proof, the inductiveness results can be **unstable** (i.e., may fluctuate across iterations). However, by iteratively generating helper assertions that invalidate the CTIs, we increase the overall likelihood of eventually establishing inductiveness.
- Variable assignments in each new CTI/CEX are independent of those in previous ones; signal values may be completely different from earlier cases and must be re-examined each time.
- The generated VCD for CTI includes only the signals pertinent to the current non-induction failure. If a DUT signal is absent from the VCD, or if specific bits of a signal are marked as 'x'/'X', it indicates that these elements are irrelevant to the non-inductive transition. It is highly recommended to derive helper assertions based solely on the relevant (non-'x') signals.
- `ric3` uses Yosys-Slang as the DUT parser and does not include a Verific frontend. Please avoid using SVA constructs (e.g., `|->`), but `$past(signal, cycle)` is supported. It is recommended to write assertions in the following format:
    ```systemverilog
    always @(posedge clk) begin
        if (!reset) 
            h_*: assert();
    end
    ```
- Submodule signals can be accessed using '.' notation.
- `ric3` restricts the reset signal to be high only at cycle 0 (step 0 in CEX (NOT CTI)), with no resets afterward (`fminit -seq reset 0,1`). During cycle 0, register values may be non-deterministic. Therefore, make sure invariants are checked post-reset: `if (!reset) h_*: assert`.
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
wire [$clog2(W)-1:0] any;
always @(posedge clk) begin
  h_*: assert (array[any] > 0);
end
```
- If you need an anyconst value (a random value that stays stable during each cycle), write it like this:
```systemverilog
reg [W-1:0] anyconst_reg;
always @(posedge clk) begin
  anyconst_reg <= anyconst_reg;
end
```

