// One-hot state register with transitions
// Props: always one-hot, valid transitions only
module onehot_fsm #(
    parameter N = 6
) (
    input            clk,
    input            rst_n,
    input      [2:0] cmd,
    output reg [N-1:0] state
);
    always @(posedge clk) begin
        if (!rst_n) begin
            state    <= {{(N-1){1'b0}}, 1'b1};  // state[0] = 1
        end else begin
            case (1'b1)
                state[0]: if (cmd[0]) state <= (1 << 1);
                state[1]: if (cmd[1]) state <= (1 << 2);
                          else if (cmd[0]) state <= (1 << 3);
                state[2]: state <= (1 << 4);
                state[3]: state <= (1 << 4);
                state[4]: if (cmd[2]) state <= (1 << 5);
                          else        state <= (1 << 0);
                state[5]: state <= (1 << 0);
                default:  state <= {{(N-1){1'b0}}, 1'b1};
            endcase
        end
    end

    // --- Formal Properties ---

    // P1: state is always one-hot
    assert property (@(posedge clk) disable iff (!rst_n)
        $onehot(state));

    // P2: state[5] can only come from state[4]
    reg [N-1:0] prev;
    always @(posedge clk)
        if (!rst_n) prev <= {{(N-1){1'b0}}, 1'b1};
        else        prev <= state;

    assert property (@(posedge clk) disable iff (!rst_n)
        state[5] |-> prev[4]);

    // P3: state[0] can come from reset, state[4], or state[5]
    assert property (@(posedge clk) disable iff (!rst_n)
        (state[0] && !prev[0]) |-> (prev[4] || prev[5]));

endmodule
