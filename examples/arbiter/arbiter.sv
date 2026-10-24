// Round-robin arbiter
// Props: mutual exclusion, no spurious grant, fairness
module arbiter #(
    parameter N = 4
) (
    input              clk,
    input              rst_n,
    input      [N-1:0] req,
    output reg [N-1:0] grant
);
    reg [$clog2(N)-1:0] last;

    always @(posedge clk) begin
        if (!rst_n) begin
            grant <= '0;
            last  <= '0;
        end else begin
            grant <= '0;
            if (|req) begin
                // round-robin: scan from last+1
                for (int i = 0; i < N; i++) begin
                    automatic int idx = (last + 1 + i) % N;
                    if (req[idx]) begin
                        grant[idx] <= 1'b1;
                        last <= idx[$clog2(N)-1:0];
                        break;
                    end
                end
            end
        end
    end

    // --- Formal Properties ---

    // P0: mutual exclusion — at most one grant at a time
    P0 :
    assert property (@(posedge clk) disable iff (!rst_n) $onehot0(grant));

    // P1: no grant without request
    P1 :
    assert property (@(posedge clk) disable iff (!rst_n) (grant & $past(~req)) == '0);

    // P2: if any request, exactly one grant
    P2 :
    assert property (@(posedge clk) disable iff (!rst_n || $past(!rst_n)) $past(|req) |-> $onehot(grant));

    // P3: fairness — track starvation for req[0]
    reg [3:0] wait_cnt;
    always @(posedge clk) begin
        if (!rst_n) wait_cnt <= '0;
        else if (req[0] && !grant[0]) wait_cnt <= wait_cnt + 1;
        else wait_cnt <= '0;
    end
    P3 :
    assert property (@(posedge clk) disable iff (!rst_n) wait_cnt < N);

endmodule
