// Priority encoder
// Props: output matches highest-priority bit, valid flag correctness
module priority_enc #(
    parameter N = 8
) (
    input              clk,
    input              rst_n,
    input      [N-1:0] req,
    output reg [$clog2(N)-1:0] idx,
    output reg         valid
);
    always @(posedge clk) begin
        if (!rst_n) begin
            idx   <= '0;
            valid <= 1'b0;
        end else begin
            valid <= |req;
            idx   <= '0;
            for (int i = N-1; i >= 0; i--) begin
                if (req[i]) idx <= i[$clog2(N)-1:0];
            end
        end
    end

    // --- Formal Properties ---

    reg [N-1:0] req_d;
    always @(posedge clk)
        if (!rst_n) req_d <= '0;
        else        req_d <= req;

    // P1: valid iff there was a request
    assert property (@(posedge clk) disable iff (!rst_n)
        valid == |req_d);

    // P2: granted index was actually requested
    assert property (@(posedge clk) disable iff (!rst_n)
        valid |-> req_d[idx]);

    // P3: no higher-priority bit was set
    // (all bits above idx must be 0)
    reg no_higher;
    always_comb begin
        no_higher = 1'b1;
        for (int i = 0; i < N; i++) begin
            if (i > idx) no_higher = no_higher & ~req_d[i];
        end
    end
    assert property (@(posedge clk) disable iff (!rst_n)
        valid |-> no_higher);

endmodule
