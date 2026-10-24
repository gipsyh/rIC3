module pipe #(
    parameter W = 16
) (
    input clk,
    rst_n,
    stall,
    input [W-1:0] a,
    b,
    c
);
    reg [W-1:0] r1, r2, r3, r4, d1, d2;
    always @(posedge clk) begin
        if (!rst_n) begin
            {r1, r2, r3, r4, d1, d2} <= 0;
        end else begin
            if (!stall) begin
                r1 <= a + b;
                r2 <= c;
                r3 <= a + c;
                r4 <= b;
                d1 <= r1 + r2;
                d2 <= r3 + r4;
            end
        end
    end

    assert property (@(posedge clk) disable iff (!rst_n) r1 + r2 == r3 + r4);
    assert property (@(posedge clk) disable iff (!rst_n) d1 == d2);
endmodule
