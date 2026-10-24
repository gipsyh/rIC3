module counter #(
    parameter int W = 10
) (
    input clk,
    input rst_n
);
    reg [W-1:0] count;
    always @(posedge clk)
        if (!rst_n) begin
            count <= {W{1'b0}};
        end else if (count == {(W - 1) {1'b1}}) begin
            count <= {W{1'b0}};
        end else begin
            count <= count + 1;
        end

    P0 :
    assert property (@(posedge clk) disable iff (!rst_n) count != {W{1'b1}});
    P1 :
    assert property (@(posedge clk) disable iff (!rst_n) count != {(W - 1) {1'b1}});
    P2 :
    assert property (@(posedge clk) disable iff (!rst_n) count != {(W - 2) {1'b1}});
    P3 :
    assert property (@(posedge clk) disable iff (!rst_n) count != {(W - 3) {1'b1}});
    P4 :
    assert property (@(posedge clk) disable iff (!rst_n) count != {(W - 4) {1'b1}});
endmodule
