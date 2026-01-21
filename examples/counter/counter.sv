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

    always_comb assume (!rst_n == $initstate);
    always @(posedge clk)
        if (rst_n) begin
            p0 : assert (count != {W{1'b1}});
            p1 : assert (count <= {(W - 1) {1'b1}});
            p2 : assert (count != {(W - 2) {1'b1}});
            p3 : assert (count != {(W - 3) {1'b1}});
            p4 : assert (count != {(W - 4) {1'b1}});
        end
endmodule
