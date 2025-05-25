module main #(
    parameter int W = 10
) (
    input wire clk,
    input wire rst,
);
    reg [W-1:0] count;
    initial count = {W{1'b0}};
    always @(posedge clk) begin
        if (rst) begin
            count <= {W{1'b0}};
        end else begin
            count <= count + 1;
        end
    end

    always @(posedge clk) begin
        assert (count != {W{1'b1}});
    end
    always @(posedge clk) begin
        assert (s_eventually (count == {W{1'b1}}));
    end
endmodule