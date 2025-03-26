`define W 10

module main(
    input wire clk,
    input wire rst,
);
    reg [`W-1:0] count;
    initial count = {`W{1'b0}};
    always @(posedge clk) begin
        if (rst) begin
            count <= {`W{1'b0}};
        end else begin
            count <= count + 1;
        end
    end

    always @(*) begin
        assert(count != {`W{1'b1}});
    end
endmodule