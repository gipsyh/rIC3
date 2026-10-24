module xor_flip (
    input             clk,
    input             rst_n,
    input      [ 4:0] flip_i,
    input      [ 4:0] flip_j,
    output reg [31:0] q
);
    always @(posedge clk) begin
        if (!rst_n) begin
            q <= '0;
        end else begin
            q[flip_i] <= ~q[flip_i];
            q[flip_j] <= ~q[flip_j];
        end
    end


    always_comb assume (flip_i != flip_j);
    always @(posedge clk) begin
        if (rst_n) begin
            assert (^q == 1'b0);
        end
    end

endmodule

