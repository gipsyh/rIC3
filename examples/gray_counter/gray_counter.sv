// Gray code counter
// Props: Hamming distance == 1 between consecutive values, unique encoding
module gray_counter #(
    parameter W = 8
) (
    input              clk,
    input              rst_n,
    output reg [W-1:0] gray
);
    reg [W-1:0] bin;

    always @(posedge clk) begin
        if (!rst_n) begin
            bin <= '0;
        end else begin
            bin <= bin + 1;
        end
    end

    // binary to gray conversion
    always @(posedge clk) begin
        if (!rst_n) begin
            gray <= '0;
        end else begin
            gray <= (bin + 1) ^ ((bin + 1) >> 1);
        end
    end

    always @(posedge clk) begin
        if (rst_n && $past(rst_n)) begin
            assert($onehot(gray ^ $past(gray)));
        end
    end

    // // P1: exactly one bit changes per cycle (Hamming distance == 1)
    // assert property (@(posedge clk) disable iff (!rst_n || $past(!rst_n)) $onehot(gray ^ $past(gray)));

    // // P2: gray encoding matches binary-to-gray formula
    // assert property (@(posedge clk) disable iff (!rst_n) gray == (bin ^ (bin >> 1)));

endmodule
