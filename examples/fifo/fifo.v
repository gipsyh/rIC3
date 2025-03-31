module fifo (
    input clk,
    input rst,
    input wr_en, rd_en,
    input [7:0] data_in,
    output reg [7:0] data_out,
    output wire empty, full
);

    reg [7:0] mem [3:0];
    reg [1:0] rd_ptr, wr_ptr;
    reg [2:0] count;

    initial rd_ptr = 0;
    initial wr_ptr = 0;
    initial count  = 0;

    always @(posedge clk) begin
        if (wr_en && !full) begin
            mem[wr_ptr] <= data_in;
            wr_ptr <= wr_ptr + 1;
            count  = count + 1;
        end
        if (rd_en && !empty) begin
            data_out <= mem[rd_ptr];
            rd_ptr <= rd_ptr + 1;
            count  = count - 1;
        end
    end

    assign empty = (count == 0);
    assign full  = (count == 4);
    
    always @(posedge clk) begin
        assert((count & 3) == ((wr_ptr - rd_ptr) & 3));
    end

endmodule