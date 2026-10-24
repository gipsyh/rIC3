module fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16,
    localparam ADDR_WIDTH = $clog2(DEPTH)
) (
    input wire clk,
    input wire rst_n,
    input wire wr_en,
    input wire [DATA_WIDTH-1:0] wdata,
    input wire rd_en,
    output wire [DATA_WIDTH-1:0] rdata,
    output wire full,
    output wire empty
);
    reg [DATA_WIDTH-1:0] mem[0:DEPTH-1];
    reg [ADDR_WIDTH-1:0] w_ptr;
    reg [ADDR_WIDTH-1:0] r_ptr;
    reg [ADDR_WIDTH:0] count;

    assign full  = (count == DEPTH);
    assign empty = (count == 0);
    assign rdata = mem[r_ptr];

    always @(posedge clk) begin
        if (!rst_n) begin
            w_ptr <= 0;
        end else if (wr_en && !full) begin
            mem[w_ptr] <= wdata;
            w_ptr <= (w_ptr == DEPTH - 1) ? 0 : w_ptr + 1;
        end
    end

    always @(posedge clk) begin
        if (!rst_n) begin
            r_ptr <= 0;
        end else if (rd_en && !empty) begin
            r_ptr <= (r_ptr == DEPTH - 1) ? 0 : r_ptr + 1;
        end
    end

    always @(posedge clk) begin
        if (!rst_n) begin
            count <= 0;
        end else begin
            case ({
                wr_en && !full, rd_en && !empty
            })
                2'b10:   count <= count + 1;
                2'b01:   count <= count - 1;
                default: count <= count;
            endcase
        end
    end

endmodule
