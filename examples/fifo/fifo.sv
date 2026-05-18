module fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16
) (
    input wire clk,
    input wire rst_n,
    input wire wr_en,
    input wire [DATA_WIDTH-1:0] wdata,
    input wire rd_en,
    output reg [DATA_WIDTH-1:0] rdata,
    output wire full,
    output wire empty
);

    localparam ADDR_WIDTH = $clog2(DEPTH);

    reg [DATA_WIDTH-1:0] mem[0:DEPTH-1];
    reg [ADDR_WIDTH-1:0] w_ptr;
    reg [ADDR_WIDTH-1:0] r_ptr;
    reg [ADDR_WIDTH:0] count;

    assign full  = (count == DEPTH);
    assign empty = (count == 0);

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            w_ptr <= 0;
        end else if (wr_en && !full) begin
            mem[w_ptr] <= wdata;
            w_ptr <= (w_ptr == DEPTH - 1) ? 0 : w_ptr + 1;
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_ptr <= 0;
            rdata <= 0;
        end else if (rd_en && !empty) begin
            rdata <= mem[r_ptr];
            r_ptr <= (r_ptr == DEPTH - 1) ? 0 : r_ptr + 1;
        end
    end

    always @(posedge clk or negedge rst_n) begin
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

    reg [ADDR_WIDTH-1:0] cr_count;
    reg [ADDR_WIDTH-1:0] push_count;
    reg [ADDR_WIDTH-1:0] pop_count;
    reg [DATA_WIDTH-1:0] check_data;

    always @(posedge clk) begin
        if (!rst_n) begin
            push_count <= 0;
            pop_count  <= 0;
        end else begin
            cr_count <= cr_count;
            if (wr_en && !full) begin
                push_count <= push_count + 1;
                if (push_count == cr_count) begin
                    check_data <= wdata;
                end
            end
            if (rd_en && !empty) begin
                pop_count <= pop_count + 1;
                if (pop_count == cr_count) begin
                    P0 : assert (check_data == mem[pop_count]);
                end
            end
        end
    end
endmodule
