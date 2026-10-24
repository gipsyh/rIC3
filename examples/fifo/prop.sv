module fifo_check #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16,
    localparam ADDR_WIDTH = $clog2(DEPTH)
) (
    input wire clk,
    input wire rst_n
);

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
            if (fifo.wr_en && !fifo.full) begin
                push_count <= push_count + 1;
                if (push_count == cr_count) begin
                    check_data <= fifo.wdata;
                end
            end
            if (fifo.rd_en && !fifo.empty) begin
                pop_count <= pop_count + 1;
                if (pop_count == cr_count) begin
                    P0 : assert (check_data == fifo.mem[pop_count]);
                end
            end
        end
    end
endmodule

bind fifo fifo_check #(
    .DATA_WIDTH(DATA_WIDTH),
    .DEPTH(DEPTH)
) fifo_check_i (
    .clk  (clk),
    .rst_n(rst_n)
);
