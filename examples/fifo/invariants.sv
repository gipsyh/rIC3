module invariants (
    input logic clk,
    input logic rst_n
);
    reg first_push;
    always @(posedge clk) begin
        if (!rst_n) begin
            first_push <= 0;
        end else begin
            if (fifo.wr_en && !fifo.full && fifo.fifo_check_i.push_count == fifo.fifo_check_i.cr_count) begin
                first_push <= 1;
            end
        end
    end

    P0 :
    assert property (@(posedge clk) disable iff (!rst_n) first_push |-> fifo.mem[fifo.fifo_check_i.cr_count] == fifo.fifo_check_i.check_data);
endmodule

bind fifo invariants invariants (.*);
