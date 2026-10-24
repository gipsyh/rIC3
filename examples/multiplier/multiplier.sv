module multiplier #(
    parameter WL = 16,
    parameter WS = WL / 2
) (
    input clk,
    input rst_n,
    input iex,
    input [WS-1:0] ix,
    input iey,
    input [WS-1:0] iy
);
    reg x, y;
    reg [WL-1:0] ma, mb;
    reg [WS-1:0] na, nb, nc, nd;
    always @(posedge clk) begin
        if (!rst_n) begin
            x  <= 1;
            y  <= 1;
            ma <= 0;
            mb <= 0;
            na <= 0;
            nb <= 0;
            nc <= 0;
            nd <= 0;
        end else begin
            ma <= na * nb;
            if (x || y) mb <= nc * nd;
            if (iex) begin
                na <= ix;
                nc <= ix;
            end
            if (iey) begin
                nb <= iy;
                nd <= iy;
            end
            x <= iex;
            y <= iey;
            assert (ma == mb);
        end
    end
endmodule
