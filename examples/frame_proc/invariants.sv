module invariants (
    input logic clk,
    input logic rst_n
);
// To use a signal from frame_proc, reference it as frame_proc.XXX.

endmodule

bind frame_proc invariants invariants (.*);
