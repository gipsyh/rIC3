/*

你是一个成熟的芯片设计工程师，擅长使用verilog去编写代码，请你帮我写一个module，要求如下：

1、接口i_valid_1 o_ready_1为数据流的开始，其握手成功代表dut接受到了一个帧，i_frame_type是一个2bit信号，在i_valid_1拉高时有效，若i_frame_type==0，代表帧头；若i_frame_type==1，代表帧身；若i_frame_type==2，代表帧尾；若i_frame_type==3，代表帧错误；i_frame_psn是24bit信号，在i_valid_1拉高时有效，每个无误帧的psn是递增+1的。i_frame_data是256bit的数据。在i_valid_1拉高时有效。

note：什么是正确帧？1、头在帧尾前或者同时收到；2、psn相较于上一个正确帧的psn+1；3、i_frame_type！=3。若收到错误帧，则该帧不作数，下一个正确帧的格式不变

2、如果帧正确，则dut会对此帧的i_frame_data加上对应的i_frame_psn。若无前帧阻塞，处理5个周期，最终会从o_valid_2接口上输出，i_ready_2是o_valid_2的握手信号。随路信号包括o_frame_psn_2，o_frame_type_2，这两个信号与该帧输入时的i_frame_psn，i_frame_type完全一样

3、若帧错误，则dut会对此帧的i_frame_data做处理全等于0。若无前帧阻塞，需要处理2个周期。最终会从o_valid_3接口上输出，i_ready_3是o_valid_3的握手信号。随路信号包括o_frame_psn_3，o_frame_type_3，这两个信号与该帧输入时的i_frame_psn，i_frame_type完全一样。

4、不论是正确帧还是错误帧，在o_valid_2获o_valid_3接口输出后，若无前帧阻塞，都会在4周期后，在o_valid_4接口输出，i_ready_4是o_valid_4的握手信号。随路信号包括o_frame_psn_4，o_frame_type_4，这两个信号与该帧输入时的i_frame_psn，i_frame_type完全一样

5、请注意，该模块遵循先入的帧一定会先处理，例如：在i_valid_1入口顺序输入的帧为A->B->C->D，A与C为正确帧，B与D为错误帧，则o_valid_2接口输出A后o_valid_3接口才会输出B，接着o_valid_2接口输出C，最后o_valid_3接口输出D，o_valid_4接口的输出顺序一定为ABCD
*/
module frame_proc #(
    parameter DWIDTH = 256,
    parameter MAIN_FIFO_DEPTH = 8,
    parameter RPT_FIFO_DEPTH = 16,
    parameter PSN_WIDTH = 24
) (
    input logic clk,
    input logic rst_n,

    // Interface 1: Input Stream
    input  logic                 i_valid_1,
    output logic                 o_ready_1,
    input  logic [          1:0] i_frame_type,  // 0:Head, 1:Body, 2:Tail, 3:Error
    input  logic [PSN_WIDTH-1:0] i_frame_psn,
    input  logic [   DWIDTH-1:0] i_frame_data,

    // Interface 2: Correct Frame Output
    output logic                 o_valid_2,
    input  logic                 i_ready_2,
    output logic [PSN_WIDTH-1:0] o_frame_psn_2,
    output logic [          1:0] o_frame_type_2,
    output logic [   DWIDTH-1:0] o_frame_data_2,

    // Interface 3: Error Frame Output
    output logic         o_valid_3,
    input  logic         i_ready_3,
    output logic [ 23:0] o_frame_psn_3,
    output logic [  1:0] o_frame_type_3,
    output logic [255:0] o_frame_data_3,

    // Interface 4: Report Output
    output logic        o_valid_4,
    input  logic        i_ready_4,
    output logic [23:0] o_frame_psn_4,
    output logic [ 1:0] o_frame_type_4
);

    //==========================================================================
    // Parameter & Enum Definitions
    //==========================================================================
    localparam TYPE_HEAD = 2'd0;
    localparam TYPE_BODY = 2'd1;
    localparam TYPE_TAIL = 2'd2;
    localparam TYPE_ERR = 2'd3;

    localparam DELAY_CORRECT = 3'd5;
    localparam DELAY_ERROR = 3'd2;
    localparam DELAY_REPORT = 3'd4;

    // FSM States
    typedef enum logic [1:0] {
        S_IDLE,
        S_PROCESS,
        S_OUTPUT
    } state_t;

    //==========================================================================
    // Part 1: Input Validation & Pre-computation
    //==========================================================================
    logic [PSN_WIDTH-1:0] exp_psn;
    logic                 inside_frame;
    logic                 frame_is_correct;

    // Pre-calculated data to be pushed into FIFO
    logic [   DWIDTH-1:0] w_data_pre;

    // 1.1 Sequence Check (Head before Tail)
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            inside_frame <= 1'b0;
        end else if (i_valid_1 && o_ready_1) begin
            if (i_frame_type == TYPE_HEAD) inside_frame <= 1'b1;
            else if (i_frame_type == TYPE_TAIL) inside_frame <= 1'b0;
        end
    end

    // 1.2 Sanity Check Logic
    // Valid sequence: Either it is a HEAD (starts seq) OR we are already inside a frame
    assign seq_ok = (i_frame_type == TYPE_HEAD) || inside_frame;
    assign psn_ok = (i_frame_psn == exp_psn);
    assign type_ok = (i_frame_type != TYPE_ERR);

    assign frame_is_correct = seq_ok && psn_ok && type_ok;

    // 1.3 Expected PSN Update
    // "每个无误帧的psn是递增+1的...若收到错误帧，则该帧不作数"
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            exp_psn <= 'd0;
        end else if (i_valid_1 && o_ready_1 && frame_is_correct) begin
            exp_psn <= exp_psn + 1'b1;
        end
    end

    // 1.4 Data Processing (Pre-calculation)
    // "正确：data + psn", "错误：data = 0"
    always_comb begin
        if (frame_is_correct) begin
            w_data_pre = i_frame_data + {232'd0, i_frame_psn};
        end else begin
            w_data_pre = 256'd0;
        end
    end

    //==========================================================================
    // Part 2: Main FIFO (Buffer & Order Preservation)
    //==========================================================================
    // Structure: {is_correct, type, psn, processed_data}
    // Width: 1 + 2 + PSN_WIDTH + DWIDTH = 283 bits
    localparam MAIN_FIFO_WIDTH = 1 + 2 + PSN_WIDTH + DWIDTH;

    logic                       main_fifo_wr;
    logic                       main_fifo_rd;
    logic                       main_fifo_full;
    logic                       main_fifo_empty;
    logic [MAIN_FIFO_WIDTH-1:0] main_fifo_din;
    logic [MAIN_FIFO_WIDTH-1:0] main_fifo_dout;
    // Connect Input to FIFO
    assign main_fifo_din = {frame_is_correct, i_frame_type, i_frame_psn, w_data_pre};
    assign main_fifo_wr  = i_valid_1 && !main_fifo_full;  // Simple flow control
    assign o_ready_1     = !main_fifo_full;

    // Instantiate FIFO (Assuming a standard sync FIFO behavior here)
    // For this example, I will use a simple RTL model. In real chip, use IP.
    fifo #(
        .DATA_WIDTH(MAIN_FIFO_WIDTH),
        .DEPTH(MAIN_FIFO_DEPTH)  // Depth adjustable
    ) u_main_fifo (
        .clk  (clk),
        .rst_n(rst_n),
        .wr_en(main_fifo_wr),
        .wdata(main_fifo_din),
        .rd_en(main_fifo_rd),
        .rdata(main_fifo_dout),
        .full (main_fifo_full),
        .empty(main_fifo_empty)
    );

    // Unpack FIFO output
    logic                 f_correct;
    logic [          1:0] f_type;
    logic [PSN_WIDTH-1:0] f_psn;
    logic [   DWIDTH-1:0] f_data;
    assign {f_correct, f_type, f_psn, f_data} = main_fifo_dout;

    //==========================================================================
    // Part 3: Main Processing FSM (Interfaces 2 & 3)
    //==========================================================================
    state_t state_cur, state_next;
    logic [2:0] delay_cnt;
    logic [2:0] target_delay;

    // Handshake success flag to trigger Report FIFO
    logic       tx_done;

    // Determine target delay based on frame correctness
    assign target_delay = f_correct ? DELAY_CORRECT : DELAY_ERROR;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            state_cur <= S_IDLE;
            delay_cnt <= 3'd0;
        end else begin
            state_cur <= state_next;

            if (state_cur == S_PROCESS) begin
                delay_cnt <= delay_cnt + 1'b1;
            end else begin
                delay_cnt <= 3'd0;
            end
        end
    end

    // Report FIFO Flow Control Check
    logic rpt_fifo_full;  // From Part 4

    always_comb begin
        state_next   = state_cur;
        main_fifo_rd = 1'b0;

        case (state_cur)
            S_IDLE: begin
                // Only start if Main FIFO has data AND Report FIFO has space
                // (Prevent deadlock/blocking if IF4 is stuck)
                if (!main_fifo_empty && !rpt_fifo_full) begin
                    // We peek the FIFO data during PROCESS state, 
                    // only pop when we move to OUTPUT or finish processing
                    state_next = S_PROCESS;
                end
            end

            S_PROCESS: begin
                // target_delay - 1 because 0..N-1 is N cycles
                if (delay_cnt >= target_delay - 1) begin
                    state_next = S_OUTPUT;
                end
            end

            S_OUTPUT: begin
                if (f_correct) begin
                    if (i_ready_2) begin
                        state_next   = S_IDLE;
                        main_fifo_rd = 1'b1;  // Pop current frame
                    end
                end else begin
                    if (i_ready_3) begin
                        state_next   = S_IDLE;
                        main_fifo_rd = 1'b1;  // Pop current frame
                    end
                end
            end
        endcase
    end

    // Interface 2 Output Logic
    assign o_valid_2 = (state_cur == S_OUTPUT) && f_correct;
    assign o_frame_psn_2 = f_psn;
    assign o_frame_type_2 = f_type;
    assign o_frame_data_2 = f_data;

    // Interface 3 Output Logic
    assign o_valid_3 = (state_cur == S_OUTPUT) && !f_correct;
    assign o_frame_psn_3 = f_psn;
    assign o_frame_type_3 = f_type;
    assign o_frame_data_3 = f_data;  // Already 0 from input stage logic

    // Detect handshake completion
    assign tx_done = (state_cur == S_OUTPUT) && 
                     ((f_correct && i_ready_2) || (!f_correct && i_ready_3));

    //==========================================================================
    // Part 4: Report Path (Interface 4)
    //==========================================================================
    // Strategy: Push metadata to a second FIFO when IF2/IF3 finishes.
    // Structure: {psn, type}
    localparam RPT_FIFO_WIDTH = 2 + PSN_WIDTH;
    logic                      rpt_fifo_wr;
    logic                      rpt_fifo_rd;
    logic                      rpt_fifo_empty;
    logic [RPT_FIFO_WIDTH-1:0] rpt_fifo_din;
    logic [RPT_FIFO_WIDTH-1:0] rpt_fifo_dout;

    assign rpt_fifo_wr  = tx_done;
    assign rpt_fifo_din = {f_psn, f_type};

    fifo #(
        .DATA_WIDTH(RPT_FIFO_WIDTH),
        .DEPTH(RPT_FIFO_DEPTH)
    ) u_rpt_fifo (
        .clk  (clk),
        .rst_n(rst_n),
        .wr_en(rpt_fifo_wr),
        .wdata(rpt_fifo_din),
        .rd_en(rpt_fifo_rd),
        .rdata(rpt_fifo_dout),
        .full (rpt_fifo_full),
        .empty(rpt_fifo_empty)
    );

    // Report FSM
    state_t r_state_cur, r_state_next;
    logic [2:0] r_delay_cnt;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            r_state_cur <= S_IDLE;
            r_delay_cnt <= 3'd0;
        end else begin
            r_state_cur <= r_state_next;
            if (r_state_cur == S_PROCESS) r_delay_cnt <= r_delay_cnt + 1'b1;
            else r_delay_cnt <= 3'd0;
        end
    end

    always_comb begin
        r_state_next = r_state_cur;
        rpt_fifo_rd  = 1'b0;

        case (r_state_cur)
            S_IDLE: begin
                if (!rpt_fifo_empty) begin
                    r_state_next = S_PROCESS;
                end
            end

            S_PROCESS: begin
                // Wait 4 cycles
                if (r_delay_cnt >= DELAY_REPORT - 1) begin
                    r_state_next = S_OUTPUT;
                end
            end

            S_OUTPUT: begin
                if (i_ready_4) begin
                    r_state_next = S_IDLE;
                    rpt_fifo_rd  = 1'b1;  // Pop
                end
            end
        endcase
    end

    assign o_valid_4      = (r_state_cur == S_OUTPUT);
    assign o_frame_psn_4  = rpt_fifo_dout[PSN_WIDTH+1:2];
    assign o_frame_type_4 = rpt_fifo_dout[1:0];

    localparam TARGET_WIDTH = MAIN_FIFO_DEPTH > RPT_FIFO_DEPTH ? MAIN_FIFO_DEPTH : RPT_FIFO_DEPTH;
    //==============================================================
    // 1. 事务计数器 (保持不变)
    //==============================================================
    logic [TARGET_WIDTH-1:0] cnt_in;
    logic [TARGET_WIDTH-1:0] cnt_out_main;
    logic [TARGET_WIDTH-1:0] cnt_out_rpt;

    always_ff @(posedge clk) begin
        if (!rst_n) cnt_in <= 0;
        else if (i_valid_1 && o_ready_1) cnt_in <= cnt_in + 1'b1;
    end

    wire tx_2_hs = o_valid_2 && i_ready_2;
    wire tx_3_hs = o_valid_3 && i_ready_3;

    always_ff @(posedge clk) begin
        if (!rst_n) cnt_out_main <= 0;
        else if (tx_2_hs || tx_3_hs) cnt_out_main <= cnt_out_main + 1'b1;
    end

    always_ff @(posedge clk) begin
        if (!rst_n) cnt_out_rpt <= 0;
        else if (o_valid_4 && i_ready_4) cnt_out_rpt <= cnt_out_rpt + 1'b1;
    end

    //==============================================================
    // 2. 符号化目标 ID (保持不变，Attribute 是普通 SV 支持的)
    //==============================================================
    logic [TARGET_WIDTH-1:0] fv_target_id;

    //==============================================================
    // 3. 辅助逻辑 (保持不变)
    //==============================================================

    always_ff @(posedge clk) begin
        if (!rst_n) begin
        end else if (i_valid_1 && o_ready_1) begin
            fv_target_id <= fv_target_id;
        end
    end

    //==============================================================
    // 4. 数据捕获 (保持不变)
    //==============================================================
    logic [PSN_WIDTH-1:0] saved_psn;
    logic [   DWIDTH-1:0] saved_expected_data;
    logic                 saved_is_correct;
    logic                 target_valid;

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            target_valid <= 1'b0;
            saved_psn    <= '0;
            saved_expected_data <= '0;
            saved_is_correct <= 1'b0;
        end else if (i_valid_1 && o_ready_1 && (cnt_in == fv_target_id)) begin
            target_valid <= 1'b1;
            saved_psn    <= i_frame_psn;
            saved_is_correct <= frame_is_correct;
            if (frame_is_correct) saved_expected_data <= i_frame_data + i_frame_psn;
            else saved_expected_data <= 256'd0;
        end
    end

    //==============================================================
    // 5. 主接口验证 (IF2 & IF3) - 使用 Immediate Assertion
    //==============================================================
    wire check_trigger_main = (cnt_out_main == fv_target_id) && (tx_2_hs || tx_3_hs);

    always_ff @(posedge clk) begin
        if (rst_n) begin  // 对应 disable iff (!rst_n)
            if (check_trigger_main) begin
                // 1. 因果性检查 (Causality)
                // 原逻辑: check_trigger_main |-> target_valid
                o_main_no_spurious : assert (target_valid);

                // 2. 数据完整性检查 (Integrity)
                // 只有当 target_valid 为高时才检查数据，避免 X 态传播
                if (target_valid) begin
                    if (saved_is_correct) begin
                        // 正确帧分支：应该走 IF2
                        o_main_path_correct : assert (tx_2_hs);

                        o_main_data_correct : assert (o_frame_data_2 == saved_expected_data);

                        o_main_psn_correct : assert (o_frame_psn_2 == saved_psn);
                    end else begin
                        // 错误帧分支：应该走 IF3
                        o_main_path_error : assert (tx_3_hs);

                        o_main_data_error : assert (o_frame_data_3 == saved_expected_data);

                        o_main_psn_error : assert (o_frame_psn_3 == saved_psn);
                    end
                end
            end
        end
    end

    //==============================================================
    // 6. 汇报接口验证 (IF4) - 使用 Immediate Assertion
    //==============================================================
    wire check_trigger_rpt = (cnt_out_rpt == fv_target_id) && (o_valid_4 && i_ready_4);

    always @(posedge clk) begin
        if (rst_n) begin
            if (check_trigger_rpt) begin
                // 1. 因果性检查
                o_rpt_no_spurious : assert (target_valid);

                // 2. 数据检查
                if (target_valid) begin
                    o_rpt_psn_check : assert (o_frame_psn_4 == saved_psn);
                end
            end
        end
    end

    //==============================================================
    // 7. Liveness 替代方案：看门狗定时器 (Watchdog Timer)
    //    原理：如果不使用 s_eventually，必须定义一个"最大超时时间"
    //==============================================================
    // localparam TIMEOUT_LIMIT = 1000;  // 根据实际处理延时调整

    // integer watchdog_main;
    // integer watchdog_rpt;

    // // Main 接口活性检查
    // always_ff @(posedge clk) begin
    //     if (!rst_n) begin
    //         watchdog_main <= 0;
    //     end else begin
    //         // 如果目标已捕获，但主接口还没输出这个目标，则开始计时
    //         if (target_valid && (cnt_out_main <= fv_target_id)) begin
    //             watchdog_main <= watchdog_main + 1;
    //             // 检查超时
    //             o_main_timeout : assert (watchdog_main < TIMEOUT_LIMIT);
    //         end else begin
    //             // 正常输出后或等待捕获前，清零计数器
    //             watchdog_main <= 0;
    //         end
    //     end
    // end


endmodule
