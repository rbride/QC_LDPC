`timescale 1ns/1ps
// =============================================================================
// Author: Ryan Bride
// File:   qcldpc_driver.sv
// Desc:   Testbench driver — generates stimulus for DUT inputs
//         Handles valid/ready handshake and drives one info block per cycle
//         Supports gap injection to stress back-pressure handling
// =============================================================================
module qcldpc_driver (
    input  logic    CLK,
    input  logic    rst_n,
    input  logic    in_ready,
    output logic    in_valid,
    output logic    in_last,
    output z_req_t  req_z,
    output logic [qcldpc_tb_pkg::TB_MAXZ-1:0] i_data
);
    import qcldpcPkg::*;
    import qcldpc_tb_pkg::*;

    // Idle defaults
    initial begin
        in_valid = 1'b0;  in_last = 1'b0;  req_z = Z_81; i_data = '0;
    end

    // -------------------------------------------------------------------------
    // Drives a complete codeword one block per cycle
    // Waits for in_ready before asserting valid
    // Correctly handles back-pressure from DUT
    // -------------------------------------------------------------------------
    task automatic drive_codeword(input test_vector_t tv);
        automatic logic [TB_MAXZ-1:0] block;
        req_z = tv.z_sel;

        for(int blk = 0; blk < TB_IBLKS_NUM; blk++) begin
            block = tv.info_bits[blk*TB_MAXZ +: TB_MAXZ];

            // Wait for DUT to be ready
            @(posedge CLK);
            while(!in_ready) @(posedge CLK);

            in_valid = 1'b1;
            in_last  = (blk == TB_IBLKS_NUM - 1);
            i_data   = block;

            @(posedge CLK);
        end

        // Deassert after last block
        in_valid = 1'b0;
        in_last  = 1'b0;
        i_data   = '0;
    endtask

    // -------------------------------------------------------------------------
    // Same as drive_codeword but randomly injects idle cycles between blocks
    // gap_probability: 0-100, percentage chance of injecting an idle cycle
    // Tests that DUT handles non-continuous input correctly
    // -------------------------------------------------------------------------
    task automatic drive_codeword_with_gaps(
        input test_vector_t tv,
        input int           gap_probability
    );
        automatic logic [TB_MAXZ-1:0] block;
        req_z = tv.z_sel;

        for(int blk = 0; blk < TB_IBLKS_NUM; blk++) begin
            // Randomly inject idle cycles before this block
            if($urandom_range(0, 99) < gap_probability) begin
                in_valid = 1'b0;
                repeat($urandom_range(1, 5)) @(posedge CLK);
            end

            block = tv.info_bits[blk*TB_MAXZ +: TB_MAXZ];

            @(posedge CLK);
            while(!in_ready) @(posedge CLK);

            in_valid = 1'b1;
            in_last  = (blk == TB_IBLKS_NUM - 1);
            i_data   = block;

            @(posedge CLK);
        end

        in_valid = 1'b0;
        in_last  = 1'b0;
        i_data   = '0;
    endtask

    // -------------------------------------------------------------------------
    // drive_reset_mid_codeword
    // Drives N blocks then asserts reset — tests recovery behavior
    // -------------------------------------------------------------------------
    task automatic drive_reset_mid_codeword(
        input int   blocks_before_reset,
        output logic rst_n_out
    );
        req_z    = Z_81;
        in_valid = 1'b1;
        i_data   = $urandom();

        repeat(blocks_before_reset) @(posedge CLK);

        // Caller controls rst_n — signal it via output
        rst_n_out = 1'b0;
        @(posedge CLK);
        in_valid = 1'b0;
        i_data   = '0;
    endtask

endmodule
