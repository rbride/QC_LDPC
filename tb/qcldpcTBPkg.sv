`timescale 1ns/1ps
// =============================================================================
// Author: Ryan Bride
// File:   qcldpc_tb_pkg.sv
// Desc:   Testbench package — shared types, structs, and constants
//         used across all testbench components
// =============================================================================
package qcldpc_tb_pkg;

    import qcldpcPkg::*;
    localparam int TB_MAXZ      = 81;
    localparam int TB_NUM_PBLKS = 4;
    localparam int TB_IBLKS_NUM = 20;
    localparam int TB_NUM_SUP_Z = 3;

    // -1 = zero block (sentinel)
    localparam int H_Z81 [0:3][0:23] = '{
        '{57, -1, -1, -1, 50, -1, 11, -1, 50, -1, 79, -1,  1,  0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1},
        '{-1, 3,  -1, 28, -1,  0, -1, 55, -1, 7,  -1, 30, -1, 24,  0, -1, -1, -1, -1, -1, -1, -1, -1, -1},
        '{-1, -1, 30, -1, -1, 24, -1, -1, 45, -1, -1, 13, -1, -1, 75,  0, -1, -1, -1, -1, -1, -1, -1, -1},
        '{-1, -1, -1, 64, -1, -1, -1, -1, -1, -1, -1, -1, 63, -1, -1, -1,  0, -1, -1, -1, -1, -1, -1, -1}
    };

    // 802.11n proto matrix for Z=54, rate 5/6
    localparam int H_Z54 [0:3][0:23] = '{
        '{39, -1, -1, -1, 31, -1,  28, -1, -1, -1,  0, -1,  1,  0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1},
        '{-1, 36, -1, -1, -1, 34, -1,  35, -1, 27, -1, 30, -1, 25,  0, -1, -1, -1, -1, -1, -1, -1, -1, -1},
        '{-1, -1, 19, -1, -1, -1, -1,  -1, 11, -1,  7, -1, -1, -1, 45,  0, -1, -1, -1, -1, -1, -1, -1, -1},
        '{-1, -1, -1, 46, -1, -1, -1,  -1, -1, -1, -1, -1,  5, -1, -1, -1,  0, -1, -1, -1, -1, -1, -1, -1}
    };

    // 802.11n proto matrix for Z=27, rate 5/6
    localparam int H_Z27 [0:3][0:23] = '{
        '{16, -1, -1, -1, 12, -1, 14, -1,  0, -1,  1, -1,  1,  0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1},
        '{-1, 17, -1, -1, -1, 17, -1,  7, -1, 1,  -1, 15, -1,  5,  0, -1, -1, -1, -1, -1, -1, -1, -1, -1},
        '{-1, -1, 13, -1, -1, -1, -1,  -1, 4,  -1,  8, -1, -1, -1, 21,  0, -1, -1, -1, -1, -1, -1, -1, -1},
        '{-1, -1, -1, 24, -1, -1, -1,  -1, -1, -1, -1, -1, 16, -1, -1, -1,  0, -1, -1, -1, -1, -1, -1, -1}
    };

    // -------------------------------------------------------------------------
    // Test vector type — one complete codeword
    // -------------------------------------------------------------------------
    typedef struct {
        logic [TB_MAXZ*TB_IBLKS_NUM-1:0]  info_bits;
        logic [TB_MAXZ*TB_NUM_PBLKS-1:0]  parity_expected;
        z_req_t                            z_sel;
        int                                test_id;
    } test_vector_t;

    // -------------------------------------------------------------------------
    // DUT result type — captured from monitor
    // -------------------------------------------------------------------------
    typedef struct {
        logic [TB_MAXZ*TB_NUM_PBLKS-1:0]  parity_actual;
        z_req_t                            z_sel;
        int                                test_id;
        int                                cycle_count;
    } dut_result_t;

    // -------------------------------------------------------------------------
    // Scoreboard statistics
    // -------------------------------------------------------------------------
    typedef struct {
        int unsigned tests_run;
        int unsigned tests_passed;
        int unsigned tests_failed;
        int unsigned latency_min;
        int unsigned latency_max;
        real         latency_avg;
    } test_stats_t;

    // -------------------------------------------------------------------------
    // Reference model functions
    // Circular left shift of Z-bit vector by s positions
    // -------------------------------------------------------------------------
    function automatic logic [TB_MAXZ-1:0] circ_shift_ref(
        input logic [TB_MAXZ-1:0] vec,
        input int                  s,
        input int                  Z
    );
        automatic logic [TB_MAXZ-1:0] result = '0;
        for(int i = 0; i < Z; i++)
            result[i] = vec[(i + s) % Z];
        return result;
    endfunction

    // Look up proto matrix shift value for given Z, row, col
    // Returns -1 for zero block
    function automatic int get_proto_val(
        input z_req_t z_sel,
        input int     row,
        input int     col
    );
        case(z_sel)
            Z_27: return H_Z27[row][col];
            Z_54: return H_Z54[row][col];
            Z_81: return H_Z81[row][col];
            default: return -1;
        endcase
    endfunction

    // Compute expected parity for given info bits and Z
    // Implements QC-LDPC systematic encoding with back-substitution
    function automatic logic [TB_MAXZ*TB_NUM_PBLKS-1:0] compute_reference(
        input logic [TB_MAXZ*TB_IBLKS_NUM-1:0] info_bits,
        input z_req_t                            z_sel
    );
        automatic logic [TB_MAXZ-1:0] info_blocks   [0:TB_IBLKS_NUM-1];
        automatic logic [TB_MAXZ-1:0] parity_blocks [0:TB_NUM_PBLKS-1];
        automatic logic [TB_MAXZ*TB_NUM_PBLKS-1:0] result;
        automatic int Z;
        automatic int shift;

        case(z_sel)
            Z_27: Z = 27;
            Z_54: Z = 54;
            Z_81: Z = 81;
            default: Z = 81;
        endcase

        // Unpack info bits into Z-wide blocks
        for(int b = 0; b < TB_IBLKS_NUM; b++)
            info_blocks[b] = info_bits[b*TB_MAXZ +: TB_MAXZ];

        // Clear parity blocks
        for(int p = 0; p < TB_NUM_PBLKS; p++)
            parity_blocks[p] = '0;

        // Accumulate info contribution into each parity row
        for(int p = 0; p < TB_NUM_PBLKS; p++) begin
            for(int b = 0; b < TB_IBLKS_NUM; b++) begin
                shift = get_proto_val(z_sel, p, b);
                if(shift != -1)
                    parity_blocks[p] ^= circ_shift_ref(info_blocks[b], shift, Z);
            end
        end

        // Back-substitution through parity columns (dual diagonal structure)
        for(int p = 1; p < TB_NUM_PBLKS; p++) begin
            shift = get_proto_val(z_sel, p, TB_IBLKS_NUM + p - 1);
            if(shift != -1)
                parity_blocks[p] ^= circ_shift_ref(parity_blocks[p-1], shift, Z);
        end

        // Pack parity blocks into result
        for(int p = 0; p < TB_NUM_PBLKS; p++)
            result[p*TB_MAXZ +: TB_MAXZ] = parity_blocks[p];

        return result;
    endfunction

endpackage
