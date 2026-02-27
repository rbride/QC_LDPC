`timescale 1ns / 1ps
package qcldpcPkg;

    parameter int MAXZ       = 81;
    parameter int NUM_SUP_Z  = 3;

    typedef struct packed {
        logic               valid;
        logic               last;
        logic [MAXZ-1:0]    data;
    } pipeline_pkt_t;

    // --------------------------------------
    // Used to Determine if 54 is present
    // will only ever be 1 or 0
    // --------------------------------------
    function automatic int unsigned detr_nonfactor_z(
        input int unsigned maxz,
        input int unsigned z_values [],  
        input int unsigned num_z
    );
        automatic int unsigned count = 0;
        for (int i = 0; i < num_z; i++) begin
            if (maxz % z_values[i] != 0)
                count++;
        end
        return count;
    endfunction

    // --------------------------------------
    // Bitmask Return telling me where Z val
    // is inside the Request Z Array 
    // --------------------------------------
    function automatic int unsigned nonfactor_z_mask(
        input int unsigned maxz,
        input int unsigned z_values [],
        input int unsigned num_z
    );
        automatic int unsigned spot_in_array = 0;
        for (int i = 0; i < num_z; i++) begin
            if (maxz % z_values[i] != 0)
                spot_in_array = i;
        end
        return spot_in_array;
    endfunction

endpackage


// // One processed signal per Z — generated statically
// logic [MAXZ-1:0] i_data_tiled [0:NUM_SUPPORTED_Z-1];

// // This generate unrolls at elaboration into NUM_SUPPORTED_Z
// // independent constant assignments — zero runtime logic
// genvar zi;
// generate
//     for (zi = 0; zi < NUM_SUPPORTED_Z; zi++) begin : TILE_GEN

//         // Each iteration is a constant expression at elaboration
//         // tools see this as hardwired bit connections, not logic
//         // equivalent to writing each case manually
//         always_comb begin
//             i_data_tiled[zi] = get_tiled_input(i_data, Z_VALUE_ARRAY[zi], MAXZ);
//         end

//     end
// endgenerate

// // Final mux — one register, select driven by req_z one-hot
// // synthesizes to exactly the same mux you have now
// // but the inputs are pre-computed wiring not runtime logic
// always_ff @(posedge CLK) begin
//     if (!rst_n) begin
//         i_data_processed <= '0;
//     end else begin
//         i_data_processed <= '0;
//         for (int i = 0; i < NUM_SUPPORTED_Z; i++) begin
//             if (req_z[i])
//                 i_data_processed <= i_data_tiled[i];
//         end
//     end
// end
// ```

// The synthesized result for your 27/54/81 config:
// ```
// TILE_GEN[0]:  i_data_tiled[0] = {i_data[26:0], i_data[26:0], i_data[26:0]}  — pure wiring
// TILE_GEN[1]:  i_data_tiled[1] = {27'b0, i_data[53:0]}                        — pure wiring
// TILE_GEN[2]:  i_data_tiled[2] = i_data[80:0]                                 — pure wiring

// Final mux:    req_z[0] ? i_data_tiled[0] :
//               req_z[1] ? i_data_tiled[1] :
//               req_z[2] ? i_data_tiled[2] :
//               '0



    

// endpackage

// module QCLDPCEncoderController #(
//     parameter int MAXZ              = `MAXZ,
//     parameter int NUM_SUPPORTED_Z   = `NUM_SUPPORTED_Z,
//     parameter int Z_VALUE_ARRAY [0:2] = '{27, 54, 81}
// )(
//     ...
// );
//     // Call functions with module parameters to get derived info
//     localparam int NUM_NONFACTOR    = count_nonfactor_z(MAXZ, Z_VALUE_ARRAY, NUM_SUPPORTED_Z);
//     localparam int NONFACTOR_MASK   = nonfactor_z_mask(MAXZ, Z_VALUE_ARRAY, NUM_SUPPORTED_Z);
//     localparam logic ALL_FACTOR     = all_z_factor(MAXZ, Z_VALUE_ARRAY, NUM_SUPPORTED_Z);

//     // Elaboration time reporting — visible in synthesis and sim logs
//     initial begin
//         $display("MAXZ = %0d", MAXZ);
//         $display("NUM_NONFACTOR = %0d", NUM_NONFACTOR);
//         $display("NONFACTOR_MASK = %0b", NONFACTOR_MASK);

//         // Per-Z breakdown
//         for (int i = 0; i < NUM_SUPPORTED_Z; i++) begin
//             if (NONFACTOR_MASK & (1 << i))
//                 $display("  Z[%0d] = %0d is NON-FACTOR of MAXZ=%0d — requires dedicated shifter",
//                          i, Z_VALUE_ARRAY[i], MAXZ);
//             else
//                 $display("  Z[%0d] = %0d divides evenly into MAXZ=%0d — tiling valid",
//                          i, Z_VALUE_ARRAY[i], MAXZ);
//         end

//         // Fatal if config is unsupported
//         if (NUM_NONFACTOR > 1)
//             $fatal(1, "CONFIG ERROR: %0d non-factor Z values detected. \
//                        Maximum supported is 1 (Z=54). \
//                        Adjust Z_VALUE_ARRAY or MAXZ.", NUM_NONFACTOR);
//     end

// endmodule



// module pipelinedCircularShifterFMAX
//     import qcldpc_pkg::*;
// #(
//     parameter int INST_MAXZ = 81
// )(
//     input  logic          CLK,
//     input  logic          rst_n,
//     input  pipeline_pkt_t pkt_in,
//     output pipeline_pkt_t pkt_out
// );
//     localparam int NumStages = $clog2(INST_MAXZ);

//     // Array of packet structs — one per stage
//     // valid, last, shift_val all travel with the data automatically
//     pipeline_pkt_t stage [0:NumStages];

//     // Stage 0 loaded from input
//     always_comb begin
//         stage[0].valid     = pkt_in.valid;
//         stage[0].last      = pkt_in.last;
//         stage[0].shift_val = pkt_in.shift_val;
//         stage[0].data      = pkt_in.data;
//     end

//     genvar i;
//     generate
//         for (i = 0; i < NumStages; i++) begin : ShifterStage
//             pipeline_pkt_t rotated;

//             always_comb begin
//                 // valid, last, shift_val pass through every stage untouched
//                 rotated          = stage[i];  // copy whole struct first

//                 // then overwrite only the data field with rotated version
//                 if (stage[i].shift_val[i])
//                     rotated.data = {
//                         stage[i].data[(1<<i)-1:0],
//                         stage[i].data[INST_MAXZ-1:(1<<i)]
//                     };
//                 // else data already copied correctly by struct assign above
//             end

//             always_ff @(posedge CLK) begin
//                 if (!rst_n)
//                     stage[i+1] <= '0;
//                 else
//                     stage[i+1] <= rotated;
//             end
//         end
//     endgenerate

//     assign pkt_out = stage[NumStages];

// endmodule



    // // --------------------------------------
    // // Bitmask Return telling me where Z val
    // // is inside the Request Z Array 
    // // --------------------------------------
    // function automatic logic [NUM_SUP_Z-1:0] nonfactor_z_mask(
    //     input int unsigned maxz,
    //     input int unsigned z_values [],
    //     input int unsigned num_z
    // );
    //     logic [NUM_SUP_Z-1:0] mask = '0;
    //     for (int i = 0; i < num_z; i++) begin
    //         if (maxz % z_values[i] != 0)
    //             mask[i] = 1'b1;
    //     end
    //     return mask;
    // endfunction


    //  // --------------------------------------
    // // Process Data Input
    // // --------------------------------------
    // function automatic logic [MAXZ-1:0] procDataInput #(
    //     parameter int z_val,
    //     parameter int maxz
    // )(
    //     input logic [MAXZ-1:0]  raw_data,
    // );
    //     automatic logic [MAXZ-1:0] result = '0;
    //     if (maxz % z_val == 0) begin
    //         // Factor — tile
    //         for (int t = 0; t < maxz / z_val; t++)
    //             result[t*z_val +: z_val] = raw_data[z_val-1:0];
    //     end
    //      else begin
    //         // Non-factor — zero pad
    //         result[z_val-1:0] = raw_data[z_val-1:0];
    //     end
    //     return result;
    // endfunction
