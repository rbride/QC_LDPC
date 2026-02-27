`timescale 1ns / 1ps
package qcldpcPkg;

    parameter int MAXZ       = 81;
    parameter int NUM_SUP_Z  = 3;

    typedef struct packed {
        logic                     valid;
        logic                     last;
        logic [MAXZ-1:0]          data;
        logic [$clog2(MAXZ)-1:0]  svals; 
    } pipeline_pkt_t;

    typedef enum logic [2:0] {
        Z_27 = 3'b001,  // Z of 81
        Z_54 = 3'b010,  // Z of 54
        Z_81 = 3'b100   // Z of 27
    } z_req_t;

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

