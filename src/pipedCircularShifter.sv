`timescale 1ns / 1ps
// ==========================================================================
// Fully Pipelined Barrel Shifter
// Author: Ryan Bride
// Description: 
//      Generic Pipelined Circular Shifter Module, Circularly Shifts Right.
//      by default preforms Clog2(MAXZ) stages (1 stage per max shift val bit)
//      to achieve FMax after synthesis, however module can be changed
//      to combine N of those shifts per cycle. This is because various 
//      Platforms and use cases my have a variety of requirments and tradeoffs
//      i.e. you could choice to do more stages per cycle lowering Fmax because 
//      you have plentiful Bram to exploit and want to do a bunch in parallel
//      at the cost of decreased clock speed etc
// MAXZ: 
//      The Maximum Value should always be used for the Z, as the top module
//      incorperating this module has a step that Zero pads the input data
//      to support the use of multiple Z values. 
// ROTATES_PER_CYCLE:
//      The number of Rotates levels / Shifts per cycle
//      Default is once again 1, for FMax
// ==========================================================================\
module pipelinedCircularShifter #(     
    parameter int MAXZ                    = 81,
    parameter int ROTATES_PER_CYCLE       = 1 //Should throw an error on 0
)(
    input logic CLK,
    input logic rst_n,
    input logic valid_in,
    input logic [MAXZ-1:0] in_data,
    input logic [$clog2(MAXZ)-1:0] shift_val,
    output logic [MAXZ-1:0] out_data,
    output logic valid_out
);  
    localparam int NumMuxlevels             = $clog2(MAXZ);
    localparam int ShiftsPerPipelineLevel   = ROTATES_PER_CYCLE;
    localparam int NumStages                = (NumMuxlevels % ShiftsPerPipelineLevel  != 0) ?
                                              ((NumMuxlevels / ShiftsPerPipelineLevel) +1 )  :
                                              (NumMuxlevels / ShiftsPerPipelineLevel);

    logic [MAXZ-1:0] stage_regs [0:NumStages];  
    logic [NumStages:0] valid_pipe;
    //stage[0] is the currently most recently streamed in data so load it in
    assign stage_regs[0] = in_data;
        
    genvar i, qq;
    generate
        for(i=0; i<NumStages; i++) begin : PipelineStage
            //Wire array for each substep output
            wire [MAXZ-1:0] stage_wires [0:ShiftsPerPipelineLevel];
            
            //Input the current value stored in the regs into the wire net
            assign stage_wires[0] = stage_regs[i];

            for(qq=0; qq<ShiftsPerPipelineLevel; qq++) begin : RotStagePerPipe
                localparam int idx = i*ShiftsPerPipelineLevel+qq;
                localparam logic realityCheck = (idx <= NumMuxlevels) ? ( 1'b1 ) : ( 1'b0 );   
                localparam int s_idx = (idx >= $clog2(MAXZ)) ? $clog2(MAXZ)-1 : idx;

                rotateStage #(
                    .MAXZ( MAXZ ),
                    .SHIFT( idx ),   
                    .DOES_EXIST( realityCheck ) //Don't actually create it the mux stuff if you don't need to
                ) rot_inst (
                    .i_data(stage_wires[qq]),
                    .o_data(stage_wires[qq+1]),
                    .en_en(shift_val[s_idx])
                );
            end : RotStagePerPipe        
                    
            //After all the stage logic, place the outputs of each stage into the register 
            always_ff @(posedge CLK) begin
                if(!rst_n)
                    stage_regs[i+1] <= '0;
                else
                    stage_regs[i+1] <= stage_wires[ShiftsPerPipelineLevel];
            end
        end
    endgenerate

    assign out_data = stage_regs[NumStages];

    always_ff @(posedge CLK) begin
        if (!rst_n)
            valid_pipe <= '0;
        else begin
            valid_pipe[0] <= valid_in;
            for (int i = 1; i <= NumStages; i++)
                valid_pipe[i] <= valid_pipe[i-1];
        end
    end

    assign valid_out = valid_pipe[NumStages];

endmodule
// -------------------------------------------------------------------------    
// Module to encapsulate the Rotation and generate a circuit only if the 
// Rotation is needed to remove uncessary rotation stages generation that exist 
// When MaxZ % ROTATES_PER_CYCLE =/= 
// -------------------------------------------------------------------------   
module rotateStage #(
    parameter int   MAXZ        = 81,
    parameter int   SHIFT       = 1,
    parameter logic DOES_EXIST  = 1     //1 if it exist 0 if it does not    
)(      
    input logic [MAXZ-1:0]  i_data, 
    input logic en_en,      //Couldn't decide on en_ or _en now its a face!!! :)        
    output logic [MAXZ-1:0] o_data
);
    localparam int clamped_shift =  
                (( 1<<SHIFT ) > (1<<$clog2(MAXZ)) ) ? $clog2(MAXZ) : SHIFT;
    localparam int sh_val_mod = (1 << SHIFT) % MAXZ;
    localparam logic o_o = (!DOES_EXIST || sh_val_mod == 0 );
    

    generate
        case(o_o) 
            1'b1 : 
                assign o_data = i_data;
            1'b0 : begin
                always_comb begin
                    if(en_en)
                        o_data = {  i_data[sh_val_mod-1:0], i_data[MAXZ-1:sh_val_mod] };
                    else 
                        o_data = i_data;
                end
            end
        endcase  
    endgenerate
endmodule

// ==========================================================================    
// Original Simplistic Pipeline Rotator
// No support for changing from doing one stage per Clog2(MAXZ)
// You can utilize this instead of the above if you want, it is tested & works
// ==========================================================================\   
module pipelinedCircularShifterFMAX #(
    parameter int MAXZ  = 81
)(
    input logic CLK,
    input logic rst_n,
    input logic valid_in,
    input logic [MAXZ-1:0] in_data,
    input logic [$clog2(MAXZ)-1:0] shift_val,
    output logic [MAXZ-1:0] out_data,
    output logic valid_out
);
    
    localparam int NumStages = $clog2(MAXZ);
    
    logic [NumStages:0] valid_pipe;
    //pipeline stages, stage[0] is the currently most recently streamed in data
    logic [MAXZ-1:0] stage [0:NumStages];  
    assign stage[0] = in_data;

    genvar i;
    generate
        for (i=0; i < NumStages; i++) begin : CircularShifterStage
            logic [MAXZ-1:0] rotated;   

            always_comb begin
                if(shift_val[i]) 
                    rotated = {stage[i][(1<<i)-1:0], stage[i][MAXZ-1:(1<<i)]};

                else
                    rotated = stage[i];
            end

            //pipeline Registers 
            always_ff @(posedge CLK) begin
                if(!rst_n)
                    stage[i+1] <= '0;
                else
                    stage[i+1] <= rotated;
            end
        end
    endgenerate
    
    always_ff @(posedge CLK) begin
        if (!rst_n)
            valid_pipe <= '0;
        else begin
            valid_pipe[0] <= valid_in;
            for (int i = 1; i <= NumStages; i++)
                valid_pipe[i] <= valid_pipe[i-1];
        end
    end

    assign out_data = stage[NumStages];

    assign valid_out = valid_pipe[NumStages];

endmodule
