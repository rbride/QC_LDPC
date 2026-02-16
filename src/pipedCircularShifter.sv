`timescale 1ns / 1ps
// ==========================================================================
// Fully Pipelined Barrel Shifter
// Author: Ryan Bride
// Description: 
//      Generic Pipelined Circular Shifter Module, Shifts right
//      and contains Clog2(MAXZ) stages (1 stage per max shift val bit),
//      The Module can be changed to do X shifts per cycle
// MAXZ: 
//      The Maximum Value should always be used for the Z, as the logic
//      incorperating this module has a step that Zero pads the input data
//
// PIPE_STAGES_PER_CYCLE:
//      As the name suggest, the number of pipeline stages per cycle
//      That the module is aiming to achieve
// ==========================================================================
module pipelinedCircularShifter2 #(
    parameter int MAXZ  = 81
)(
    input logic CLK,
    input logic rst_n,
    input logic [MAXZ-1:0] in_data,
    input logic [$clog2(MAXZ)-1:0] shift_val,
    output logic [MAXZ-1:0] out_data
);

    localparam int NumStages = $clog2(MAXZ);
    
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
    
    assign out_data = stage[NumStages];

endmodule

module pipelinedCircularShifter1 #(     
    parameter int MAXZ                    = 81,
    parameter int PIPE_STAGES_PER_CYCLE   = 1
)(
    input logic CLK,
    input logic rst_n,
    input logic [MAXZ-1:0] in_data,
    input logic [$clog2(MAXZ)-1:0] shift_val,
    output logic [MAXZ-1:0] out_data
);  

    localparam int NumMuxlevels             = $clog2(MAXZ);
    localparam int StagesPerPipelineLevel   = PIPE_STAGES_PER_CYCLE;
    localparam int NumStages                = (NumMuxlevels % StagesPerPipelineLevel  != 0) ?
                                              ((NumMuxlevels / StagesPerPipelineLevel) +1 )  :
                                              (NumMuxlevels / StagesPerPipelineLevel);

    logic [MAXZ-1:0] stage_regs [0:NumStages];  
    //stage[0] is the currently most recently streamed in data so load it in
    assign stage_regs[0] = in_data;
        
    genvar i, qq;
    generate
        for(i=0; i<NumStages; i++) begin : PipelineStage
            

            
            assign rotated = tmpwires[StagesPerPipelineLevel*(i+1)];
            
            always_ff @(posedge CLK) begin
                if(!rst_n)
                    stage_regs[i+1] <= '0;
                else
                    stage_regs[i+1] <= rotated;
            end


        end
    endgenerate

    assign out_data = stage_regs[NumStages];

endmodule

//To work around verilog/system verilog limitations that are causing issues with generate functions
//simulation, and Synthesis, that is tool dependent, the individual rotation stage is moved out into its own module
module rotateStage #(
    parameter int MAXZ      = 81,
    parameter int SHIFT     = 1
)(
    input logic [MAXZ-1:0]  i_data, 
    input logic en_en,      //Couldn't decide on en_ or _en now its a face!!! :)        
    output logic [MAXZ-1:0] o_data
);
    
    assign o_data = ( en_en ) ? 
            ( { i_data[ (1<<SHIFT)-1:0 ], i_data[ MAXZ-1:(1<<SHIFT) ] } ) :
            ( i_data ) ; 

endmodule


// // //Shift the amount of times needed for this stage. 
//             for(qq=0; qq<StagesPerPipelineLevel; qq++) begin : NumMuxlevels
//                 localparam int idx = i*StagesPerPipelineLevel+qq;
//                 if( idx < NumStages) begin
//                     assign tmpwires[qq+1] = shift_val[idx] ?
//                         {tmpwires[qq][(1<<idx)-1:0], tmpwires[qq][MAXZ-1:(1<<idx)]}  :
//                         tmpwires[qq];
                
//                 end else begin
//                     assign tmpwires[qq+1] = tmpwires[qq];                    
//                 end
//             end