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
    parameter int PIPE_STAGES_PER_CYCLE   = 1 //Should throw an error on 0
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
            
            //Wire array for each substep output
            wire [MAXZ-1:0] stage_wires [0:StagesPerPipelineLevel];

            //Input the current value stored in the regs into the wire net
            assign stage_wires[0] = stage_regs[i];

            for(qq=0; qq<StagesPerPipelineLevel; qq++) begin : RotStagePerPipe
                localparam int idx = i*StagesPerPipelineLevel+qq;
                localparam logic realityCheck = (idx <= NumMuxlevels) ? ( 1'b1 ) : ( 1'b0 ); 
        
                rotateStage #(
                    .MAXZ( MAXZ ),
                    .SHIFT( idx ),
                    .DOES_EXIST( realityCheck ) //Don't actually create it the mux stuff if you don't need to
                ) rot_inst (
                    .i_data(stage_wires[qq]),
                    .o_data(stage_wires[qq+1]),
                    .en_en(shift_val[idx])
                );
            end : RotStagePerPipe        
                    
            //After all the stage logic, place the outputs of each stage into the register 
            always_ff @(posedge CLK) begin
                    if(!rst_n)
                        stage_regs[i+1] <= '0;
                    else
                        stage_regs[i+1] <= stage_wires[StagesPerPipelineLevel];;
            end
        end
    endgenerate

    assign out_data = stage_regs[NumStages];

endmodule

//To work around verilog/system verilog limitations that are causing issues with generate functions
//simulation, and Synthesis, that is tool dependent, the individual rotation stage is moved out into its own module
module rotateStage #(
    parameter int MAXZ          = 81,
    parameter int SHIFT         = 1,
    parameter logic DOES_EXIST    = 1         //Chat am I cooking? 
)(
    input logic [MAXZ-1:0]  i_data, 
    input logic en_en,      //Couldn't decide on en_ or _en now its a face!!! :)        
    output logic [MAXZ-1:0] o_data
);
    genvar o_o;
    generate
        if(DOES_EXIST) begin
            assign o_data = ( en_en ) ? 
                ( { i_data[ (1<<SHIFT)-1:0 ], i_data[ MAXZ-1:(1<<SHIFT) ] } ) :
                //stage[i][(1<<i)-1:0], stage[i][MAXZ-1:(1<<i)]
                ( i_data ) ; 
        end else begin
            assign o_data = i_data;
        end
    endgenerate

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