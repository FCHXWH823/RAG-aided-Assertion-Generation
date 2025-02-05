// Greg Stitt
// University of Florida
//
// This testbench illustrates how to create a testbench for a simple pipeline
// without an enable. It also demonstrates subtle timing differences when 
// functions are used within assertion properties.
//
// TODO: Change the commented out assertion properties to test each version. 

`timescale 1 ns / 100 ps

module simple_pipeline_sva   #(
    parameter int WIDTH=16,
    parameter int LATENCY=4
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic [WIDTH-1:0]  in[8],
    input logic 	     valid_in,
    input logic [WIDTH-1:0] out,
    input logic 	     valid_out
    );

    default clocking cb @(posedge clk);
    endclocking
    default disable iff (rst);
      

   function automatic logic is_out_correct1(logic [WIDTH-1:0] in[8]);      
     logic [WIDTH-1:0] sum = 0;
      
      for (int i=0; i < 4; i++) begin
         sum += in[i*2] * in[i*2+1];     
      end
      
      return sum == out;      
   endfunction
   
   // To solve the problem with the previous function, we simply add a parameter
   // to the function that takes the output from the assertion property, which
   // ensures that the output has not been changed yet after the clock edge.
   function automatic logic is_out_correct2(logic [WIDTH-1:0] in[8], logic [WIDTH-1:0] out);
      logic [WIDTH-1:0] sum = 0;
      
      for (int i=0; i < 4; i++) begin
         sum += in[i*2] * in[i*2+1];     
      end
      
      return sum == out;      
   endfunction
   
   int count;    
   always_ff @(posedge clk or posedge rst)
     if (rst) count = 0;
     else if (count < LATENCY) count ++;
      
   // Make sure the valid output is not asserted after reset until the pipeline
   // fills up.
   assert property (count < LATENCY |-> valid_out == 1'b0);

   // Make sure valid out is asserted correctly after the pipeline is full.
   assert property (count == LATENCY |-> valid_out == $past(valid_in, LATENCY));
   
      
endmodule
