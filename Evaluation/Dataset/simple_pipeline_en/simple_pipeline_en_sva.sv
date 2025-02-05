module simple_pipeline_en_sva  #(
    parameter int WIDTH=16,
    parameter int LATENCY=4
    )
   (
    input logic 	     clk,
    input logic 	     rst,
    input logic 	     en, 
    input logic [WIDTH-1:0]  in[8],
    input logic 	     valid_in,
    input logic [WIDTH-1:0] out,
    input logic 	     valid_out
    );

    default clocking cb @(posedge clk);
    endclocking
    default disable iff (rst);
      
   // In this example, we use a simpler function that returns the correct
   // output, instead of comparing with the correct output directly. When
   // there is a single output, this strategy is preferred, but when the
   // output is an array, you often need a function to verify all output values.
   function automatic logic [WIDTH-1:0] model(logic [WIDTH-1:0] in[8]);
      logic [WIDTH-1:0] sum = 0;
      for (int i=0; i < 4; i++) sum += in[i*2] * in[i*2+1];      
      return sum;     
   endfunction
   
   // This needs to include the enable now because the pipeline only advances 
   // when en is asserted.
   int count;    
   always_ff @(posedge clk or posedge rst)
     if (rst) count = 0;
     else if (en == 1'b1 && count < LATENCY) count ++;

   // We need to account for stalls, instead of just waiting for the latency.
   // Fortunately, the $past function can be enabled with a third paremeter,
   // for which we use our en signal.
   assert property(count == LATENCY |-> model($past(in, LATENCY, en)) == out);
   
   // Make sure the valid output is not asserted after reset until the pipeline
   // fills up.
   assert property (count < LATENCY |-> valid_out == '0);

   // Verify valid out after the pipeline is full.
   assert property (count == LATENCY |-> valid_out == $past(valid_in, LATENCY, en));
   
   // Make sure all pipeline stages are reset.
   assert property (count < LATENCY |-> out == '0);
      
endmodule
