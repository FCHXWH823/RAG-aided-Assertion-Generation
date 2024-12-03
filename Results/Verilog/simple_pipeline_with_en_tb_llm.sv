module simple_pipeline_with_en_tb_llm;

   localparam int NUM_TESTS = 10000;
   localparam int WIDTH = 8;
   localparam int LATENCY = 3; // Assuming some latency value for the pipeline, adjust as necessary.
      
   logic          clk, rst, en, valid_in, valid_out;
   logic [WIDTH-1:0] in[8];
   logic [WIDTH-1:0] out;
    
   simple_pipeline_with_en #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while (1) #5 clk = ~clk;      
   end

   initial begin
      $timeformat(-9, 0, " ns");

      rst <= 1'b1;
      en <= 1'b0;      
      valid_in <= 1'b0;
      for (int i=0; i < 8; i++) in[i] <= '0;
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;
      @(posedge clk);
 
      for (int i=0; i < NUM_TESTS; i++) begin
         en <= $random;  
         for (int i=0; i < 8; i++) in[i] <= $random;
         valid_in <= $random;    
         @(posedge clk);
      end

      $display("Tests completed.");      
      disable generate_clock;
   end

   // Assertions
   // Assertion 1: Check output matches expected value after defined latency
   assert property (@(posedge clk) disable iff(rst) 
                   (en == 1'b1) |-> (out == expected_value(in, $past(in), LATENCY))
                   ) 
   else $error("Output does not match expected value after latency!");

   // Assertion 2: Check valid_out does not go high prematurely
   assert property (@(posedge clk) disable iff(rst)
                   (valid_out == 1'b0) throughout (LATENCY)
                   )
   else $error("valid_out went high before LATENCY cycles!");

   // Assertion 3: Check valid_out matches valid_in from LATENCY cycles ago
   assert property (@(posedge clk) disable iff(rst)
                   (valid_out == $past(valid_in, LATENCY))
                   )
   else $error("valid_out does not match valid_in from LATENCY cycles ago!");

   // Assertion 4: Check output remains zero until LATENCY clocks have passed
   assert property (@(posedge clk) disable iff(rst)
                   (out == '0) throughout (LATENCY)
                   )
   else $error("Output is not zero until LATENCY cycles have passed!");

   // Function to calculate expected value (for Assertion 1)
   function automatic logic [WIDTH-1:0] expected_value(
       input logic [WIDTH-1:0] in, 
       input logic [WIDTH-1:0] last_in[V],
       input int latency);
       // Define how to compute expected value based on the pipeline's behavior
       // This should be replaced with the actual logic according to DUT functionality
       return last_in[latency]; // Example function logic
   endfunction

endmodule