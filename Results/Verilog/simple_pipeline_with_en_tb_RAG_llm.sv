module simple_pipeline_with_en_tb_RAG_llm;

   localparam int NUM_TESTS = 10000;
   localparam int WIDTH = 8;
   localparam int LATENCY = DUT.LATENCY; // Assuming DUT.LATENCY is defined in the DUT

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

   // Assertion 1: Check output matches expected value after latency when rst is 0
   assert property ( 
      !rst |-> ( ((out == model_function(in[$past(clk, LATENCY)])) && (en)) throughout (DUT.LATENCY) )
   );

   // Assertion 2: Check valid_out remains low until DUT.LATENCY clocks have gone when rst is 0
   assert property ( 
      !rst |-> (valid_out == 1'b0 throughout (DUT.LATENCY) )
   );

   // Assertion 3: Check valid_out matches valid_in from DUT.LATENCY cycles ago, when en is high
   assert property ( 
      !rst |-> (valid_out == $past(valid_in, LATENCY) when (en))
   );

   // Assertion 4: Check out remains zero until DUT.LATENCY clocks have gone when rst is 0
   assert property ( 
      !rst |-> (out == 0 throughout (DUT.LATENCY) )
   );

endmodule