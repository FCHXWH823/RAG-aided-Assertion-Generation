module simple_pipeline_tb_llm;

   localparam int NUM_TESTS = 1000;
   localparam int WIDTH = 8;
   localparam int LATENCY = 4; // Example latency; you should replace it with the actual latency of your pipeline

   logic          clk, rst, valid_in, valid_out;
   logic [WIDTH-1:0] in[8];
   logic [WIDTH-1:0] out;

   simple_pipeline #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while (1) #5 clk = ~clk;      
   end

   initial begin
      $timeformat(-9, 0, " ns");

      rst <= 1'b1;
      valid_in <= 1'b0;
      for (int i=0; i < 8; i++) in[i] <= '0;
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;
      @(posedge clk);

      for (int i=0; i < NUM_TESTS; i++) begin
         for (int j=0; j < 8; j++) in[j] = $random;
         valid_in <= $random;
         @(posedge clk);
      end

      $display("Tests completed.");      
      disable generate_clock;
   end

   // Assertion 1: Check that after reset, output matches input from LATENCY cycles ago
   assert property ( 
      @(posedge clk)
      (rst == 0) |=> (out == in[valid_in] /* Replace with correct input index */)
      ## LATENCY 
      (valid_in != 0)
   );

   // Assertion 2: Check that valid_out remains low until the pipeline latency has been reached
   assert property ( 
      @(posedge clk)
      (rst == 0) |=> (valid_out == 0) 
      ## (LATENCY - 1) 
      (valid_out != 0)
   );

   // Assertion 3: Check that valid_out matches valid_in from LATENCY cycles ago
   assert property ( 
      @(posedge clk)
      (rst == 0) |=> (valid_out == valid_in) 
      ## LATENCY 
      (valid_in != 0)
   );

   // Assertion 4: Check that out remains low until the pipeline latency has been reached
   assert property ( 
      @(posedge clk)
      (rst == 0) |=> (out == '0) 
      ## (LATENCY - 1) 
      (out != '0)
   );

endmodule