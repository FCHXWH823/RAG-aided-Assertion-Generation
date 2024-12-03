module simple_pipeline_tb_RAG_llm;

   localparam int NUM_TESTS = 1000;
   localparam int WIDTH = 8;
      
   logic          clk, rst, valid_in, valid_out;
   logic [WIDTH-1:0] in[8];
   logic [WIDTH-1:0] out;
   localparam int LATENCY = DUT.LATENCY; // Assuming DUT.LATENCY is defined

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
         for (int i=0; i < 8; i++) in[i] = $random;
         valid_in <= $random;
         @(posedge clk);
      end

      $display("Tests completed.");      
      disable generate_clock;
   end

   // Assertion 1: Check that once the pipeline reaches its defined latency, the output is correct based on the input values from DUT.LATENCY cycles ago
   assert property (rst == 0 |-> (now >= LATENCY * 10ns) |=> (out == in[(LATENCY - 1) % 8]));

   // Assertion 2: Check that valid_out remains low until the pipeline latency has been reached
   assert property (rst == 0 |-> (now < LATENCY * 10ns) |=> (valid_out == 0));

   // Assertion 3: Check that valid_out matches valid_in from DUT.LATENCY cycles ago
   assert property (rst == 0 |-> (now >= LATENCY * 10ns) |=> (valid_out == valid_in[(LATENCY - 1) % 8]));

   // Assertion 4: Check that out remains low until the pipeline latency has been reached
   assert property (rst == 0 |-> (now < LATENCY * 10ns) |=> (out == 0));

endmodule