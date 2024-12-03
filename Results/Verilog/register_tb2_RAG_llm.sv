module register_tb2_RAG_llm;

   localparam NUM_TESTS = 10000;
   localparam WIDTH = 8;
   logic clk, rst, en;
   logic [WIDTH-1:0] in, out;

   logic             output_check_en = 1'b0, first_en = 1'b0;
      
   register #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;      
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");         

      rst <= 1'b1;
      in <= 1'b0;      
      en <= 1'b0;
      
      for (int i=0; i < 5; i++)
        @(posedge clk);

      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin    
         in <= $random;
         en <= $random;
         @(posedge clk);

         if (first_en) output_check_en = 1'b1;
         if (en) first_en = 1'b1;         
      end

      disable generate_clock;
      $display("Tests completed.");
   end 

   // Assertion 1: Check output equals input when rst=0 and en=1
   always @(posedge clk) begin
      assert property (rst == 0 && en == 1 |-> out == in)
      else $error("Assertion 1 failed: Output does not equal input when rst=0 and en=1.");
   end

   // Assertion 2: Check output equals previous output when rst=0 and en=0
   always @(posedge clk) begin
      assert property (rst == 0 && en == 0 |-> out == $past(out))
      else $error("Assertion 2 failed: Output does not equal previous output when rst=0 and en=0.");
   end

   // Assertion 3: Check output does not change when rst=0 and en=0
   always @(posedge clk) begin
      assert property (rst == 0 && en == 0 |-> out == $past(out))
      else $error("Assertion 3 failed: Output changed when rst=0 and en=0.");
   end

   // Assertion 4: Check output equals 0 when rst=1
   always @(rst) begin
      assert (rst == 1 -> out == 0)
      else $error("Assertion 4 failed: Output is not 0 when rst=1.");
   end

endmodule