module register_tb2_llm;

   localparam NUM_TESTS = 10000;
   localparam WIDTH = 8;
   logic clk, rst, en;
   logic [WIDTH-1:0] in, out, prev_out;

   logic             output_check_en = 1'b0, first_en = 1'b0;
      
   register #(.WIDTH(WIDTH)) DUT (.clk(clk), .rst(rst), .en(en), .in(in), .out(out));

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
         prev_out = out; // Store the previous output for checking

         if (first_en) output_check_en = 1'b1;
         if (en) first_en = 1'b1;         
      end

      disable generate_clock;
      $display("Tests completed.");
   end 

   // Assertion 1: Validate output matches input when rst=0 and en=1
   always @(posedge clk) begin
      if (!rst) begin
         assert property (@(posedge clk) en == 1'b1 |-> out == in)
         else $error("Assertion 1 failed: output does not match input when en=1 and rst=0.");
      end
   end

   // Assertion 2: Validate output matches previous output when rst=0 and en=0
   always @(posedge clk) begin
      if (!rst) begin
         assert property (@(posedge clk) en == 1'b0 |-> out == prev_out)
         else $error("Assertion 2 failed: output does not match previous output when en=0 and rst=0.");
      end
   end

   // Assertion 3: Validate output does not change when rst=0 and en=0
   always @(posedge clk) begin
      if (!rst) begin
         assert property (@(posedge clk) en == 1'b0 |-> out === prev_out)
         else $error("Assertion 3 failed: output changed when en=0 and rst=0.");
      end
   end

   // Assertion 4: Check output is 0 when rst=1
   always @(rst) begin
      assert (rst == 1'b1 => out == 0)
      else $error("Assertion 4 failed: output is not 0 when rst=1.");
   end

endmodule