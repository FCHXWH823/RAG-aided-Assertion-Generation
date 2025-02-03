module simple_pipeline_tb_RAG_llm;

   localparam int NUM_TESTS = 1000;
   localparam int WIDTH = 8;
      
   logic          clk, rst, valid_in, valid_out;
   logic [WIDTH-1:0] in[8];
   logic [WIDTH-1:0] out;
    
   simple_pipeline #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while (1) #5 clk = ~clk;      
   end

   initial begin
      $timeformat(-9, 0, "" ns"");

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

      $display(""Tests completed."");      
      disable generate_clock;
   end
   
   function automatic logic is_out_correct2(logic [WIDTH-1:0] in[8], logic [WIDTH-1:0] out);
      logic [WIDTH-1:0] sum = 0;
      
      for (int i=0; i < 4; i++) begin
         sum += in[i*2] * in[i*2+1];     
      end
      
      return sum == out;      
   endfunction
   
   int count;    
   always_ff @(posedge clk or posedge rst) begin
     if (rst) 
       count = 0;
     else if (count < DUT.LATENCY) 
       count++;
   end

   // Assertion 1: Check correctness of output data after latency
   assert property (@(posedge clk) disable iff (rst) 
      (count == DUT.LATENCY) |=> (is_out_correct2($past(in), $past(out))));

   // Assertion 2: Ensure valid_out remains deasserted while count < DUT.LATENCY
   assert property (@(posedge clk) disable iff (rst) 
      (count < DUT.LATENCY) |=> (valid_out == 1'b0));

   // Assertion 3: Check that valid_out matches valid_in after latency
   assert property (@(posedge clk) disable iff (rst) 
      (count == DUT.LATENCY) |=> (valid_out == $past(valid_in, DUT.LATENCY)));

   // Assertion 4: Check that out is zero while count < DUT.LATENCY
   assert property (@(posedge clk) disable iff (rst) 
      (count < DUT.LATENCY) |=> (out == '0));
   
endmodule