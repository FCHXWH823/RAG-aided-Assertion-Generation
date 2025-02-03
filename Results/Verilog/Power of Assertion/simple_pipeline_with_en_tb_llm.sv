module simple_pipeline_with_en_tb_llm;

   localparam int NUM_TESTS = 10000;
   localparam int WIDTH = 8;
      
   logic          clk, rst, en, valid_in, valid_out;
   logic [WIDTH-1:0] in[8];
   logic [WIDTH-1:0] out;
    
   simple_pipeline_with_en #(.WIDTH(WIDTH)) DUT (.*);

   initial begin : generate_clock
      clk = 1'b0;
      while (1) #5 clk = ~clk;      
   end

   initial begin
      $timeformat(-9, 0, "" ns"");

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

      $display(""Tests completed."");      
      disable generate_clock;
   end

      function automatic logic [WIDTH-1:0] model(logic [WIDTH-1:0] in[8]);
      logic [WIDTH-1:0] sum = 0;
      for (int i=0; i < 4; i++) sum += in[i*2] * in[i*2+1];      
      return sum;     
   endfunction

   int count;    
   always_ff @(posedge clk or posedge rst)
     if (rst) count = 0;
     else if (en == 1'b1 && count < DUT.LATENCY) count ++;

   // Assertion 1
   assert property (@(posedge clk) disable iff (rst) 
      (count == DUT.LATENCY) |=> (out == model(in))); 

   // Assertion 2
   assert property (@(posedge clk) disable iff (rst) 
      (count < DUT.LATENCY) |=> (valid_out == 1'b0)); 

   // Assertion 3
   assert property (@(posedge clk) disable iff (rst) 
      (count == DUT.LATENCY) |=> (valid_out == valid_in)); 

   // Assertion 4
   assert property (@(posedge clk) disable iff (rst) 
      (count < DUT.LATENCY) |=> (out == '0)); 

endmodule