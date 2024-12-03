module delay_tb3_RAG_llm;

   localparam NUM_TESTS = 1000;
   localparam CYCLES = 30;  
   localparam WIDTH = 8;  
   localparam logic HAS_ASYNC_RESET = 1'b1;   
   localparam logic RESET_ACTIVATION_LEVEL = 1'b1;   
   localparam logic [WIDTH-1:0] RESET_VALUE = '0; 
   logic             clk = 1'b0;
   logic             rst;
   logic             en;
   logic [WIDTH-1:0] in; 
   logic [WIDTH-1:0] out;

   delay #(.CYCLES(CYCLES), .WIDTH(WIDTH), .HAS_ASYNC_RESET(HAS_ASYNC_RESET),
           .RESET_ACTIVATION_LEVEL(RESET_ACTIVATION_LEVEL), 
           .RESET_VALUE(RESET_VALUE))

   DUT (.en(1'b1), .*);

   initial begin : generate_clock
      while (1)
        #5 clk = ~clk;      
   end
           
   initial begin
      $timeformat(-9, 0, "" ns"");

      rst <= 1'b1;
      in <= '0;      
      for (int i=0; i < 5; i++)
        @(posedge clk);
      
      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin
         in <= $random;
         @(posedge clk);
      end  

      disable generate_clock;
      $display(""Tests completed."");      
   end

   int count;    
   always_ff @(posedge clk or posedge rst)
     if (rst) count = 0;
     else if (count < CYCLES) count ++;

   // Assertion 1: Output matches input delayed by CYCLES
   property p_output_matches_input_delayed;
      @(posedge clk) 
      (count >= CYCLES && !rst) |=> (out === in);
   endproperty
   assert p_output_matches_input_delayed;

   // Assertion 2: Output matches RESET_VALUE when count equals CYCLES
   property p_output_matches_reset_value;
      @(posedge clk) 
      (count == CYCLES) |=> (out === RESET_VALUE);
   endproperty
   assert p_output_matches_reset_value;

endmodule