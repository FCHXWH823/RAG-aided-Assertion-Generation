module delay_tb2_llm;

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
   DUT (.*);
   
   initial begin : generate_clock
      while (1)
        #5 clk = ~clk;      
   end
           
   initial begin
      $timeformat(-9, 0, "" ns"");

      rst <= 1'b1;
      en <= 1'b0;      
      in <= '0;      
      for (int i=0; i < 5; i++)
        @(posedge clk);

      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < NUM_TESTS; i++) begin
         in <= $random;
         en <= $random;         
         @(posedge clk);
      end  

      disable generate_clock;
      $display(""Tests completed."");      
   end

   logic [WIDTH-1:0] reference_queue[$];
   
   always_ff @(posedge clk or posedge rst)
     if (rst) begin
        reference_queue = {};
        for (int i=0; i < CYCLES; i++) reference_queue = {reference_queue, RESET_VALUE};
     end
     else if (en) begin
        reference_queue = {reference_queue[1:$], in};
     end

   // Assertion 1: Checks that at every rising edge of the clock, the output matches the expected value from reference_queue
   assert property (@(posedge clk) out == reference_queue[0])
     else $fatal(""Assertion failed: Output does not match expected value!"");

   // Assertion 2: Checks that the reset sets the reference queue to the reset value
   assert property (@(posedge rst) reference_queue == {RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE, RESET_VALUE}) 
     else $fatal(""Assertion failed: Reference queue not properly initialized on reset!"");

   // Assertion 3: Checks that the reference queue length does not exceed its defined capacity (CYCLES)
   assert property (always @(posedge clk) $count(reference_queue) <= CYCLES)
     else $fatal(""Assertion failed: Reference queue exceeds defined capacity!"");

endmodule