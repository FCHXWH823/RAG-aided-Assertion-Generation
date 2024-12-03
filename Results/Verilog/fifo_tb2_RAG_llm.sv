module fifo_tb2_RAG_llm;

   localparam WIDTH = 8;
   localparam DEPTH = 16;
   
   logic             clk;
   logic             rst;
   logic             full;
   logic             wr_en;
   logic [WIDTH-1:0] wr_data;
   logic             empty; 
   logic             rd_en; 
   logic [WIDTH-1:0] rd_data;

   fifo #(.WIDTH(WIDTH), .DEPTH(DEPTH)) DUT (.*);
   
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin
      $timeformat(-9, 0, " ns");
      rst <= 1'b1;
      rd_en <= 1'b0;
      wr_en <= 1'b0;
      wr_data <= '0;      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < 10000; i++) begin
         wr_data <= $random;
         wr_en <= $random;
         rd_en <= $random;
         @(posedge clk);        
      end

      disable generate_clock;
      $display("Tests Completed.");      
   end  

   // Assertion 1: Check that we never write to the FIFO when it is full
   a1: assert property (@(posedge clk) (!full) |=> (wr_en |-> !full));

   // Assertion 2: Check that we never read from the FIFO when it is empty
   a2: assert property (@(posedge clk) (!empty) |=> (rd_en |-> !empty));

   // Assertion 3: Check that a valid write leads to a matching read
   logic [WIDTH-1:0] data; // local variable to store wr_data
   a3: assert property (
      @(posedge clk) 
      (wr_en && !full && (data = wr_data)) |=> 
      ##[1:$] (rd_en && !empty && (rd_data == data))
   ) else $display("At time %0t: Matching read for data %0d", $time, rd_data);

endmodule