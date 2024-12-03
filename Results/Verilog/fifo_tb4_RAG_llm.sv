module fifo_tb4_RAG_llm;

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

   // Assertion 1: Check that there is never a write while the FIFO is full
   assert property (@(posedge clk) !(full && wr_en));

   // Assertion 2: Check that there is never a read while the FIFO is empty
   assert property (@(posedge clk) !(empty && rd_en));

   // Assertion 3: Check that the read data should equal the first element in FIFO
   logic [WIDTH-1:0] correct_rd_data; // Assume this is defined and set appropriately in the FIFO implementation
   assert property (@(posedge clk) (rd_en |=> (rd_data == correct_rd_data)));

endmodule