module fifo_tb3_RAG_llm;

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
      $timeformat(-9, 0, "" ns"");
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
      $display(""Tests Completed."");
   end

   // Assertion 1: If a write operation is initiated, then the FIFO should not be full in the next clock cycle.
   assert property (@(posedge clk) (wr_en && DUT.valid_wr) |=> !full);

   // Assertion 2: If a read operation is initiated, then the FIFO should not be empty in the next clock cycle.
   assert property (@(posedge clk) (rd_en && DUT.valid_rd) |=> !empty);

   // Assertion 3: Check that on each valid write, we eventually read the same data with the matching tag.
   logic [31:0] wr_tag;
   logic [31:0] serving_id;
   int write_counter = 0;

   always @(posedge clk) begin
      if (wr_en && DUT.valid_wr) begin
         wr_tag <= write_counter;  // Assign a unique tag for each write
         write_counter++;
      end
   end

   assert property (@(posedge clk) (wr_en && DUT.valid_wr) |=> (first_match(wr_tag, serving_id) ##1 (rd_en && DUT.valid_rd && (DUT.rd_tag == wr_tag) |=> (rd_data == wr_data))));

endmodule