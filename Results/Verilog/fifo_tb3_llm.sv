module fifo_tb3_llm;

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

   // Additional variables for assertions
   integer          wr_tag;          // Unique tag for writes
   integer          current_tag;     // Counter for serving writes
   integer          served_tag;      // Tag of the served write
   reg              tag_valid;       // Indicates if the tag is valid

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

      // Initialize the tag counters
      wr_tag = 0;         
      current_tag = 0;  
      tag_valid = 0;     
      
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;

      for (int i=0; i < 10000; i++) begin
         wr_data <= $random;
         wr_en <= $random;
         rd_en <= $random;

         if (wr_en) begin
            wr_tag = current_tag;         // Assign the current tag to the write
            tag_valid = 1;                // Set tag as valid
            current_tag = current_tag + 1;// Increment the tag for the next write
         end
         
         // Check if there's a read operation
         if (rd_en && tag_valid) begin
            served_tag = wr_tag;          // Assign served tag from wr_tag
            tag_valid = 0;                // Invalidate the tag after it is served
         end

         @(posedge clk);         
      end

      disable generate_clock;
      $display("Tests Completed.");
   end         

   // Assertion 1: Check that there is no write when FIFO is full
   assert property ( @(posedge clk) (!full || !wr_en) )
      else $fatal("Error: Write attempted while FIFO is full!");

   // Assertion 2: Check that there is no read when FIFO is empty
   assert property ( @(posedge clk) (!empty || !rd_en) )
      else $fatal("Error: Read attempted while FIFO is empty!");

   // Assertion 3: Check matching read after valid write
   assert property ( @(posedge clk) 
      (wr_en && tag_valid) |=> 
      (rd_en && (served_tag == wr_tag) ##1 (rd_data == wr_data))
   )
      else $fatal("Error: Read data does not match the written data for the served tag!");

endmodule