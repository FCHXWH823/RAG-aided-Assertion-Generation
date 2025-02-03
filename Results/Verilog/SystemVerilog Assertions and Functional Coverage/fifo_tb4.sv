module fifo_tb4;

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
      
   assert property (@(posedge clk) DUT.valid_wr |-> !full);
   assert property (@(posedge clk) DUT.valid_rd |-> !empty);

   logic [WIDTH-1:0] correct_rd_data;   
   logic [WIDTH-1:0] reference[$];

   always_ff @(posedge clk or posedge rst)
     if (rst) begin
        reference = {};
     end
     else begin
        correct_rd_data = reference[0];       
        
        if (rd_en && !empty) begin
           reference = reference[1:$];
        end

        if (wr_en && !full) begin
           reference = {reference, wr_data};
        end    
      end
   
   assert property(@(posedge clk) rd_en && !empty |=> rd_data == correct_rd_data);     
         
endmodule