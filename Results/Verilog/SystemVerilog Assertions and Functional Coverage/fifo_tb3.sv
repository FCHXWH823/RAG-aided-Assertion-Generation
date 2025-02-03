module fifo_tb3;

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

   int tag=0, serving=0;   
   function void inc_tag();
      tag = tag + 1'b1;
   endfunction
   
   function void inc_serving();
      serving = serving + 1'b1; 
   endfunction
   
   property check_output;
      int wr_tag;
      logic [WIDTH-1:0] data;
            @(posedge clk) (wr_en && !full, wr_tag=tag, inc_tag(), data=wr_data) |-> first_match(##[1:$] (rd_en && !empty && serving==wr_tag, inc_serving())) ##1 rd_data==data;
   endproperty
            
   ap_check_output : assert property (check_output);
         
endmodule