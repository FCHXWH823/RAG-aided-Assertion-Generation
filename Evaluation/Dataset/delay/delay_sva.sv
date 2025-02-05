module delay_sva
  #(
    parameter int 		CYCLES=4,
    parameter int 		WIDTH=8,
    parameter logic 		HAS_ASYNC_RESET = 1'b1,
    parameter logic 		RESET_ACTIVATION_LEVEL = 1'b1,
    parameter logic [WIDTH-1:0] RESET_VALUE = '0
    )
   (
    input logic 	     clk, rst, en,
    input logic [WIDTH-1:0]  in,
    input logic [WIDTH-1:0] out
    );
      
//   localparam CYCLES = 4;  
//   localparam WIDTH = 8;  
//   localparam logic HAS_ASYNC_RESET = 1'b1;   
//   localparam logic RESET_ACTIVATION_LEVEL = 1'b1;   
//   localparam logic [WIDTH-1:0] RESET_VALUE = '0; 

   default clocking cb @(posedge clk);
   endclocking
   default disable iff (rst);

   int count;    
   always_ff @(posedge clk or posedge rst)
     if (rst) count = 0;
     else if (en == 1'b1 && count < CYCLES) count ++;

   assert property(count < CYCLES || out == $past(in, CYCLES, en));

   assert property(count == CYCLES || out == RESET_VALUE);

   assert property(!en |=> $stable(out));
         
endmodule // delay_tb4
