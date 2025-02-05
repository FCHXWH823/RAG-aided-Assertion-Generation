module AR_sva (input logic [2500:0] a, input logic clk);


assert property (a<200);

endmodule