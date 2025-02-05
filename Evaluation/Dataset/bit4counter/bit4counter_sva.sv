/* File name: bit4counter_assertions.sv */
module bit4counter_sva (
  input clk,
  input reset,
  input reg [3:0] counter,
  input reg overflow
);

  // Property declarations

  // Property to check if the counter increments by 1
  property p_increment;
  @(posedge clk)
  (!reset && $past(counter) != 4'b1111) |-> ##1 (counter == $past(counter) + 4'b0001 && overflow == 0);
  endproperty
  assert property (p_increment);

  // Property to check if the counter overflows
  property p_overflow;
  @(posedge clk)
  (!reset && $past(counter) == 4'b1111) |-> ##1 (counter == 4'b0000 && overflow == 1);
  endproperty
  assert property (p_overflow);
  

endmodule