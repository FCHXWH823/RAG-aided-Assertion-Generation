analyze -clear
analyze -sv ./Ripple_Carry_Adder.sv
analyze -sv ./Ripple_Carry_Adder_sva.sv
analyze -sv ./Ripple_Carry_Adder_bind.svh

elaborate -top Ripple_Carry_Adder

clock clk
reset -expression ~rst
prove -all
report -summary -force -result -file fpv.rpt
exit

