analyze -clear
analyze -sv12 ./Ripple_Carry_Adder_assertion.sv

elaborate -top Ripple_Carry_Adder

clock clk
reset -expression ~rst
prove -all
report -summary -force -result -file fpv.rpt
exit

