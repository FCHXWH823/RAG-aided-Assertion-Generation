analyze -clear
analyze -sv12 ./reversing_bits_assertion.sv

elaborate -top reversing_bits

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

