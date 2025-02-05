analyze -clear
analyze -sv ./reversing_bits.sv
analyze -sv ./reversing_bits_sva.sv
analyze -sv ./reversing_bits_bind.svh

elaborate -top reversing_bits

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

