analyze -clear
analyze -sv ./register_assertion.sv

elaborate -top register

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
