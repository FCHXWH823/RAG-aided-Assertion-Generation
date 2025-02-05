analyze -clear
analyze -sv ./ff_assertion.sv

elaborate -top ff

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
