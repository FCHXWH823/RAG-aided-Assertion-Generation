analyze -clear
analyze -sv ./register.sv
analyze -sv ./register_sva.sv
analyze -sv ./register_bind.svh

elaborate -top register

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
