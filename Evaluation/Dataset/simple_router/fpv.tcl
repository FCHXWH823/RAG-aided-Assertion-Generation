analyze -clear
analyze -sv ./simple_router_assertion.sv

elaborate -top simple_router

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit
