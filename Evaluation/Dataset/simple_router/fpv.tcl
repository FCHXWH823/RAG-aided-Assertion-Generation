analyze -clear
analyze -sv ./simple_router.sv
analyze -sv ./simple_router_sva.sv
analyze -sv ./simple_router_bind.svh

elaborate -top simple_router

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit
