analyze -clear
analyze -sv12 ./simple_router_Openai-4o-mini.sv

elaborate -top simple_router

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_Openai-4o-mini.rpt
exit
