analyze -clear
analyze -sv12 ./arbiter_assertion.sv

elaborate -top arbiter

clock clk
reset -expression ~rst_n
prove -all
report -summary -force -result -file fpv.rpt
exit

