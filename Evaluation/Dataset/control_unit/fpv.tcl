analyze -clear
analyze -sv12 ./control_unit_assertion.sv

elaborate -top control_unit

clock clk
reset -expression rst_n
prove -all
report -summary -force -result -file fpv.rpt
exit

