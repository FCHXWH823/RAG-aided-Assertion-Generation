analyze -clear
analyze -sv12 ./delay_assertion.sv

elaborate -top delay

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

