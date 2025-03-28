analyze -clear
analyze -sv12 ./delay2_assertion.sv

elaborate -top delay2

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

