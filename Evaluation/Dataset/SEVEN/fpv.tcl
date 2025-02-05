analyze -clear
analyze -sv12 ./SEVEN_assertion.sv

elaborate -top SEVEN

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

