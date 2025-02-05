analyze -clear
analyze -sv12 ./i2c_assertion.sv

elaborate -top i2c

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

