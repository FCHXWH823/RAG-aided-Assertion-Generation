analyze -clear
analyze -sv12 ./module_i2c_assertion.sv

elaborate -top module_i2c

clock PCLK
reset PRESETn
prove -all
report -summary -force -result -file fpv.rpt
exit

