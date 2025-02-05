analyze -clear
analyze -sv12 ./PWM_assertion.sv

elaborate -top PWM

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

