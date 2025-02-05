analyze -clear
analyze -sv12 ./lcd_assertion.sv

elaborate -top lcd

clock clk
reset -expression ~(state[0])
prove -all
report -summary -force -result -file fpv.rpt
exit

