analyze -clear
analyze -sv12 ./lcd.sv
analyze -sv12 ./lcd_sva.sv
analyze -sv12 ./lcd_bind.svh

elaborate -top lcd

clock clk
reset -expression ~(state[0])
prove -all
report -summary -force -result -file fpv.rpt
exit

