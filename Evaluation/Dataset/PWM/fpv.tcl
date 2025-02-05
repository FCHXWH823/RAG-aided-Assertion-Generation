analyze -clear
analyze -sv12 ./PWM.sv
analyze -sv12 ./PWM_sva.sv
analyze -sv12 ./PWM_bind.svh

elaborate -top PWM

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit

