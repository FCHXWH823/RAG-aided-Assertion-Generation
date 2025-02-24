analyze -clear
analyze -sv12 ./busarbiter_assertion.sv

elaborate -top busarbiter

clock clk
reset -expression reset
prove -all
report -summary -force -result -file fpv.rpt
exit
