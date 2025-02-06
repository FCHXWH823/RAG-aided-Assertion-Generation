analyze -clear
analyze -sv12 ./Gray_Code_Counter_assertion.sv

elaborate -top Gray_Code_Counter

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv.rpt
exit

