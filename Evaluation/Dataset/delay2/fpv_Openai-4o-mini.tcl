analyze -clear
analyze -sv12 ./delay2_Openai-4o-mini.sv

elaborate -top delay2

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_Openai-4o-mini.rpt
exit

