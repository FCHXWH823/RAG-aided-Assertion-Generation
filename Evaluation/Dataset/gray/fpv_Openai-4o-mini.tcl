analyze -clear
analyze -sv12 ./gray_Openai-4o-mini.sv

elaborate -top gray

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_Openai-4o-mini.rpt
exit

