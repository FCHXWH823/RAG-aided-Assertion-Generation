analyze -clear
analyze -sv12 ./register_Openai-4o-mini.sv

elaborate -top register

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_Openai-4o-mini.rpt
