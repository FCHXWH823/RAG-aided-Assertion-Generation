analyze -clear
analyze -sv12 ./or1200_defines.v
analyze -sv12 ./or1200_ctrl_Openai-4o-mini.sv

elaborate -top or1200_ctrl

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_Openai-4o-mini.rpt
exit

