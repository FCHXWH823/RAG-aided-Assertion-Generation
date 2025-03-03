analyze -clear
analyze -sv12 ./module_i2c_CoT-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top module_i2c

clock PCLK
reset PRESETn
prove -all
report -summary -force -result -file fpv_CoT-Dynamic-RAG-Openai-4o-mini.rpt
exit

