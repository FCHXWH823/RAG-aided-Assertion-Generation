analyze -clear
analyze -sv12 ./Gray_Code_Counter_CoT-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top Gray_Code_Counter

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv_CoT-Dynamic-RAG-Openai-4o-mini.rpt
exit

