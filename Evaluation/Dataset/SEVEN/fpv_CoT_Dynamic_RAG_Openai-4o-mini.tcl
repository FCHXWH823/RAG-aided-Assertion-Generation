analyze -clear
analyze -sv12 ./SEVEN_CoT-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top SEVEN

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_CoT-Dynamic-RAG-Openai-4o-mini.rpt
exit

