analyze -clear
analyze -sv12 ./Gray_To_Binary_CoT-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top Gray_To_Binary

clock clk
reset -expression ~rst
prove -all
report -summary -force -result -file fpv_CoT-Dynamic-RAG-Openai-4o-mini.rpt
exit

