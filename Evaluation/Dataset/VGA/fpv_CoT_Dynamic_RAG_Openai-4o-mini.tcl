analyze -clear
analyze -sv12 ./VGA_CoT-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top VGA

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_CoT-Dynamic-RAG-Openai-4o-mini.rpt
exit

