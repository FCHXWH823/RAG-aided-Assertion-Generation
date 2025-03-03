analyze -clear
analyze -sv12 ./ff_CoT-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top ff

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_CoT-Dynamic-RAG-Openai-4o-mini.rpt
