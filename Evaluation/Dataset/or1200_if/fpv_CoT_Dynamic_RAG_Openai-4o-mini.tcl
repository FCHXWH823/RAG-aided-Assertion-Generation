analyze -clear
analyze -sv12 ./or1200_if_CoT-Dynamic-RAG-Openai-4o-mini.sv
analyze -sv12 ./or1200_defines.v

elaborate -top or1200_if

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_CoT-Dynamic-RAG-Openai-4o-mini.rpt
exit

