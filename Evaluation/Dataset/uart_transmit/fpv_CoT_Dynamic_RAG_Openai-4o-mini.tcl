analyze -clear
analyze -sv12 ./uart_transmit_CoT-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top uart_transmit

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_CoT-Dynamic-RAG-Openai-4o-mini.rpt
exit

