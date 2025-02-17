analyze -clear
analyze -sv12 ./uartTrans_Dynamic-RAG-Openai-4o-mini.sv

elaborate -top uartTrans

clock clk
reset reset
prove -all
report -summary -force -result -file fpv_Dynamic-RAG-Openai-4o-mini.rpt
exit

