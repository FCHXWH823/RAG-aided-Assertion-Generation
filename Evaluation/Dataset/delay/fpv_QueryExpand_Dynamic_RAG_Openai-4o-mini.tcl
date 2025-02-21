analyze -clear
analyze -sv12 ./delay_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top delay

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
exit

