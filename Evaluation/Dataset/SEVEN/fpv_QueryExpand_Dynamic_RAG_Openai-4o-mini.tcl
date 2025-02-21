analyze -clear
analyze -sv12 ./SEVEN_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top SEVEN

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv__QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
exit

