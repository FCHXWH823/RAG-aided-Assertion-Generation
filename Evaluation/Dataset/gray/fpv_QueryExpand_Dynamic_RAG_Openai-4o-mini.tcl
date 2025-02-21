analyze -clear
analyze -sv12 ./gray_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top gray

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv__QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
exit

