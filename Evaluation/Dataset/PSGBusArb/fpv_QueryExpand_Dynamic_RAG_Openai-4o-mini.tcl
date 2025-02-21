analyze -clear
analyze -sv12 ./PSGBusArb_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top PSGBusArb

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
exit

