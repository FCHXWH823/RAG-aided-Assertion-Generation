analyze -clear
analyze -sv12 ./arb2_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top arb2

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
exit

