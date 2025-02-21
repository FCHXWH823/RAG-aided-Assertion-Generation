analyze -clear
analyze -sv12 ./eth_rxstatem_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top eth_rxstatem

clock MRxClk
reset Reset
prove -all
report -summary -force -result -file fpv_QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
exit

