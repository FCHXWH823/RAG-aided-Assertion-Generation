analyze -clear
analyze -sv12 ./ff_QueryExpand-Dynamic-RAG-Openai-4o-mini.sv

elaborate -top ff

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv__QueryExpand-Dynamic-RAG-Openai-4o-mini.rpt
