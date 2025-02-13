analyze -clear
analyze -sv12 ./apb_RAG-Openai-4o-mini.sv

elaborate -top apb

clock PCLK
reset PRESETn
prove -all
report -summary -force -result -file fpv_RAG-Openai-4o-mini.rpt
exit

