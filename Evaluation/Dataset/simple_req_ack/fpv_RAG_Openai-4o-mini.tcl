analyze -clear
analyze -sv12 ./simple_req_ack_RAG-Openai-4o-mini.sv

elaborate -top simple_req_ack

clock clk
reset -expression !rst_n
prove -all
report -summary -force -result -file fpv_RAG-Openai-4o-mini.rpt
exit

