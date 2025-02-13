analyze -clear
analyze -sv12 ./second_largest_RAG-Openai-4o-mini.sv

elaborate -top second_largest

clock clk
reset -expression ~resetn
prove -all
report -summary -force -result -file fpv_RAG-Openai-4o-mini.rpt
exit

