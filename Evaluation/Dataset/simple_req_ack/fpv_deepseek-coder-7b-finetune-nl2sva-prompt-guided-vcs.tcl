analyze -clear
analyze -sv12 ./simple_req_ack_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv

elaborate -top simple_req_ack

clock clk
reset -expression !rst_n
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

