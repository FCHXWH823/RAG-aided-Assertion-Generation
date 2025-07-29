analyze -clear
analyze -sv12 ./arbiter_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv

elaborate -top arbiter

clock clk
reset -expression ~rst_n
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

