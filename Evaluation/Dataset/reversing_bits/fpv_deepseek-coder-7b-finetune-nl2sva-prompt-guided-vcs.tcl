analyze -clear
analyze -sv12 ./reversing_bits_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv

elaborate -top reversing_bits

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

