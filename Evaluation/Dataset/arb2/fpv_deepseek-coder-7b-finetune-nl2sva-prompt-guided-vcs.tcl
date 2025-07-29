analyze -clear
analyze -sv12 ./arb2_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv

elaborate -top arb2

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

