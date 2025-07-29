analyze -clear
analyze -sv12 ./PWM_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv

elaborate -top PWM

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

