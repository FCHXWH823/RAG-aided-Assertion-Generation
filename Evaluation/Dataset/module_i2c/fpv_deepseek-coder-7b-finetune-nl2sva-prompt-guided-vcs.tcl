analyze -clear
analyze -sv12 ./module_i2c_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv

elaborate -top module_i2c

clock PCLK
reset PRESETn
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

