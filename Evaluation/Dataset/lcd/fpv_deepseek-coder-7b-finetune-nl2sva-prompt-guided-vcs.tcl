analyze -clear
analyze -sv12 ./lcd_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv

elaborate -top lcd

clock clk
reset -none
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

