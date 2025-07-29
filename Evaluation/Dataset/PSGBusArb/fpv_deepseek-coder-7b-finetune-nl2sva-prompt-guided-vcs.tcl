analyze -clear
analyze -sv12 ./PSGBusArb_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv

elaborate -top PSGBusArb

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

