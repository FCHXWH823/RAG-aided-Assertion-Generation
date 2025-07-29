analyze -clear
analyze -sv12 ./VGA_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.sv

elaborate -top VGA

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv_deepseek-coder-7b-finetune-nl2sva-prompt-guided-vcs.rpt
exit

