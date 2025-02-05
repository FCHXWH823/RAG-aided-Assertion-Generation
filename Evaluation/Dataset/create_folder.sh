#!/bin/bash

# Script to create a folder and generate specific files based on the user input name.

echo "Enter the name for the folder and files:"
read Name

# Create the directory if it doesn't exist
mkdir -p "$Name"

# Navigate into the directory
cd "$Name"

# Create the files
touch "${Name}.sv" "${Name}_sva.sv" "${Name}_bind.svh" "fpv.tcl" "jg.sh"

# Add content to fpv.tcl
echo "analyze -clear
analyze -sv12 ./${Name}.sv
analyze -sv12 ./${Name}_sva.sv
analyze -sv12 ./${Name}_bind.svh

elaborate -top $Name

clock clk
reset -expression rst
prove -all
report -summary -force -result -file fpv.rpt
exit
" > fpv.tcl

echo "bind ${Name} ${Name}_sva #() u_${Name}_sva (.*);
" > ${Name}_bind.svh

echo "jg -no_gui fpv.tcl" > jg.sh
chmod 777 ./jg.sh

echo "Folder and files created successfully."
