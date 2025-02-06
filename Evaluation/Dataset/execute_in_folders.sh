#!/bin/bash

# Name of the executable file
EXECUTABLE="fpv.tcl"

# Loop through all directories in the current folder
for dir in */; do
    if [[ -d "$dir" && -x "$dir/$EXECUTABLE" ]]; then
        echo "Executing $EXECUTABLE in $dir"
        (cd "$dir" && jg -no_gui "$EXECUTABLE")
    else
        echo "Skipping $dir (executable not found or not executable)"
    fi
done
