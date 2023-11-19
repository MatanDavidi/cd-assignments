#!/bin/bash

# Specify the directory path
directory_path="./oatprograms"

# Specify the command you want to run for each file
command_to_run="./main.native"

# Loop through each file in the directory
for file in "$directory_path"/*; do
    # Check if the item is a file (not a directory)
    if [ -f "$file" ]; then
        # Run the command for each file
        echo "$file$";
        $command_to_run "$file"
    fi
done
