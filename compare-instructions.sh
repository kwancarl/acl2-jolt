#!/bin/bash

# Array of instruction names
instructions=(
    "add_instruction_32"
    "add_instruction_64"
    "and_instruction_32"
    "and_instruction_64"
    "beq_instruction_32"
    "beq_instruction_64"
    "bge_instruction_32"
    "bge_instruction_64"
    "bgeu_instruction_32"
    "bgeu_instruction_64"
    "bne_instruction_32"
    "bne_instruction_64"
    "lb_instruction_32"
    "lb_instruction_64"
    "lh_instruction_32"
    "lh_instruction_64"
    "or_instruction_32"
    "or_instruction_64"
    "sb_instruction_32"
    "sb_instruction_64"
    "sh_instruction_32"
    "sh_instruction_64"
    "sw_instruction_32"
    "sw_instruction_64"
    "slt_instruction_32"
    "slt_instruction_64"
    "sltu_instruction_32"
    "sltu_instruction_64"
    "sub_instruction_32"
    "sub_instruction_64"
    "xor_instruction_32"
    "xor_instruction_64"
    "sra_instruction_32"
    "sra_instruction_64"
    "sll_instruction_32"
    "sll_instruction_64"
    "srl_instruction_32"
    "srl_instruction_64"
)

# Add a new variable for the skip-generation flag
skip_file_generation=false

# Parse command-line arguments
while getopts ":s-:" opt; do
  case $opt in
    s)
      skip_file_generation=true
      ;;
    -)
      case "${OPTARG}" in
        skip)
          skip_file_generation=true
          ;;
        *)
          echo "Invalid option: --${OPTARG}" >&2
          exit 1
          ;;
      esac
      ;;
    \?)
      echo "Invalid option: -$OPTARG" >&2
      exit 1
      ;;
  esac
done

validation_dir="validation/instructions"

# Post-processing function for the ACL2 files to remove line breaks
post_process_acl2_output() {
    local input_file="$1"
    local output_file="${input_file}.tmp"
    
    # Remove single line breaks within cons pairs
    awk '
    BEGIN { RS = ""; ORS = "\n\n" }
    {
        gsub(/\n /, " ");
        print
    }
    ' "$input_file" > "$output_file"
    
    # Replace the original file with the processed one
    mv "$output_file" "$input_file"
}

if [ "$skip_file_generation" = false ]; then
    # Step 0: Create the validation directory if it doesn't exist
    mkdir -p "$validation_dir"

    # Step 1: Call Rust print functions
    echo "Calling Rust print functions..."
    echo
    # Have to be inside Rust project directory
    cd jolt
    cargo test --package jolt-core --lib -- jolt::instruction::print::test --show-output
    cd ..

    # Step 2: Call ACL2 to print its version of the instructions
    echo "Calling ACL2 print functions..."
    echo
    acl2 < print-instructions.lisp

    # Post-process all the ACL2 files to remove line breaks
    echo "Post-processing ACL2 output files to remove line breaks..."
    for instruction in "${instructions[@]}"; do
        acl2_file="${validation_dir}/${instruction}_acl2.txt"
        if [ -f "$acl2_file" ]; then
            post_process_acl2_output "$acl2_file"
        fi
    done
    echo "Post-processing complete."
    echo
else
    echo "Skipping file generation steps..."
    echo
fi

# Step 3: Compare the files
echo "Comparing Rust and ACL2 outputs..."
echo
all_passed=true
for instruction in "${instructions[@]}"; do
    rust_file="${instruction}_rust.txt"
    acl2_file="${instruction}_acl2.txt"

    if [ -f "${validation_dir}/${rust_file}" ] && [ -f "${validation_dir}/${acl2_file}" ]; then
        if diff -q "${validation_dir}/${rust_file}" "${validation_dir}/${acl2_file}" >/dev/null 2>&1; then
            echo "${instruction}: Files are identical. Test passed."
            echo
            # Delete the generated files
            # rm "$rust_file" "$acl2_file"
        else
            echo "${instruction}: Files are different. Test failed."
            echo
            echo "Please check the differences between ${validation_dir}/${rust_file} and ${validation_dir}/${acl2_file}"
            echo
            all_passed=false
        fi
    else
        echo "${instruction}: One or both files missing. Test failed."
        echo
        all_passed=false
    fi
done

if $all_passed; then
    echo "All tests passed successfully."
    echo
else
    echo "Some tests failed. Please check the output above for details."
    echo
    exit 1
fi
