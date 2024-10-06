#!/bin/bash

# Array of subtable names
subtables=(
    "and_subtable"
    "eq_subtable"
    "eq_abs_subtable"
    "left_msb_subtable"
    "lt_abs_subtable"
    "ltu_subtable"
    "or_subtable"
    "right_msb_subtable"
    "xor_subtable"

    "sll_subtable_0_32"
    "sll_subtable_1_32"
    "sll_subtable_2_32"
    "sll_subtable_3_32"

    "sll_subtable_0_64"
    "sll_subtable_1_64"
    "sll_subtable_2_64"
    "sll_subtable_3_64"
    "sll_subtable_4_64"
    "sll_subtable_5_64"
    "sll_subtable_6_64"
    "sll_subtable_7_64"

    "sra_sign_subtable_32"
    "sra_sign_subtable_64"

    "srl_subtable_0_32"
    "srl_subtable_1_32"
    "srl_subtable_2_32"
    "srl_subtable_3_32"

    "srl_subtable_0_64"
    "srl_subtable_1_64"
    "srl_subtable_2_64"
    "srl_subtable_3_64"
    "srl_subtable_4_64"
    "srl_subtable_5_64"
    "srl_subtable_6_64"
    "srl_subtable_7_64"

    "identity_subtable"
    "sign_extend_subtable_8"
    "sign_extend_subtable_16"
    "truncate_overflow_subtable_8"
    "truncate_overflow_subtable_32"
    # "div_by_zero_subtable"
    # "left_is_zero_subtable"
    # "right_is_zero_subtable"
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

validation_dir="validation/subtables"

if [ "$skip_file_generation" = false ]; then

    # Step 0: Create the validation directory for subtables if it doesn't exist
    mkdir -p "$validation_dir"

    # Step 1: Call Rust print functions
    echo "Calling Rust print functions..."
    echo
    # Have to be inside Rust project directory
    cd jolt
    cargo test --package jolt-core --lib -- jolt::subtable::print::test --show-output
    cd ..

    # Step 2: Call ACL2 to print its version of the subtables
    echo "Calling ACL2 print functions..."
    echo

    acl2 < print-subtables.lisp
else
    echo "Skipping file generation steps..."
    echo
fi

# Step 3: Compare the files
echo "Comparing Rust and ACL2 outputs..."
echo

all_passed=true
for subtable in "${subtables[@]}"; do
    rust_file="${subtable}_rust.txt"
    acl2_file="${subtable}_acl2.txt"
    
    if [ -f "${validation_dir}/${rust_file}" ] && [ -f "${validation_dir}/${acl2_file}" ]; then
        if diff -q "${validation_dir}/${rust_file}" "${validation_dir}/${acl2_file}" >/dev/null 2>&1; then
            echo "${subtable}: Files are identical. Test passed."
            echo
            # Delete the generated files
            # rm "$rust_file" "$acl2_file"
        else
            echo "${subtable}: Files are different. Test failed."
            echo
            echo "Please check the differences between ${validation_dir}/${rust_file} and ${validation_dir}/${acl2_file}"
            echo
            all_passed=false
        fi
    else
        echo "${subtable}: One or both files missing. Test failed."
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