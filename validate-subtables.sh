#!/bin/bash

# Array of subtable names
subtables=(
    "and_subtable"
    "eq_subtable"
    "eq_abs_subtable"
    "identity_subtable"
    "left_msb_subtable"
    "lt_abs_subtable"
    "ltu_subtable"
    "or_subtable"
    "right_msb_subtable"
    "sign_extend_subtable_8"
    "sign_extend_subtable_16"
    "sll_subtable_0_32"
    "sll_subtable_1_32"
    "sll_subtable_2_32"
    "sll_subtable_3_32"
    "sra_sign_subtable_8"
    "srl_subtable_0_32"
    "srl_subtable_1_32"
    "srl_subtable_2_32"
    "srl_subtable_3_32"
    "truncate_overflow_subtable_8"
    "truncate_overflow_subtable_32"
    "xor_subtable"
    # "div_by_zero_subtable"
    # "left_is_zero_subtable"
    # "right_is_zero_subtable"
)

# Step 1: Call Rust print functions
echo "Calling Rust print functions..."
for subtable in "${subtables[@]}"; do
    cargo test --package jolt-core --lib -- "jolt::subtable::print::test::${subtable}" --exact --nocapture
done

# Step 2: Call ACL2 to print its version of the subtables
echo "Calling ACL2 to print subtables..."
# TODO: Add the command to run ACL2 and generate its version of the subtables
# For example: acl2 < print_subtables.lisp

# Step 3: Compare the files
echo "Comparing Rust and ACL2 outputs..."
all_passed=true
for subtable in "${subtables[@]}"; do
    rust_file="${subtable}_4.txt"
    acl2_file="acl2_${subtable}_4.txt"
    
    if [ -f "$rust_file" ] && [ -f "$acl2_file" ]; then
        if diff -q "$rust_file" "$acl2_file" >/dev/null 2>&1; then
            echo "${subtable}: Files are identical. Test passed."
            # Delete the generated files
            rm "$rust_file" "$acl2_file"
        else
            echo "${subtable}: Files are different. Test failed."
            echo "Please check the differences between $rust_file and $acl2_file"
            all_passed=false
        fi
    else
        echo "${subtable}: One or both files missing. Test failed."
        all_passed=false
    fi
done

if $all_passed; then
    echo "All tests passed successfully."
else
    echo "Some tests failed. Please check the output above for details."
    exit 1
fi