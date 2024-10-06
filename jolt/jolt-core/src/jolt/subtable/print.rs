#[macro_export]
macro_rules! print_subtable_test {
    ($test_name:ident, $subtable_type:ty, $F:ty, $m:expr, $print_to_file:expr) => {
        #[test]
        fn $test_name() {
            let m = $m;
            let M = 1 << (2 * m);
            let subtable = <$subtable_type>::new();
            let materialized = subtable.materialize(M);

            let output: Box<dyn std::io::Write> = if $print_to_file {
                let file_name = format!("{}_rust.txt", stringify!($test_name));
                // Let the folder be `../../validation/subtables`
                let path = std::env::current_dir()
                    .expect("Failed to get current directory")
                    .parent()
                    .and_then(|p| p.parent())
                    .expect("Failed to get parent directory")
                    .join("validation/subtables/")
                    .join(file_name);
                println!("Attempting to create file at: {:?}", path);
                Box::new(std::fs::File::create(&path).expect("Failed to create file"))
            } else {
                Box::new(std::io::stdout())
            };
            let mut writer = std::io::BufWriter::new(output);

            // We want to print the subtable in the same format as ACL2. For most tables, this is
            // `((x . y) . val)\n` for decreasing x and y. For `identity`, `sign_extend`, and
            // `truncate_overflow`, the output format is `(x . val)\n` for decreasing x.
            let is_special_case = stringify!($test_name).contains("identity")
                || stringify!($test_name).contains("sign_extend")
                || stringify!($test_name).contains("truncate_overflow");
            if is_special_case {
            println!(
                    "This is either identity, sign_extend, or truncate_overflow. Printing table of format \"(x . val)\"..."
                );
            }

            for idx in (0..M).rev() {
                let entry = &materialized[idx];
                if is_special_case {
                    writeln!(writer, "({} . {})\n", idx, entry.to_u64().unwrap())
                        .expect("Failed to write");
                } else {
                    let (x, y) = $crate::utils::split_bits(idx, m);
                    writeln!(writer, "(({} . {}) . {})\n", x, y, entry.to_u64().unwrap())
                        .expect("Failed to write");
                }
            }
        }
    };
}

#[cfg(test)]
mod test {
    use crate::field::JoltField;
    use crate::jolt::subtable::{
        and::AndSubtable, eq::EqSubtable, eq_abs::EqAbsSubtable, identity::IdentitySubtable,
        left_msb::LeftMSBSubtable, lt_abs::LtAbsSubtable, ltu::LtuSubtable, or::OrSubtable,
        right_msb::RightMSBSubtable, sign_extend::SignExtendSubtable, sll::SllSubtable,
        sra_sign::SraSignSubtable, srl::SrlSubtable, truncate_overflow::TruncateOverflowSubtable,
        xor::XorSubtable, LassoSubtable,
    };
    // div_by_zero::DivByZeroSubtable,
    // left_is_zero::LeftIsZeroSubtable,
    // right_is_zero::RightIsZeroSubtable,
    use ark_bn254::Fr;
    use ark_serialize::Write;

    print_subtable_test!(and_subtable, AndSubtable<Fr>, Fr, 8, true);
    // print_subtable_test!(
    //     div_by_zero_subtable,
    //     DivByZeroSubtable<Fr>,
    //     Fr,
    //     8,
    //     true
    // );
    print_subtable_test!(eq_subtable, EqSubtable<Fr>, Fr, 8, true);
    print_subtable_test!(eq_abs_subtable, EqAbsSubtable<Fr>, Fr, 8, true);
    // print_subtable_test!(
    //     left_is_zero_subtable,
    //     LeftIsZeroSubtable<Fr>,
    //     Fr,
    //     8,
    //     true
    // );
    print_subtable_test!(left_msb_subtable, LeftMSBSubtable<Fr>, Fr, 8, true);
    print_subtable_test!(lt_abs_subtable, LtAbsSubtable<Fr>, Fr, 8, true);
    print_subtable_test!(ltu_subtable, LtuSubtable<Fr>, Fr, 8, true);
    print_subtable_test!(or_subtable, OrSubtable<Fr>, Fr, 8, true);
    // print_subtable_test!(
    //     right_is_zero_subtable,
    //     RightIsZeroSubtable<Fr>,
    //     Fr,
    //     8,
    //     true
    // );
    print_subtable_test!(right_msb_subtable, RightMSBSubtable<Fr>, Fr, 8, true);
    print_subtable_test!(xor_subtable, XorSubtable<Fr>, Fr, 8, true);

    print_subtable_test!(sll_subtable_0_32, SllSubtable<Fr, 0, 32>, Fr, 8, true);
    print_subtable_test!(sll_subtable_1_32, SllSubtable<Fr, 1, 32>, Fr, 8, true);
    print_subtable_test!(sll_subtable_2_32, SllSubtable<Fr, 2, 32>, Fr, 8, true);
    print_subtable_test!(sll_subtable_3_32, SllSubtable<Fr, 3, 32>, Fr, 8, true);
    print_subtable_test!(sll_subtable_0_64, SllSubtable<Fr, 0, 64>, Fr, 8, true);
    print_subtable_test!(sll_subtable_1_64, SllSubtable<Fr, 1, 64>, Fr, 8, true);
    print_subtable_test!(sll_subtable_2_64, SllSubtable<Fr, 2, 64>, Fr, 8, true);
    print_subtable_test!(sll_subtable_3_64, SllSubtable<Fr, 3, 64>, Fr, 8, true);
    print_subtable_test!(sll_subtable_4_64, SllSubtable<Fr, 4, 64>, Fr, 8, true);
    print_subtable_test!(sll_subtable_5_64, SllSubtable<Fr, 5, 64>, Fr, 8, true);
    print_subtable_test!(sll_subtable_6_64, SllSubtable<Fr, 6, 64>, Fr, 8, true);
    print_subtable_test!(sll_subtable_7_64, SllSubtable<Fr, 7, 64>, Fr, 8, true);
    print_subtable_test!(sra_sign_subtable_32, SraSignSubtable<Fr, 32>, Fr, 8, true);
    print_subtable_test!(sra_sign_subtable_64, SraSignSubtable<Fr, 64>, Fr, 8, true);
    print_subtable_test!(srl_subtable_0_32, SrlSubtable<Fr, 0, 32>, Fr, 8, true);
    print_subtable_test!(srl_subtable_1_32, SrlSubtable<Fr, 1, 32>, Fr, 8, true);
    print_subtable_test!(srl_subtable_2_32, SrlSubtable<Fr, 2, 32>, Fr, 8, true);
    print_subtable_test!(srl_subtable_3_32, SrlSubtable<Fr, 3, 32>, Fr, 8, true);
    print_subtable_test!(srl_subtable_0_64, SrlSubtable<Fr, 0, 64>, Fr, 8, true);
    print_subtable_test!(srl_subtable_1_64, SrlSubtable<Fr, 1, 64>, Fr, 8, true);
    print_subtable_test!(srl_subtable_2_64, SrlSubtable<Fr, 2, 64>, Fr, 8, true);
    print_subtable_test!(srl_subtable_3_64, SrlSubtable<Fr, 3, 64>, Fr, 8, true);
    print_subtable_test!(srl_subtable_4_64, SrlSubtable<Fr, 4, 64>, Fr, 8, true);
    print_subtable_test!(srl_subtable_5_64, SrlSubtable<Fr, 5, 64>, Fr, 8, true);
    print_subtable_test!(srl_subtable_6_64, SrlSubtable<Fr, 6, 64>, Fr, 8, true);
    print_subtable_test!(srl_subtable_7_64, SrlSubtable<Fr, 7, 64>, Fr, 8, true);

    print_subtable_test!(identity_subtable, IdentitySubtable<Fr>, Fr, 8, true);
    print_subtable_test!(sign_extend_subtable_8, SignExtendSubtable<Fr, 8>, Fr, 8, true);
    print_subtable_test!(sign_extend_subtable_16, SignExtendSubtable<Fr, 16>, Fr, 8, true);
    print_subtable_test!(
        truncate_overflow_subtable_8,
        TruncateOverflowSubtable<Fr, 8>,
        Fr,
        8,
        true
    );
    print_subtable_test!(truncate_overflow_subtable_32, TruncateOverflowSubtable<Fr, 32>, Fr, 8, true);
}
