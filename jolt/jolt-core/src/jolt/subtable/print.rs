#[macro_export]
macro_rules! print_subtable_test {
    ($test_name:ident, $subtable_type:ty, $F:ty, $m:expr, $print_to_file:expr $(, $file_name:expr)?) => {
        #[test]
        fn $test_name() {
            let m = $m;
            let M = 1 << (2 * m);
            let subtable = <$subtable_type>::new();
            let materialized = subtable.materialize(M);

            let output: Box<dyn std::io::Write> = if $print_to_file {
                let file_name = "foo";
                // $($file_name.to_string())
                //     .unwrap_or_else(|| format!("{}.txt", stringify!($test_name)));
                let path = std::env::current_dir()
                    .expect("Failed to get current directory")
                    .join(file_name);
                println!("Attempting to create file at: {:?}", path);
                Box::new(std::fs::File::create(&path).expect("Failed to create file"))
            } else {
                Box::new(std::io::stdout())
            };
            let mut writer = std::io::BufWriter::new(output);

            // We want to print the subtable in the same format as ACL2
            // which is `((x . y) . val)` for decreasing x and y.
            for idx in (0..M).rev() {
                let entry = &materialized[idx];
                let (x, y) = $crate::utils::split_bits(idx, m);
                writeln!(writer, "(({} . {}) . {})", x, y, entry.to_u64().unwrap())
                    .expect("Failed to write");
            }
        }
    };
}

#[cfg(test)]
mod print {
    use crate::field::JoltField;
    use crate::jolt::subtable::{
        and::AndSubtable, div_by_zero::DivByZeroSubtable, eq::EqSubtable, eq_abs::EqAbsSubtable,
        identity::IdentitySubtable, left_is_zero::LeftIsZeroSubtable, left_msb::LeftMSBSubtable,
        lt_abs::LtAbsSubtable, ltu::LtuSubtable, or::OrSubtable,
        right_is_zero::RightIsZeroSubtable, right_msb::RightMSBSubtable,
        sign_extend::SignExtendSubtable, sll::SllSubtable, sra_sign::SraSignSubtable,
        srl::SrlSubtable, truncate_overflow::TruncateOverflowSubtable, xor::XorSubtable,
        LassoSubtable,
    };
    use ark_bn254::Fr;
    use ark_serialize::Write;

    print_subtable_test!(and_subtable, AndSubtable<Fr>, Fr, 2, false);
    print_subtable_test!(div_by_zero_subtable, DivByZeroSubtable<Fr>, Fr, 2, false);
    print_subtable_test!(eq_subtable, EqSubtable<Fr>, Fr, 2, false);
    print_subtable_test!(eq_abs_subtable, EqAbsSubtable<Fr>, Fr, 2, false);
    print_subtable_test!(identity_subtable, IdentitySubtable<Fr>, Fr, 2, false);
    print_subtable_test!(left_is_zero_subtable, LeftIsZeroSubtable<Fr>, Fr, 2, false);
    print_subtable_test!(left_msb_subtable, LeftMSBSubtable<Fr>, Fr, 2, false);
    print_subtable_test!(lt_abs_subtable, LtAbsSubtable<Fr>, Fr, 2, false);
    print_subtable_test!(ltu_subtable, LtuSubtable<Fr>, Fr, 2, false);
    print_subtable_test!(or_subtable, OrSubtable<Fr>, Fr, 2, false);
    print_subtable_test!(
        right_is_zero_subtable,
        RightIsZeroSubtable<Fr>,
        Fr,
        2,
        false
    );
    print_subtable_test!(right_msb_subtable, RightMSBSubtable<Fr>, Fr, 2, false);
    print_subtable_test!(sign_extend_subtable, SignExtendSubtable<Fr, 8>, Fr, 2, false);
    print_subtable_test!(sll_subtable, SllSubtable<Fr, 0, 32>, Fr, 2, false);
    print_subtable_test!(sra_sign_subtable, SraSignSubtable<Fr, 8>, Fr, 2, false);
    print_subtable_test!(srl_subtable, SrlSubtable<Fr, 0, 32>, Fr, 2, false);
    print_subtable_test!(
        truncate_overflow_subtable,
        TruncateOverflowSubtable<Fr, 8>,
        Fr,
        2,
        false
    );
    print_subtable_test!(xor_subtable, XorSubtable<Fr>, Fr, 2, false);
}
