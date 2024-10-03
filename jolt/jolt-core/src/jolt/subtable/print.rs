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
                // Let the folder be `../../validation`
                let path = std::env::current_dir()
                    .expect("Failed to get current directory")
                    .parent()
                    .and_then(|p| p.parent())
                    .expect("Failed to get parent directory")
                    .join("validation")
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
            println!(
                "This is either identity, sign_extend, or truncate_overflow. Printing table of format \"(x . val)\"..."
            );

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

    // # subtable_enum!(
    //     #   RV32ISubtables,
    //     #   AND: AndSubtable<F>,
    //     #   EQ_ABS: EqAbsSubtable<F>,
    //     #   EQ: EqSubtable<F>,
    //     #   LEFT_MSB: LeftMSBSubtable<F>,
    //     #   RIGHT_MSB: RightMSBSubtable<F>,
    //     #   IDENTITY: IdentitySubtable<F>,
    //     #   LT_ABS: LtAbsSubtable<F>,
    //     #   LTU: LtuSubtable<F>,
    //     #   OR: OrSubtable<F>,
    //     #   SIGN_EXTEND_8: SignExtendSubtable<F, 8>,
    //     #   SIGN_EXTEND_16: SignExtendSubtable<F, 16>,
    //     #   SLL0: SllSubtable<F, 0, WORD_SIZE>,
    //     #   SLL1: SllSubtable<F, 1, WORD_SIZE>,
    //     #   SLL2: SllSubtable<F, 2, WORD_SIZE>,
    //     #   SLL3: SllSubtable<F, 3, WORD_SIZE>,
    //     #   SRA_SIGN: SraSignSubtable<F, WORD_SIZE>,
    //     #   SRL0: SrlSubtable<F, 0, WORD_SIZE>,
    //     #   SRL1: SrlSubtable<F, 1, WORD_SIZE>,
    //     #   SRL2: SrlSubtable<F, 2, WORD_SIZE>,
    //     #   SRL3: SrlSubtable<F, 3, WORD_SIZE>,
    //     #   TRUNCATE: TruncateOverflowSubtable<F, WORD_SIZE>,
    //     #   TRUNCATE_BYTE: TruncateOverflowSubtable<F, 8>,
    //     #   XOR: XorSubtable<F>,
    //     #   LEFT_IS_ZERO: LeftIsZeroSubtable<F>,
    //     #   RIGHT_IS_ZERO: RightIsZeroSubtable<F>,
    //     #   DIV_BY_ZERO: DivByZeroSubtable<F>
    //     # );

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
    print_subtable_test!(sll_subtable_0_32, SllSubtable<Fr, 0, 32>, Fr, 8, true);
    print_subtable_test!(sll_subtable_1_32, SllSubtable<Fr, 1, 32>, Fr, 8, true);
    print_subtable_test!(sll_subtable_2_32, SllSubtable<Fr, 2, 32>, Fr, 8, true);
    print_subtable_test!(sll_subtable_3_32, SllSubtable<Fr, 3, 32>, Fr, 8, true);
    print_subtable_test!(sra_sign_subtable_8, SraSignSubtable<Fr, 8>, Fr, 8, true);
    print_subtable_test!(srl_subtable_0_32, SrlSubtable<Fr, 0, 32>, Fr, 8, true);
    print_subtable_test!(srl_subtable_1_32, SrlSubtable<Fr, 1, 32>, Fr, 8, true);
    print_subtable_test!(srl_subtable_2_32, SrlSubtable<Fr, 2, 32>, Fr, 8, true);
    print_subtable_test!(srl_subtable_3_32, SrlSubtable<Fr, 3, 32>, Fr, 8, true);
    print_subtable_test!(xor_subtable, XorSubtable<Fr>, Fr, 8, true);

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
