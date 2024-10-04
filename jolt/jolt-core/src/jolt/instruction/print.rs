#[macro_export]
macro_rules! print_instruction_test {
    ($test_name:ident, $instruction:expr, $F:ty, $print_to_file:tt, $is_single_operand:tt) => {
        #[test]
        fn $test_name() {
            let output: Box<dyn std::io::Write> = if $print_to_file {
                let file_name = format!("{}_rust.txt", stringify!($test_name));
                // Let the folder be `../../validation`
                let path = std::env::current_dir()
                    .expect("Failed to get current directory")
                    .parent()
                    .and_then(|p| p.parent())
                    .expect("Failed to get parent directory")
                    .join("validation/instructions/")
                    .join(file_name);
                println!("Attempting to create file at: {:?}", path);
                Box::new(std::fs::File::create(&path).expect("Failed to create file"))
            } else {
                Box::new(std::io::stdout())
            };
            let mut writer = std::io::BufWriter::new(output);

            // Add some examples of 32-bit x and y for testing
            let examples_32: [(u64, u64); 20] = [
                (0, 0),                                         // Both zero
                (u32::MAX as u64, u32::MAX as u64),             // Both maximum value
                (1, 1),                                         // Both one
                ((u32::MAX / 2) as u64, (u32::MAX / 2) as u64), // Both middle value
                (u32::MIN as u64, u32::MAX as u64),             // Min and max
                (u32::MAX as u64, u32::MIN as u64),             // Max and min
                (0x80000000u64, 0x80000000u64), // Both minimum negative (signed interpretation)
                (0x7FFFFFFFu64, 0x7FFFFFFFu64), // Both maximum positive (signed interpretation)
                (0xAAAAAAAAu64, 0x55555555u64), // Alternating bit patterns
                (0x55555555u64, 0xAAAAAAAAu64), // Inverse alternating bit patterns
                (0xFFFF0000u64, 0x0000FFFFu64), // Upper half set, lower half set
                (0x0000FFFFu64, 0xFFFF0000u64), // Lower half set, upper half set
                (0x12345678u64, 0x87654321u64), // Random-looking values
                (0xDEADBEEFu64, 0xCAFEBABEu64), // Common debug values
                (0x00000001u64, 0xFFFFFFFFu64), // Smallest positive and largest value
                (0xFFFFFFFFu64, 0x00000001u64), // Largest value and smallest positive
                (0x80000000u64, 0x7FFFFFFFu64), // Minimum negative and maximum positive (signed)
                (0x01234567u64, 0x89ABCDEFu64), // Ascending and descending hex digits
                (0xF0F0F0F0u64, 0x0F0F0F0Fu64), // Alternating nibble patterns
                (0x00FF00FFu64, 0xFF00FF00u64), // Alternating byte patterns
            ];

            let examples_64 = [
                (0u64, 0u64),                             // Both zero
                (u64::MAX, u64::MAX),                     // Both maximum value
                (1u64, 1u64),                             // Both one
                (u64::MAX / 2, u64::MAX / 2),             // Both middle value
                (u64::MIN, u64::MAX),                     // Min and max
                (u64::MAX, u64::MIN),                     // Max and min
                (0x8000000000000000, 0x8000000000000000), // Both minimum negative (signed interpretation)
                (0x7FFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF), // Both maximum positive (signed interpretation)
                (0xAAAAAAAAAAAAAAAA, 0x5555555555555555), // Alternating bit patterns
                (0x5555555555555555, 0xAAAAAAAAAAAAAAAA), // Inverse alternating bit patterns
                (0xFFFFFFFF00000000, 0x00000000FFFFFFFF), // Upper half set, lower half set
                (0x00000000FFFFFFFF, 0xFFFFFFFF00000000), // Lower half set, upper half set
                (0x123456789ABCDEF0, 0xFEDCBA9876543210), // Random-looking values
                (0xDEADBEEFCAFEBABE, 0xBADC0FFEEBADF00D), // Common debug values
                (0x0000000000000001, 0xFFFFFFFFFFFFFFFF), // Smallest positive and largest value
                (0xFFFFFFFFFFFFFFFF, 0x0000000000000001), // Largest value and smallest positive
                (0x8000000000000000, 0x7FFFFFFFFFFFFFFF), // Minimum negative and maximum positive (signed)
                (0x0123456789ABCDEF, 0xFEDCBA9876543210), // Ascending and descending hex digits
                (0xF0F0F0F0F0F0F0F0, 0x0F0F0F0F0F0F0F0F), // Alternating nibble patterns
                (0x00FF00FF00FF00FF, 0xFF00FF00FF00FF00), // Alternating byte patterns
            ];

            // Determine if we test 32-bit or 64-bit
            let is_32_bit = stringify!($test_name).contains("32");
            let examples = if is_32_bit { examples_32 } else { examples_64 };

            for (x, y) in examples.iter() {
                create_and_write_instruction!($instruction, $is_single_operand, x, y, writer);
            }
        }
    };
}

#[macro_export]
macro_rules! create_and_write_instruction {
    ($instruction:expr, true, $x:expr, $y:expr, $writer:expr) => {
        let instruction = $instruction(*$x);
        let result = instruction.lookup_entry();
        writeln!($writer, "(({} . {}) . {})\n", $x, $y, result).expect("Failed to write");
    };
    ($instruction:expr, false, $x:expr, $y:expr, $writer:expr) => {
        let instruction = $instruction(*$x, *$y);
        let result = instruction.lookup_entry();
        writeln!($writer, "(({} . {}) . {})\n", $x, $y, result).expect("Failed to write");
    };
}

#[cfg(test)]
mod test {
    // use crate::field::JoltField;
    use crate::jolt::instruction::{
        add::ADDInstruction, and::ANDInstruction, beq::BEQInstruction, bge::BGEInstruction,
        bgeu::BGEUInstruction, bne::BNEInstruction, lb::LBInstruction, lh::LHInstruction,
        or::ORInstruction, sb::SBInstruction, sh::SHInstruction, sll::SLLInstruction,
        slt::SLTInstruction, sltu::SLTUInstruction, sra::SRAInstruction, srl::SRLInstruction,
        sub::SUBInstruction, sw::SWInstruction, xor::XORInstruction, JoltInstruction,
    };
    use crate::print_instruction_test;
    // use ark_bn254::Fr;
    use ark_serialize::Write;

    print_instruction_test!(add_instruction_32, ADDInstruction::<32>, Fr, true, false);

    print_instruction_test!(add_instruction_64, ADDInstruction::<64>, Fr, true, false);

    print_instruction_test!(and_instruction_32, ANDInstruction::<32>, Fr, true, false);

    print_instruction_test!(and_instruction_64, ANDInstruction::<64>, Fr, true, false);

    print_instruction_test!(beq_instruction_32, BEQInstruction::<32>, Fr, true, false);

    print_instruction_test!(beq_instruction_64, BEQInstruction::<64>, Fr, true, false);

    print_instruction_test!(bge_instruction_32, BGEInstruction::<32>, Fr, true, false);

    print_instruction_test!(bge_instruction_64, BGEInstruction::<64>, Fr, true, false);

    print_instruction_test!(bgeu_instruction_32, BGEUInstruction::<32>, Fr, true, false);

    print_instruction_test!(bgeu_instruction_64, BGEUInstruction::<64>, Fr, true, false);

    print_instruction_test!(bne_instruction_32, BNEInstruction::<32>, Fr, true, false);

    print_instruction_test!(bne_instruction_64, BNEInstruction::<64>, Fr, true, false);

    print_instruction_test!(lb_instruction_32, LBInstruction::<32>, Fr, true, true);

    print_instruction_test!(lb_instruction_64, LBInstruction::<64>, Fr, true, true);

    print_instruction_test!(lh_instruction_32, LHInstruction::<32>, Fr, true, true);

    print_instruction_test!(lh_instruction_64, LHInstruction::<64>, Fr, true, true);

    print_instruction_test!(or_instruction_32, ORInstruction::<32>, Fr, true, false);

    print_instruction_test!(or_instruction_64, ORInstruction::<64>, Fr, true, false);

    print_instruction_test!(sb_instruction_32, SBInstruction::<32>, Fr, true, true);

    print_instruction_test!(sb_instruction_64, SBInstruction::<64>, Fr, true, true);

    print_instruction_test!(sh_instruction_32, SHInstruction::<32>, Fr, true, true);

    print_instruction_test!(sh_instruction_64, SHInstruction::<64>, Fr, true, true);

    print_instruction_test!(sw_instruction_32, SWInstruction::<32>, Fr, true, true);

    print_instruction_test!(sw_instruction_64, SWInstruction::<64>, Fr, true, true);

    print_instruction_test!(slt_instruction_32, SLTInstruction::<32>, Fr, true, false);

    print_instruction_test!(slt_instruction_64, SLTInstruction::<64>, Fr, true, false);

    print_instruction_test!(sltu_instruction_32, SLTUInstruction::<32>, Fr, true, false);

    print_instruction_test!(sltu_instruction_64, SLTUInstruction::<64>, Fr, true, false);

    print_instruction_test!(sub_instruction_32, SUBInstruction::<32>, Fr, true, false);

    print_instruction_test!(sub_instruction_64, SUBInstruction::<64>, Fr, true, false);

    print_instruction_test!(xor_instruction_32, XORInstruction::<32>, Fr, true, false);

    print_instruction_test!(xor_instruction_64, XORInstruction::<64>, Fr, true, false);

    print_instruction_test!(sra_instruction_32, SRAInstruction::<32>, Fr, true, false);

    print_instruction_test!(sra_instruction_64, SRAInstruction::<64>, Fr, true, false);

    print_instruction_test!(sll_instruction_32, SLLInstruction::<32>, Fr, true, false);

    print_instruction_test!(sll_instruction_64, SLLInstruction::<64>, Fr, true, false);

    print_instruction_test!(srl_instruction_32, SRLInstruction::<32>, Fr, true, false);

    print_instruction_test!(srl_instruction_64, SRLInstruction::<64>, Fr, true, false);
}
