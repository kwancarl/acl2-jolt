pub fn to_ram_address(index: usize) -> usize {
    index * constants::BYTES_PER_INSTRUCTION + constants::RAM_START_ADDRESS as usize
}

pub mod attributes;
pub mod constants;
pub mod parallel;
pub mod rv_trace;
pub mod serializable;
