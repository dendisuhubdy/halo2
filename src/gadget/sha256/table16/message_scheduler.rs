use std::convert::TryInto;

use super::{
    super::BLOCK_SIZE, get_tag, interleave_u16_with_zeros, BlockWord, Gate, SpreadInputs,
    SpreadVar, Table16Chip, ROUNDS,
};
use crate::{
    arithmetic::FieldExt,
    gadget::{Cell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};

const DECOMPOSE_0_ROWS: usize = 2;
const DECOMPOSE_1_ROWS: usize = 2;
const DECOMPOSE_2_ROWS: usize = 3;
const DECOMPOSE_3_ROWS: usize = 2;
const SIGMA_0_V1_ROWS: usize = 4;
const SIGMA_0_V2_ROWS: usize = 4;
const SIGMA_1_V1_ROWS: usize = 4;
const SIGMA_1_V2_ROWS: usize = 4;

#[derive(Clone, Debug)]
pub(super) struct MessageWord {
    var: Cell,
    value: Option<u32>,
}

#[derive(Clone, Debug)]
pub(super) struct MessageScheduler {
    lookup: SpreadInputs,
    message_schedule: Column<Advice>,
    extras: [Column<Advice>; 6],

    /// Construct a word using reduce_4.
    s_word: Column<Fixed>,
    /// Decomposition gate for W_0, W_62, W_63.
    s_decompose_0: Column<Fixed>,
    /// Decomposition gate for W_[1..14]
    s_decompose_1: Column<Fixed>,
    /// Decomposition gate for W_[14..49]
    s_decompose_2: Column<Fixed>,
    /// Decomposition gate for W_[49..62]
    s_decompose_3: Column<Fixed>,
    /// sigma_0 gate for W_[1..14]
    s_lower_sigma_0: Column<Fixed>,
    /// sigma_1 gate for W_[49..62]
    s_lower_sigma_1: Column<Fixed>,
    /// sigma_0_v2 gate for W_[14..49]
    s_lower_sigma_0_v2: Column<Fixed>,
    /// sigma_1_v2 gate for W_[14..49]
    s_lower_sigma_1_v2: Column<Fixed>,
    /// Reduce output from each of the sigma gates
    s_reduce: Column<Fixed>,
    /// Range check and bit spread check on two 2-bit words
    s22: Column<Fixed>,
    /// Range check and bit spread check on a 2-bit words followed by a 3-bit word
    s23: Column<Fixed>,
}

impl MessageScheduler {
    /// Configures the message scheduler.
    ///
    /// `message_schedule` is the column into which the message schedule will be placed.
    /// The caller must create appropriate permutations in order to load schedule words
    /// into the compression rounds.
    ///
    /// `extras` contains columns that the message scheduler will only use for internal
    /// gates, and will not place any constraints on (such as lookup constraints) outside
    /// itself.
    pub(super) fn new<F: FieldExt>(
        meta: &mut ConstraintSystem<F>,
        lookup: SpreadInputs,
        message_schedule: Column<Advice>,
        extras: [Column<Advice>; 6],
    ) -> Self {
        // Create fixed columns for the selectors we will require.
        let s_word = meta.fixed_column();
        let s_decompose_0 = meta.fixed_column();
        let s_decompose_1 = meta.fixed_column();
        let s_decompose_2 = meta.fixed_column();
        let s_decompose_3 = meta.fixed_column();
        let s_lower_sigma_0 = meta.fixed_column();
        let s_lower_sigma_1 = meta.fixed_column();
        let s_lower_sigma_0_v2 = meta.fixed_column();
        let s_lower_sigma_1_v2 = meta.fixed_column();
        let s_reduce = meta.fixed_column();
        let s22 = meta.fixed_column();
        let s23 = meta.fixed_column();

        // Rename these here for ease of matching the gates to the specification.
        let a_0 = lookup.tag;
        let a_1 = lookup.dense;
        let a_2 = lookup.spread;
        let a_3 = extras[0];
        let a_4 = extras[1];
        let a_5 = message_schedule;
        let a_6 = extras[2];
        let a_7 = extras[3];
        let a_8 = extras[4];
        let a_9 = extras[5];

        // s_decompose_0 for all words
        meta.create_gate(|meta| {
            let s_decompose_0 = meta.query_fixed(s_decompose_0, 0);
            let lo = meta.query_advice(a_3, 0);
            let hi = meta.query_advice(a_4, 0);
            let word = meta.query_advice(a_5, 0);

            Gate::s_decompose_0(s_decompose_0, lo, hi, word).0
        });

        // s_decompose_1 for W_1 to W_13
        // (3, 4, 11, 14)-bit chunks
        meta.create_gate(|meta| {
            let s_decompose_1 = meta.query_fixed(s_decompose_1, 0);
            let a = meta.query_advice(a_3, 1); // 3-bit chunk
            let b = meta.query_advice(a_4, 1); // 4-bit chunk
            let c = meta.query_advice(a_1, 1); // 11-bit chunk
            let d = meta.query_advice(a_1, 0); // 14-bit chunk
            let word = meta.query_advice(a_5, 0);

            Gate::s_decompose_1(s_decompose_1, a, b, c, d, word).0
        });

        // s_decompose_2 for W_14 to W_48
        // (3, 4, 3, 7, 1, 1, 13)-bit chunks
        meta.create_gate(|meta| {
            let s_decompose_2 = meta.query_fixed(s_decompose_2, 0);
            let a = meta.query_advice(a_3, -1); // 3-bit chunk
            let b = meta.query_advice(a_1, 1); // 4-bit chunk
            let c = meta.query_advice(a_4, -1); // 3-bit chunk
            let d = meta.query_advice(a_1, 0); // 7-bit chunk
            let e = meta.query_advice(a_3, 1); // 1-bit chunk
            let f = meta.query_advice(a_4, 1); // 1-bit chunk
            let g = meta.query_advice(a_1, -1); // 13-bit chunk
            let word = meta.query_advice(a_5, 0);

            Gate::s_decompose_2(s_decompose_2, a, b, c, d, e, f, g, word).0
        });

        // s_decompose_3 for W_49 to W_61
        // (10, 7, 2, 13)-bit chunks
        meta.create_gate(|meta| {
            let s_decompose_3 = meta.query_fixed(s_decompose_3, 0);
            let a = meta.query_advice(a_3, 1); // 10-bit chunk
            let b = meta.query_advice(a_4, 1); // 7-bit chunk
            let c = meta.query_advice(a_1, 1); // 2-bit chunk
            let d = meta.query_advice(a_1, 0); // 13-bit chunk
            let word = meta.query_advice(a_5, 0);

            Gate::s_decompose_3(s_decompose_3, a, b, c, d, word).0
        });

        // s_word for W_16 to W_63
        meta.create_gate(|meta| {
            let s_word = meta.query_fixed(s_word, 0);

            let sigma_0_lo = meta.query_advice(a_6, -1);
            let sigma_1_lo = meta.query_advice(a_7, -1);
            let w_7_lo = meta.query_advice(a_8, -1);
            let w_16_lo = meta.query_advice(a_1, -1);

            let sigma_0_hi = meta.query_advice(a_6, 0);
            let sigma_1_hi = meta.query_advice(a_7, 0);
            let w_7_hi = meta.query_advice(a_8, 0);
            let w_16_hi = meta.query_advice(a_1, 0);

            let word = meta.query_advice(a_5, 0);
            let carry = meta.query_advice(a_9, 0);

            Gate::s_word(
                s_word, sigma_0_lo, sigma_1_lo, w_7_lo, w_16_lo, sigma_0_hi, sigma_1_hi, w_7_hi,
                w_16_hi, word, carry,
            )
            .0
        });

        // s22
        meta.create_gate(|meta| {
            let s22 = meta.query_fixed(s22, 0);
            let dense_0 = meta.query_advice(a_3, 0);
            let spread_0 = meta.query_advice(a_4, 0);
            let dense_1 = meta.query_advice(a_5, 0);
            let spread_1 = meta.query_advice(a_6, 0);

            Gate::s22(s22, dense_0, spread_0, dense_1, spread_1).0
        });

        // s23
        meta.create_gate(|meta| {
            let s23 = meta.query_fixed(s22, 0);
            let dense_0 = meta.query_advice(a_3, 0);
            let spread_0 = meta.query_advice(a_4, 0);
            let dense_1 = meta.query_advice(a_5, 0);
            let spread_1 = meta.query_advice(a_6, 0);

            Gate::s23(s23, dense_0, spread_0, dense_1, spread_1).0
        });

        // sigma_0 v1 on W_1 to W_13
        // (3, 4, 11, 14)-bit chunks
        meta.create_gate(|meta| {
            Gate::s_lower_sigma_0(
                meta.query_fixed(s_lower_sigma_0, 0), // s_lower_sigma_0
                meta.query_advice(a_2, -1),           // spread_r0_even
                meta.query_advice(a_2, 0),            // spread_r0_odd
                meta.query_advice(a_2, 1),            // spread_r1_even
                meta.query_advice(a_3, 0),            // spread_r1_odd
                meta.query_advice(a_6, 1),            // spread_a
                meta.query_advice(a_4, -1),           // spread_b_lo
                meta.query_advice(a_6, -1),           // spread_b_hi
                meta.query_advice(a_4, 0),            // spread_c
                meta.query_advice(a_5, 0),            // spread_d
            )
            .0
        });

        // sigma_0 v2 on W_14 to W_48
        // (3, 4, 3, 7, 1, 1, 13)-bit chunks
        meta.create_gate(|meta| {
            Gate::s_lower_sigma_0_v2(
                meta.query_fixed(s_lower_sigma_0_v2, 0), // s_lower_sigma_0_v2
                meta.query_advice(a_2, -1),              // spread_r0_even
                meta.query_advice(a_2, 0),               // spread_r0_odd
                meta.query_advice(a_2, 1),               // spread_r1_even
                meta.query_advice(a_3, 0),               // spread_r1_odd
                meta.query_advice(a_6, -1),              // spread_a
                meta.query_advice(a_4, -1),              // spread_b_lo
                meta.query_advice(a_4, 1),               // spread_b_hi
                meta.query_advice(a_6, 1),               // spread_c
                meta.query_advice(a_4, 0),               // spread_d
                meta.query_advice(a_7, -1),              // spread_e
                meta.query_advice(a_7, 1),               // spread_f
                meta.query_advice(a_5, 0),               // spread_g
            )
            .0
        });

        // sigma_1 v2 on W_14 to W_48
        // (3, 4, 3, 7, 1, 1, 13)-bit chunks
        meta.create_gate(|meta| {
            Gate::s_lower_sigma_1_v2(
                meta.query_fixed(s_lower_sigma_1_v2, 0), // s_lower_sigma_1_v2
                meta.query_advice(a_2, -1),              // spread_r0_even
                meta.query_advice(a_2, 0),               // spread_r0_odd
                meta.query_advice(a_2, 1),               // spread_r1_even
                meta.query_advice(a_3, 0),               // spread_r1_odd
                meta.query_advice(a_6, -1),              // spread_a
                meta.query_advice(a_4, -1),              // spread_b_lo
                meta.query_advice(a_4, 1),               // spread_b_hi
                meta.query_advice(a_6, 1),               // spread_c
                meta.query_advice(a_4, 0),               // spread_d
                meta.query_advice(a_7, -1),              // spread_e
                meta.query_advice(a_7, 1),               // spread_f
                meta.query_advice(a_5, 0),               // spread_g
            )
            .0
        });

        // sigma_1 v1 on W_49 to W_61
        // (10, 7, 2, 13)-bit chunks
        meta.create_gate(|meta| {
            Gate::s_lower_sigma_1(
                meta.query_fixed(s_lower_sigma_1, 0), // s_lower_sigma_1
                meta.query_advice(a_2, -1),           // spread_r0_even
                meta.query_advice(a_2, 0),            // spread_r0_odd
                meta.query_advice(a_2, 1),            // spread_r1_even
                meta.query_advice(a_3, 0),            // spread_r1_odd
                meta.query_advice(a_4, 0),            // spread_a
                meta.query_advice(a_4, -1),           // spread_b_lo
                meta.query_advice(a_6, -1),           // spread_b_mid
                meta.query_advice(a_4, 1),            // spread_b_hi
                meta.query_advice(a_6, 1),            // spread_c
                meta.query_advice(a_5, 0),            // spread_d
            )
            .0
        });

        MessageScheduler {
            lookup,
            message_schedule,
            extras,
            s_word,
            s_decompose_0,
            s_decompose_1,
            s_decompose_2,
            s_decompose_3,
            s_lower_sigma_0,
            s_lower_sigma_1,
            s_lower_sigma_0_v2,
            s_lower_sigma_1_v2,
            s_reduce,
            s22,
            s23,
        }
    }

    pub(super) fn process<F: FieldExt>(
        &self,
        layouter: &mut impl Layouter<Table16Chip<F>>,
        input: [BlockWord; BLOCK_SIZE],
    ) -> Result<[MessageWord; ROUNDS], Error> {
        let mut w = Vec::with_capacity(ROUNDS);

        struct SpreadWord {
            tag: u8,
            dense: u16,
            spread: u32,
        }

        // Returns tag, dense, spread for a 16-bit word
        fn get_spread_word(word: u16) -> SpreadWord {
            SpreadWord {
                tag: get_tag(word),
                dense: word,
                spread: interleave_u16_with_zeros(word),
            }
        }

        // Get (tag, dense, spread) for lo and hi bits of each input word
        let input_spread: Vec<(SpreadWord, SpreadWord)> = input
            .iter()
            .map(|word| {
                let word = word.value.unwrap();
                let lo = get_spread_word(word as u16);
                let hi = get_spread_word((word >> 16) as u16);
                (lo, hi)
            })
            .collect();

        layouter.assign_region(|mut region| {
            // Assign W_0
            {
                let var = region.assign_advice(self.message_schedule, 0, || {
                    input[0]
                        .value
                        .map(|v| F::from_u64(v as u64))
                        .ok_or(Error::SynthesisError)
                })?;

                // Decompose W_0
                region.assign_fixed(self.s_decompose_0, 0, || Ok(F::one()))?;
                // Lower 16-bit lookup
                let lo_W_0 = SpreadVar::new(
                    &mut region,
                    &self.lookup,
                    0,
                    input_spread[0].0.tag,
                    Some(input_spread[0].0.dense),
                    Some(input_spread[0].0.spread),
                )?;
                // Higher 16-bit lookup
                let hi_W_0 = SpreadVar::new(
                    &mut region,
                    &self.lookup,
                    0,
                    input_spread[0].1.tag,
                    Some(input_spread[0].1.dense),
                    Some(input_spread[0].1.spread),
                )?;

                w.push(MessageWord {
                    var,
                    value: input[0].value,
                });
            }

            // Assign W_1 to W_13
            for i in 1..14 {
                let var = region.assign_advice(
                    self.message_schedule,
                    2 + (DECOMPOSE_1_ROWS + SIGMA_0_V1_ROWS) * (i - 1),
                    || {
                        input[i]
                            .value
                            .map(|v| F::from_u64(v as u64))
                            .ok_or(Error::SynthesisError)
                    },
                )?;
                w.push(MessageWord {
                    var,
                    value: input[i].value,
                });
            }

            // Assign W_14 and W_15
            const starting_row: usize = 2 + 13 * (DECOMPOSE_1_ROWS + SIGMA_0_V1_ROWS);
            for i in 14..16 {
                let var = region.assign_advice(
                    self.message_schedule,
                    starting_row
                        + (DECOMPOSE_2_ROWS + SIGMA_0_V2_ROWS + SIGMA_1_V2_ROWS) * (i - 14)
                        + 1,
                    || {
                        input[i]
                            .value
                            .map(|v| F::from_u64(v as u64))
                            .ok_or(Error::SynthesisError)
                    },
                )?;
                w.push(MessageWord {
                    var,
                    value: input[i].value,
                });
            }

            // sigma_0 v1 on W_1 to W_13
            // (3, 4, 11, 14)-bit chunks
            for i in 1..14 {}

            // sigma_0 v2 and sigma_1 v2 on W_14 to W_48
            // (3, 4, 3, 7, 1, 1, 13)-bit chunks
            for i in 14..49 {}

            // sigma_1 v1 on W_49 to W_61
            // (10, 7, 2, 13)-bit chunks
            for i in 49..62 {}

            // s_word
            for i in 17..64 {}

            Ok(())
        })?;

        Ok(w.try_into().unwrap())
    }
}
