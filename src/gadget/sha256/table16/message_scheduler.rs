use std::convert::TryInto;

use super::{
    super::BLOCK_SIZE, get_tag, interleave_u16_with_zeros, BlockWord, SpreadInputs, SpreadVar,
    Table16Chip, ROUNDS,
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

        // meta.create_gate(|meta| {});

        MessageScheduler {
            lookup,
            message_schedule,
            extras,
            s_word,
            s_decompose_0,
            s_decompose_1,
            s_decompose_2,
            s_decompose_3,
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

            Ok(())
        })?;

        Ok(w.try_into().unwrap())
    }
}
