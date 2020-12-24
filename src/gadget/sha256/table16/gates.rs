use crate::arithmetic::FieldExt;
use crate::plonk::Expression;

pub struct Gate<F: FieldExt>(pub Expression<F>);

impl<F: FieldExt> Gate<F> {
    const ones: Expression<F> = Expression::Ones();

    // Helper gates
    fn lagrange_interpolate(
        var: Expression<F>,
        points: Vec<u16>,
        evals: Vec<u32>,
    ) -> (F, Expression<F>) {
        assert_eq!(points.len(), evals.len());
        let deg = points.len();

        fn factorial(n: u64) -> u64 {
            if n < 2 {
                1
            } else {
                n * factorial(n - 1)
            }
        }

        // Scale the whole expression by factor to avoid divisions
        let factor = factorial(points.len() as u64);

        let numerator = |var: Expression<F>, eval: u32, idx: u64| {
            let mut expr = Self::ones;
            for i in 0..deg {
                if i as u64 != idx {
                    expr = expr * (Self::ones * (-F::one()) * F::from_u64(idx) + var.clone());
                }
            }
            expr * F::from_u64(eval.into())
        };
        let denominator = |idx: i32| {
            let mut denom: i32 = 1;
            for i in 0..deg {
                if i as i32 != idx {
                    denom *= idx - i as i32
                }
            }
            if denom < 0 {
                -F::one() * F::from_u64(factor / -denom as u64)
            } else {
                F::from_u64(factor / denom as u64)
            }
        };

        let mut expr = Self::ones;
        for ((idx, point), eval) in points.iter().enumerate().zip(evals.iter()) {
            expr = expr + numerator(var.clone(), *eval, idx as u64) * denominator(idx as i32)
        }

        (F::from_u64(factor), expr)
    }

    fn range_check(value: Expression<F>, lower_range: u64, upper_range: u64) -> Expression<F> {
        let mut expr = Self::ones;
        for i in lower_range..(upper_range + 1) {
            expr = expr * (Self::ones * (-F::one()) * F::from_u64(i) + value.clone())
        }
        expr
    }

    // 2-bit range check
    fn two_bit_range_check(value: Expression<F>) -> Expression<F> {
        Self::range_check(value, 0, (1 << 2) - 1)
    }

    // 2-bit spread interpolation
    fn two_bit_spread(dense: Expression<F>, spread: Expression<F>) -> Expression<F> {
        let (factor, lagrange_poly) = Self::lagrange_interpolate(
            dense,
            vec![0b00, 0b01, 0b10, 0b11],
            vec![0b0000, 0b0001, 0b0100, 0b0101],
        );

        lagrange_poly + (spread * factor * (-F::one()))
    }

    // 3-bit range check
    fn three_bit_range_check(value: Expression<F>) -> Expression<F> {
        Self::range_check(value, 0, (1 << 3) - 1)
    }

    // 3-bit spread
    fn three_bit_spread(dense: Expression<F>, spread: Expression<F>) -> Expression<F> {
        let (factor, lagrange_poly) = Self::lagrange_interpolate(
            dense,
            vec![0b000, 0b001, 0b010, 0b011, 0b100, 0b101, 0b110, 0b111],
            vec![
                0b000000, 0b000001, 0b000100, 0b000101, 0b010000, 0b010001, 0b010100, 0b010101,
            ],
        );

        lagrange_poly + (spread * factor * (-F::one()))
    }

    /// Spread and range check on two 2-bit words
    pub fn s22(
        s22: Expression<F>,
        dense_0: Expression<F>,
        spread_0: Expression<F>,
        dense_1: Expression<F>,
        spread_1: Expression<F>,
    ) -> Self {
        let two_bit_range_check_0 = Self::two_bit_range_check(dense_0.clone());
        let two_bit_range_check_1 = Self::two_bit_range_check(dense_1.clone());
        let two_bit_spread_0 = Self::two_bit_spread(dense_0, spread_0);
        let two_bit_spread_1 = Self::two_bit_spread(dense_1, spread_1);

        Gate(two_bit_range_check_0 + two_bit_range_check_1 + two_bit_spread_0 + two_bit_spread_1)
    }

    /// Spread and range check on a 2-bit word and a 3-bit word
    pub fn s23(
        s23: Expression<F>,
        dense_0: Expression<F>,
        spread_0: Expression<F>,
        dense_1: Expression<F>,
        spread_1: Expression<F>,
    ) -> Self {
        let two_bit_range_check = Self::two_bit_range_check(dense_0.clone());
        let three_bit_range_check = Self::three_bit_range_check(dense_1.clone());
        let two_bit_spread = Self::two_bit_spread(dense_0, spread_0);
        let three_bit_spread = Self::three_bit_spread(dense_1, spread_1);

        Gate(two_bit_range_check + three_bit_range_check + two_bit_spread + three_bit_spread)
    }

    // s_decompose_0 for all words
    pub fn s_decompose_0(
        s_decompose_0: Expression<F>,
        lo: Expression<F>,
        hi: Expression<F>,
        word: Expression<F>,
    ) -> Self {
        Gate(s_decompose_0 * (lo + hi * F::from_u64(1 << 16) + word * (-F::one())))
    }

    // s_decompose_1 for W_1 to W_13
    // (3, 4, 11, 14)-bit chunks
    pub fn s_decompose_1(
        s_decompose_1: Expression<F>,
        a: Expression<F>,
        b: Expression<F>,
        c: Expression<F>,
        d: Expression<F>,
        word: Expression<F>,
    ) -> Self {
        Gate(
            s_decompose_1
                * (a + b * F::from_u64(1 << 3)
                    + c * F::from_u64(1 << 7)
                    + d * F::from_u64(1 << 18)
                    + word * (-F::one())),
        )
    }

    // s_decompose_2 for W_14 to W_48
    // (3, 4, 3, 7, 1, 1, 13)-bit chunks
    pub fn s_decompose_2(
        s_decompose_2: Expression<F>,
        a: Expression<F>,
        b: Expression<F>,
        c: Expression<F>,
        d: Expression<F>,
        e: Expression<F>,
        f: Expression<F>,
        g: Expression<F>,
        word: Expression<F>,
    ) -> Self {
        Gate(
            s_decompose_2
                * (a + b * F::from_u64(1 << 3)
                    + c * F::from_u64(1 << 7)
                    + d * F::from_u64(1 << 10)
                    + e * F::from_u64(1 << 17)
                    + f * F::from_u64(1 << 18)
                    + g * F::from_u64(1 << 19)
                    + word * (-F::one())),
        )
    }

    // s_decompose_3 for W_49 to W_61
    // (10, 7, 2, 13)-bit chunks
    pub fn s_decompose_3(
        s_decompose_3: Expression<F>,
        a: Expression<F>,
        b: Expression<F>,
        c: Expression<F>,
        d: Expression<F>,
        word: Expression<F>,
    ) -> Self {
        Gate(
            s_decompose_3
                * (a + b * F::from_u64(1 << 10)
                    + c * F::from_u64(1 << 17)
                    + d * F::from_u64(1 << 19)
                    + word * (-F::one())),
        )
    }

    // s_word for W_16 to W_63
    pub fn s_word(
        s_word: Expression<F>,
        sigma_0_lo: Expression<F>,
        sigma_1_lo: Expression<F>,
        w_7_lo: Expression<F>,
        w_16_lo: Expression<F>,
        sigma_0_hi: Expression<F>,
        sigma_1_hi: Expression<F>,
        w_7_hi: Expression<F>,
        w_16_hi: Expression<F>,
        word: Expression<F>,
        carry: Expression<F>,
    ) -> Self {
        let lo = sigma_0_lo + sigma_1_lo + w_7_lo + w_16_lo;
        let hi = sigma_0_hi + sigma_1_hi + w_7_hi + w_16_hi;

        let word_check = lo
            + hi * F::from_u64(1 << 16)
            + word * (-F::one())
            + carry.clone() * (-F::one()) * F::from_u64(1 << 32);
        let carry_check = Self::range_check(carry, 0, 3);

        Gate(s_word * (word_check + carry_check))
    }

    // sigma_0 v1 on W_1 to W_13
    // (3, 4, 11, 14)-bit chunks
    pub fn s_lower_sigma_0(
        s_lower_sigma_0: Expression<F>,
        spread_r0_even: Expression<F>,
        spread_r0_odd: Expression<F>,
        spread_r1_even: Expression<F>,
        spread_r1_odd: Expression<F>,
        spread_a: Expression<F>,
        spread_b_lo: Expression<F>,
        spread_b_hi: Expression<F>,
        spread_c: Expression<F>,
        spread_d: Expression<F>,
    ) -> Self {
        let spread_witness = spread_r0_even
            + spread_r0_odd * F::from_u64(2)
            + (spread_r1_even + spread_r1_odd * F::from_u64(2)) * F::from_u64(1 << 32);
        let xor_0 = spread_b_lo.clone()
            + spread_b_hi.clone() * F::from_u64(1 << 4)
            + spread_c.clone() * F::from_u64(1 << 8)
            + spread_d.clone() * F::from_u64(1 << 30);
        let xor_1 = spread_c.clone()
            + spread_d.clone() * F::from_u64(1 << 22)
            + spread_a.clone() * F::from_u64(1 << 50)
            + spread_b_lo.clone() * F::from_u64(1 << 56)
            + spread_b_hi.clone() * F::from_u64(1 << 60);
        let xor_2 = spread_d
            + spread_a * F::from_u64(1 << 28)
            + spread_b_lo * F::from_u64(1 << 34)
            + spread_b_hi * F::from_u64(1 << 38)
            + spread_c * F::from_u64(1 << 42);
        let xor = xor_0 + xor_1 + xor_2;

        Gate(spread_witness + (xor * -F::one()))
    }

    // sigma_1 v1 on W_49 to W_61
    // (10, 7, 2, 13)-bit chunks
    pub fn s_lower_sigma_1(
        s_lower_sigma_0: Expression<F>,
        spread_r0_even: Expression<F>,
        spread_r0_odd: Expression<F>,
        spread_r1_even: Expression<F>,
        spread_r1_odd: Expression<F>,
        spread_a: Expression<F>,
        spread_b_lo: Expression<F>,
        spread_b_mid: Expression<F>,
        spread_b_hi: Expression<F>,
        spread_c: Expression<F>,
        spread_d: Expression<F>,
    ) -> Self {
        let spread_witness = spread_r0_even
            + spread_r0_odd * F::from_u64(2)
            + (spread_r1_even + spread_r1_odd * F::from_u64(2)) * F::from_u64(1 << 32);
        let xor_0 = spread_b_lo.clone()
            + spread_b_mid.clone() * F::from_u64(1 << 4)
            + spread_b_hi.clone() * F::from_u64(1 << 8)
            + spread_c.clone() * F::from_u64(1 << 14)
            + spread_d.clone() * F::from_u64(1 << 18);
        let xor_1 = spread_c.clone()
            + spread_d.clone() * F::from_u64(1 << 4)
            + spread_a.clone() * F::from_u64(1 << 30)
            + spread_b_lo.clone() * F::from_u64(1 << 50)
            + spread_b_mid.clone() * F::from_u64(1 << 54)
            + spread_b_hi.clone() * F::from_u64(1 << 58);
        let xor_2 = spread_d.clone()
            + spread_a.clone() * F::from_u64(1 << 26)
            + spread_b_lo.clone() * F::from_u64(1 << 46)
            + spread_b_mid.clone() * F::from_u64(1 << 50)
            + spread_b_hi.clone() * F::from_u64(1 << 54)
            + spread_c.clone() * F::from_u64(1 << 60);
        let xor = xor_0 + xor_1 + xor_2;

        Gate(spread_witness + (xor * -F::one()))
    }

    // sigma_0 v2 on W_14 to W_48
    // (3, 4, 3, 7, 1, 1, 13)-bit chunks
    pub fn s_lower_sigma_0_v2(
        s_lower_sigma_0_v2: Expression<F>,
        spread_r0_even: Expression<F>,
        spread_r0_odd: Expression<F>,
        spread_r1_even: Expression<F>,
        spread_r1_odd: Expression<F>,
        spread_a: Expression<F>,
        spread_b_lo: Expression<F>,
        spread_b_hi: Expression<F>,
        spread_c: Expression<F>,
        spread_d: Expression<F>,
        spread_e: Expression<F>,
        spread_f: Expression<F>,
        spread_g: Expression<F>,
    ) -> Self {
        let spread_witness = spread_r0_even
            + spread_r0_odd * F::from_u64(2)
            + (spread_r1_even + spread_r1_odd * F::from_u64(2)) * F::from_u64(1 << 32);
        let xor_0 = spread_b_lo.clone()
            + spread_b_hi.clone() * F::from_u64(1 << 4)
            + spread_c.clone() * F::from_u64(1 << 8)
            + spread_d.clone() * F::from_u64(1 << 14)
            + spread_e.clone() * F::from_u64(1 << 28)
            + spread_f.clone() * F::from_u64(1 << 30)
            + spread_g.clone() * F::from_u64(1 << 32);
        let xor_1 = spread_c.clone()
            + spread_d.clone() * F::from_u64(1 << 6)
            + spread_e.clone() * F::from_u64(1 << 20)
            + spread_f.clone() * F::from_u64(1 << 22)
            + spread_g.clone() * F::from_u64(1 << 24)
            + spread_a.clone() * F::from_u64(1 << 50)
            + spread_b_lo.clone() * F::from_u64(1 << 56)
            + spread_b_hi.clone() * F::from_u64(1 << 60);
        let xor_2 = spread_f
            + spread_g * F::from_u64(1 << 2)
            + spread_a * F::from_u64(1 << 28)
            + spread_b_lo * F::from_u64(1 << 34)
            + spread_b_hi * F::from_u64(1 << 38)
            + spread_c * F::from_u64(1 << 42)
            + spread_d * F::from_u64(1 << 48)
            + spread_e * F::from_u64(1 << 62);
        let xor = xor_0 + xor_1 + xor_2;

        Gate(spread_witness + (xor * -F::one()))
    }

    // sigma_1 v2 on W_14 to W_48
    // (3, 4, 3, 7, 1, 1, 13)-bit chunks
    pub fn s_lower_sigma_1_v2(
        s_lower_sigma_1_v2: Expression<F>,
        spread_r0_even: Expression<F>,
        spread_r0_odd: Expression<F>,
        spread_r1_even: Expression<F>,
        spread_r1_odd: Expression<F>,
        spread_a: Expression<F>,
        spread_b_lo: Expression<F>,
        spread_b_hi: Expression<F>,
        spread_c: Expression<F>,
        spread_d: Expression<F>,
        spread_e: Expression<F>,
        spread_f: Expression<F>,
        spread_g: Expression<F>,
    ) -> Self {
        let spread_witness = spread_r0_even
            + spread_r0_odd * F::from_u64(2)
            + (spread_r1_even + spread_r1_odd * F::from_u64(2)) * F::from_u64(1 << 32);
        let xor_0 = spread_d.clone()
            + spread_e.clone() * F::from_u64(1 << 14)
            + spread_f.clone() * F::from_u64(1 << 16)
            + spread_g.clone() * F::from_u64(1 << 18);
        let xor_1 = spread_e.clone()
            + spread_f.clone() * F::from_u64(1 << 2)
            + spread_g.clone() * F::from_u64(1 << 4)
            + spread_a.clone() * F::from_u64(1 << 30)
            + spread_b_lo.clone() * F::from_u64(1 << 36)
            + spread_b_hi.clone() * F::from_u64(1 << 40)
            + spread_c.clone() * F::from_u64(1 << 44)
            + spread_d.clone() * F::from_u64(1 << 50);
        let xor_2 = spread_g
            + spread_a * F::from_u64(1 << 26)
            + spread_b_lo * F::from_u64(1 << 32)
            + spread_b_hi * F::from_u64(1 << 36)
            + spread_c * F::from_u64(1 << 40)
            + spread_d * F::from_u64(1 << 46)
            + spread_e * F::from_u64(1 << 60)
            + spread_f * F::from_u64(1 << 62);
        let xor = xor_0 + xor_1 + xor_2;

        Gate(spread_witness + (xor * -F::one()))
    }
}
