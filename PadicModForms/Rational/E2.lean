/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.E2
public import PadicModForms.Rational.Eisenstein

/-!
# The rational q-expansion of `E2`

This file identifies the Fourier and ordinary level-one `q`-expansions of `E2` with the scalar
extension of `E_rat 2`.
-/

@[expose] public noncomputable section

open UpperHalfPlane PowerSeries ArithmeticFunction sigma ModularForm

namespace EisensteinSeries

/-- `E_rat 2` is the rational Fourier expansion of `E2`. -/
theorem E2_eq_tsum_E_rat (z : ℍ) :
    E2 z = ((coeff 0 (E_rat 2) : ℚ) : ℂ) + ∑' n : ℕ+, ((coeff n (E_rat 2) : ℚ) : ℂ) *
        Function.Periodic.qParam 1 z ^ (n : ℕ) := by
  simp only [E2_eq_tsum_cexp, coeff_E_rat, reduceIte, Rat.cast_one, PNat.ne_zero, Nat.cast_ofNat,
    bernoulli_two, div_inv_eq_mul, Nat.add_one_sub_one, neg_mul, Rat.cast_neg, Rat.cast_mul,
    Rat.cast_ofNat, Rat.cast_natCast, Function.Periodic.qParam, Complex.ofReal_one, div_one,
    ← tsum_mul_left, sub_eq_add_neg, ← tsum_neg]
  congr 1
  exact tsum_congr (fun n ↦ by ring)

/-- The ordinary level-one `q`-expansion of `E2` is the scalar extension of `E_rat 2` to `ℂ`. -/
theorem qExpansion_E2_eq_E_rat_map : qExpansion 1 EisensteinSeries.E2 =
    (EisensteinSeries.E_rat 2).map (algebraMap ℚ ℂ) := by
  ext m
  rw [coeff_map, E2_qExpansion_coeff]
  by_cases hm : m = 0
  · simp [hm]
  · simp [E_rat, hm, bernoulli_two]
    norm_num

end EisensteinSeries
