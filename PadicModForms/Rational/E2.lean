/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.Rational.Eisenstein
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.CategoryTheory.Category.Init
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
import PadicModForms.ForMathlib.E2

/-!
# The rational q-expansion of `E2`

This file identifies the Fourier and ordinary level-one `q`-expansions of `E2` with the scalar
extension of `E₂Rat`.
-/

@[expose] public noncomputable section

open UpperHalfPlane PowerSeries ArithmeticFunction sigma ModularForm

namespace EisensteinSeries

/-- `E₂Rat` is the rational Fourier expansion of `E2`. -/
theorem E2_eq_tsum_E₂Rat (z : ℍ) :
    E2 z = ((coeff 0 E₂Rat : ℚ) : ℂ) + ∑' n : ℕ+, ((coeff n E₂Rat : ℚ) : ℂ) *
        Function.Periodic.qParam 1 z ^ (n : ℕ) := by
  simp [E2_eq_tsum_cexp, Function.Periodic.qParam, ← tsum_mul_left, sub_eq_add_neg,
    ← tsum_neg, mul_assoc]

/-- The ordinary level-one `q`-expansion of `E2` is the scalar extension of `E₂Rat` to `ℂ`. -/
theorem qExpansion_E2_eq_E₂Rat_map : qExpansion 1 EisensteinSeries.E2 =
    E₂Rat.map (algebraMap ℚ ℂ) := by
  ext m
  rw [coeff_map, E2_qExpansion_coeff]
  by_cases hm : m = 0
  · simp [hm]
  · simp [hm]

end EisensteinSeries
