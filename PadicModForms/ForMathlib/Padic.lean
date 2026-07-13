/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib

/-!
# Auxiliary results on the additive valuation on `ℚ_[p]`
-/

@[expose] public section

variable {p : ℕ} [hp : Fact p.Prime]

namespace Padic

-- should go to Mathlib.NumberTheory.Padics.PadicNumbers
theorem intCast_le_addValuation_iff_norm_le_pow (k : ℤ) (x : ℚ_[p]) :
    (k : EInt) ≤ (Padic.addValuation x : EInt) ↔ ‖x‖ ≤ (p : ℝ) ^ (-k) := by
  by_cases hx : x = 0
  · simp [hx, Padic.addValuation, zpow_nonneg (p.cast_nonneg : (0 : ℝ) ≤ p)]
  · rw [Padic.addValuation.apply hx, Padic.norm_eq_zpow_neg_valuation hx, zpow_le_zpow_iff_right₀
      (mod_cast hp.1.one_lt), WithBotTop.coe, Function.comp_apply, WithBot.coe_le_coe,
      WithTop.coe_le_coe]
    lia

-- should go to Mathlib.NumberTheory.Padics.PadicNumbers
theorem zero_le_addValuation_iff_norm_le_one (x : ℚ_[p]) :
    0 ≤ (Padic.addValuation x : EInt) ↔ ‖x‖ ≤ 1 := by
  by_cases hx : x = 0 <;> simp_all [Padic.norm_le_one_iff_val_nonneg]

-- should go to Mathlib.NumberTheory.Padics.PadicNumbers
variable (p) in
theorem zero_le_addValuation_ratCast_iff (q : ℚ) :
    0 ≤ (Padic.addValuation (q : ℚ_[p]) : EInt) ↔ ¬ p ∣ q.den := by
  rw [← Rat.padicValuation_le_one_iff]
  by_cases hq : q = 0
  · simp [hq]
  · rw [Padic.addValuation.apply (Rat.cast_ne_zero.mpr hq), Padic.valuation_ratCast]
    simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      if_neg hq]
    rw [show WithZero.exp (-padicValRat p q) = (WithZero.exp (padicValRat p q))⁻¹ by simp]
    rw [inv_le_one₀ (WithZero.exp_pos (a := padicValRat p q)), ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    norm_cast

end Padic
