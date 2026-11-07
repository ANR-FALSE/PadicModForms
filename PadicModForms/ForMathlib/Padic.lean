/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import PadicModForms.ForMathlib.IntLocalization
public import Mathlib.Order.WithBotTop
import Mathlib.NumberTheory.Padics.WithVal

/-!
# Auxiliary results on the additive valuation on `ℚ_[p]`

We also record how the valuation, and the norm, see the `p`-integral rationals and their reduction
modulo `p`.
-/

public section

variable {p : ℕ} [hp : Fact p.Prime]

namespace Padic

-- should go to Mathlib.NumberTheory.Padics.PadicNumbers
theorem intCast_le_addValuation_iff_norm_le_pow (k : ℤ) (x : ℚ_[p]) :
    k ≤ (Padic.addValuation x : EInt) ↔ ‖x‖ ≤ (p : ℝ) ^ (-k) := by
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
    simp [Rat.padicValuation, hq]

end Padic

/-! ### `p`-integral rationals -/

namespace pLocalInt

open Padic

variable (x : pLocalInt p)

-- should go to Mathlib.NumberTheory.Padics.HeightOneSpectrum
/-- A `p`-integral rational has `p`-adic norm at most `1`. -/
theorem norm_coe_le_one : ‖(x : ℚ_[p])‖ ≤ 1 :=
  Padic.norm_rat_le_one ((mem_pLocalInt_iff p).1 x.2)

variable {x}

-- should go to Mathlib.NumberTheory.Padics.HeightOneSpectrum
/-- A `p`-integral rational with nonzero reduction modulo `p` is a unit of `pLocalInt p`, hence has
`p`-adic norm exactly `1`. -/
theorem norm_coe_eq_one (hx : pLocalInt.toZMod x ≠ 0) : ‖(x : ℚ_[p])‖ = 1 := by
  have hx0 : (x : ℚ_[p]) ≠ 0 := by
    simpa using fun h0 ↦ hx ((Subtype.ext h0 : x = 0) ▸ map_zero _)
  have hinv : ‖((x : ℚ_[p]))⁻¹‖ ≤ 1 := by
    simpa using norm_coe_le_one ⟨x⁻¹, inv_mem_pLocalInt x.2 (by grind)⟩
  have hone : ‖(x : ℚ_[p])‖ * ‖((x : ℚ_[p]))⁻¹‖ = 1 := by
    rw [← norm_mul, mul_inv_cancel₀ hx0, norm_one]
  nlinarith [norm_nonneg (x : ℚ_[p]), norm_coe_le_one x]

/-- A `p`-integral rational with nonzero reduction modulo `p ^ m` has `p`-adic norm larger than
`(p ^ m)⁻¹`: if `‖x‖ ≤ (p ^ m)⁻¹` then `x / p ^ m` is `p`-integral, so `p ^ m` divides `x`. -/
theorem pow_lt_norm_coe {m : ℕ} (hx : pLocalInt.toZModPow m x ≠ 0) :
    ((p : ℝ) ^ m)⁻¹ < ‖(x : ℚ_[p])‖ := by
  contrapose! hx
  refine pLocalInt.toZModPow_eq_zero_of_dvd ⟨⟨x / p ^ m, ?_⟩, ?_⟩
  · rw [mem_pLocalInt_iff, ← Rat.padicValuation_le_one_iff,
      ← Padic.norm_rat_le_one_iff_padicValuation_le_one]
    push_cast
    rw [norm_div, norm_pow, Padic.norm_p, inv_pow]
    exact div_le_one_of_le₀ hx (by positivity)
  · ext
    exact (mul_div_cancel₀ _ (pow_ne_zero m (Nat.cast_ne_zero.2 hp.out.ne_zero))).symm

variable (x)

-- should go to Mathlib.NumberTheory.Padics.HeightOneSpectrum
/-- A `p`-integral rational reduces to `0` modulo `p ^ m`
exactly when its `p`-adic norm is `≤ (p ^ m)⁻¹`. -/
theorem norm_coe_le_inv_pow_iff (m : ℕ) :
    ‖(x : ℚ_[p])‖ ≤ ((p : ℝ) ^ m)⁻¹ ↔ pLocalInt.toZModPow m x = 0 := by
  by_cases hm : m = 0
  · rw [hm, pow_zero, inv_one]
    simpa [↓norm_coe_le_one] using pLocalInt.toZModPow_zero x
  refine ⟨by simpa using mt (pow_lt_norm_coe (p := p)), fun hx ↦ ?_⟩
  obtain ⟨y, hy⟩ := pLocalInt.dvd_of_toZModPow_eq_zero hx
  have hcast : (x : ℚ_[p]) = p ^ m * y := by simp_all
  simpa [hcast, norm_mul, norm_p] using mul_le_of_le_one_right (by positivity) (norm_coe_le_one y)

/-- A `p`-integral rational reduces to `0` modulo `p` exactly when its `p`-adic norm is `≤ p⁻¹`. -/
theorem norm_coe_le_inv_iff :
    ‖(x : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ↔ pLocalInt.toZMod x = 0 := by
  rw [← pow_one (p : ℝ), norm_coe_le_inv_pow_iff (m := 1) x]
  exact toZModPow_one_eq_zero_iff x

-- should go to Mathlib.NumberTheory.Padics.HeightOneSpectrum
/-- A `p`-integral rational reduces to `0` modulo `p ^ m` exactly when its valuation is at least
`m`. This generalizes `pLocalInt.one_le_addValuation_iff`. -/
theorem natCast_le_addValuation_iff (m : ℕ) :
    ((m : ℤ) : EInt) ≤ (addValuation (x : ℚ_[p]) : EInt) ↔ pLocalInt.toZModPow m x = 0 := by
  rw [intCast_le_addValuation_iff_norm_le_pow, zpow_neg, zpow_natCast, norm_coe_le_inv_pow_iff]

theorem one_le_addValuation_iff :
    1 ≤ (addValuation (x : ℚ_[p]) : EInt) ↔ pLocalInt.toZMod x = 0 := by
  rw [← toZModPow_one_eq_zero_iff, ← natCast_le_addValuation_iff x 1]
  simp [WithBotTop.coe]

end pLocalInt
