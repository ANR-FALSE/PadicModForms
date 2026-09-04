/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import PadicModForms.ForMathlib.EInt
public import PadicModForms.ForMathlib.IntLocalization

/-!
# Auxiliary results on the additive valuation on `ℚ_[p]`

We also record how the valuation, and the norm, see the `p`-integral rationals and their reduction
modulo `p`.
-/

@[expose] public section

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
    simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      ite_eq_right hq]
    rw [show WithZero.exp (-padicValRat p q) = (WithZero.exp (padicValRat p q))⁻¹ by simp]
    rw [inv_le_one₀ (WithZero.exp_pos (a := padicValRat p q)), ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    norm_cast

end Padic

/-! ### `p`-integral rationals -/

namespace pLocalInt

open Padic

variable {x : pLocalInt p}

-- should go to Mathlib.NumberTheory.Padics.HeightOneSpectrum
/-- A `p`-integral rational has `p`-adic norm at most `1`. -/
theorem norm_coe_le_one (x : pLocalInt p) : ‖(x : ℚ_[p])‖ ≤ 1 :=
  (zero_le_addValuation_iff_norm_le_one _).1
    ((zero_le_addValuation_ratCast_iff p _).2 ((mem_pLocalInt_iff _).1 x.2))

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

theorem pow_le_norm_coe {m : ℕ} (hx : pLocalInt.toZModPow m x ≠ 0) :
    ((p : ℝ) ^ m)⁻¹ < ‖(x : ℚ_[p])‖ := by
  by_cases hxzero : x = 0
  · simp [hxzero] at hx
  contrapose! hx
  rw [← zpow_natCast, ← zpow_neg, ← intCast_le_addValuation_iff_norm_le_pow,
    Padic.addValuation.apply (mod_cast hxzero), WithBotTop.coe, Function.comp_apply,
    WithBot.coe_le_coe, WithTop.coe_le_coe, valuation_ratCast] at hx
  obtain ⟨y, z, hy⟩ := IsLocalization.exists_mk'_eq (Ideal.span {(p : ℤ)}).primeCompl x
  have heq : x * z = y := by simpa using IsLocalization.eq_mk'_iff_mul_eq.mp hy.symm
  have hvaleq : padicValRat p x + padicValRat p z = padicValRat p y := by
    rw [← padicValRat.mul (by simp [hxzero])]
    · congr; norm_cast
    simp only [ne_eq, Int.cast_eq_zero]
    exact fun h => (h ▸ (Ideal.mem_primeCompl_iff.mp z.property)) (Ideal.span {(p : ℤ)}).zero_mem
  simp only [padicValRat.of_int] at hvaleq
  have hvaly : m ≤ padicValInt p y := by
    rw [← Nat.cast_le (α := ℤ), ← hvaleq]
    linarith
  have hdvdy : (p : (pLocalInt p)) ^ m ∣ y := by
    obtain ⟨b, hb⟩ := (padicValInt_dvd_iff m y).mpr (Or.inr hvaly)
    exact ⟨b, by rw [hb]; push_cast; ring⟩
  rw [← heq] at hdvdy
  rw [pLocalInt.toZModPow_eq_zero_iff]
  exact (IsLocalization.map_units (pLocalInt p) z).dvd_mul_right.mp hdvdy

-- should go to Mathlib.NumberTheory.Padics.HeightOneSpectrum
/-- A `p`-integral rational reduces to `0` modulo `p` exactly when its `p`-adic norm is `≤ 1`. -/
theorem norm_coe_le_inv_iff (x : pLocalInt p) :
    ‖(x : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ↔ pLocalInt.toZMod x = 0 := by
  refine ⟨fun h ↦ by_contra fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rw [norm_coe_eq_one hx] at h
    exact absurd h (not_le.2 (inv_lt_one_of_one_lt₀ (mod_cast hp.1.one_lt)))
  · obtain ⟨y, hy⟩ := pLocalInt.dvd_of_toZMod_eq_zero hx
    have hcast : (x : ℚ_[p]) = p * y := by simp_all
    simpa [hcast, norm_mul, norm_p] using mul_le_of_le_one_right (by positivity) (norm_coe_le_one y)

theorem norm_coe_le_inv_pow_iff (m : ℕ) (x : pLocalInt p) :
    ‖(x : ℚ_[p])‖ ≤ ((p : ℝ) ^ m)⁻¹ ↔ pLocalInt.toZModPow m x = 0 := by
  by_cases hm : m = 0
  · simp only [hm, pow_zero, inv_one, norm_coe_le_one, true_iff]
    exact hm ▸ pLocalInt.toZModPow_zero x
  refine ⟨by simpa using mt (pow_le_norm_coe (p := p)), fun hx ↦ ?_⟩
  obtain ⟨y, hy⟩ := pLocalInt.dvd_of_toZModPow_eq_zero hx
  have hcast : (x : ℚ_[p]) = p ^ m * y := by simp_all
  simpa [hcast, norm_mul, norm_p] using mul_le_of_le_one_right (by positivity) (norm_coe_le_one y)

-- should go to Mathlib.NumberTheory.Padics.HeightOneSpectrum
/-- A `p`-integral rational reduces to `0` modulo `p` exactly when its valuation is at least `1`. -/
theorem one_le_addValuation_iff (x : pLocalInt p) :
    1 ≤ (addValuation (x : ℚ_[p]) : EInt) ↔ pLocalInt.toZMod x = 0 := by
  rw [show 1 = ((1 : ℤ) : EInt) by simp [WithBotTop.coe],
    intCast_le_addValuation_iff_norm_le_pow, zpow_neg, zpow_one, norm_coe_le_inv_iff]

-- should go to Mathlib.NumberTheory.Padics.HeightOneSpectrum
/-- A `p`-integral rational reduces to `0` modulo `p ^ m` exactly when its valuation is at least
`m`. This generalizes `pLocalInt.one_le_addValuation_iff`. -/
theorem natCast_le_addValuation_iff (m : ℕ) (x : pLocalInt p) :
    ((m : ℤ) : EInt) ≤ (addValuation (x : ℚ_[p]) : EInt) ↔ pLocalInt.toZModPow m x = 0 := by
  rw [intCast_le_addValuation_iff_norm_le_pow, zpow_neg, zpow_natCast, norm_coe_le_inv_pow_iff]

end pLocalInt
