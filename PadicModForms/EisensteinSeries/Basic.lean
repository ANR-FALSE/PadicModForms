/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.EisensteinSeries.Defs
public import PadicModForms.ForMathlib.Bernoulli

/-!
# Basic results about Eisenstein series

This file proves coefficient formulas and modularity results for the Eisenstein series defined in
`PadicModForms.EisensteinSeries.Defs`.
-/

@[expose] public section

open UpperHalfPlane PowerSeries ArithmeticFunction sigma ModularForm

variable {p : ℕ} [Fact p.Prime] (n : ℕ)

namespace EisensteinSeries

@[simp] theorem coeff_E_rat (k : ℕ) :
    coeff n (E_rat k) = if n = 0 then 1 else -(2 * k / bernoulli k : ℚ) * σ (k - 1) n :=
  coeff_mk ..

@[simp] theorem coeff_G_rat (k : ℕ) :
    coeff n (G_rat k) = if n = 0 then -(bernoulli k / (2 * k) : ℚ) else σ (k - 1) n :=
  coeff_mk ..

/-- `E_rat 2` is the rational Fourier expansion of `E2`. -/
theorem E2_eq_tsum_E_rat (z : ℍ) :
    E2 z = ((coeff 0 (E_rat 2) : ℚ) : ℂ) +
      ∑' n : ℕ+, ((coeff n (E_rat 2) : ℚ) : ℂ) *
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

@[simp] theorem coeff_P : coeff n P = if n = 0 then 1 else (-24 : ℚ_[p]) * σ 1 n := by
  by_cases hn : n = 0
  · simp [P, hn]
  · simp [P, hn, bernoulli_two]
    norm_num

@[simp] theorem coeff_Q : coeff n Q = if n = 0 then 1 else (240 : ℚ_[p]) * σ 3 n := by
  by_cases hn : n = 0
  · simp [Q, hn]
  · simp [Q, hn, bernoulli_four]
    ring

@[simp] theorem coeff_R : coeff n R = if n = 0 then 1 else -(504 : ℚ_[p]) * σ 5 n := by
  by_cases hn : n = 0
  · simp [R, hn]
  · simp [R, hn, bernoulli_six]
    norm_num

variable {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k)

@[simp]
theorem coeff_E_int (hpk : p - 1 ∣ k) : (coeff n (E_int hk hk2 hpk) : pLocalInt p) =
      if n = 0 then 1 else -(2 * k / bernoulli k) * σ (k - 1) n := by
  rw [E_int, coeff_toSubring, coeff_E_rat]

/-- The constant coefficient of `E_int` is `1`. -/
@[simp]
theorem coeff_E_int_zero (hpk : p - 1 ∣ k) : coeff 0 (E_int hk hk2 hpk) = 1 := by
  exact Subtype.ext <| by simp only [coeff_E_int, reduceIte, OneMemClass.coe_one]

/-- A nonconstant coefficient of `E_int` factors through `Bₖ⁻¹`. -/
theorem coeff_E_int_of_ne_zero (hpk : p - 1 ∣ k) {m : ℕ} (hm : m ≠ 0) :
    coeff m (E_int hk hk2 hpk) =
      -(2 * k) * ⟨_, inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩ * σ (k - 1) m := Subtype.ext <| by
  simp [coeff_E_int, hm, div_eq_mul_inv, show ((2 : pLocalInt p) : ℚ) = 2 from
    map_ofNat (pLocalInt p).subtype 2]

/-- Extending scalars from `pLocalInt p` to `ℚ` sends `E_int` to `E_rat`. -/
theorem E_int_map (hpk : p - 1 ∣ k) : (E_int hk hk2 hpk).map (algebraMap _ ℚ) = E_rat k := by
  ext
  simp [coeff_E_int, coeff_E_rat]

namespace ModP

/-- The coefficients of `E`. -/
@[simp]
theorem coeff_E (hp : 5 ≤ p) (m : ℕ) : (coeff m (E hp) : pLocalInt p) =
    if m = 0 then 1 else -(2 * (p - 1) / bernoulli (p - 1)) * σ (p - 2) m := by
  rw [E, coeff_E_int, Nat.cast_sub (by lia : 1 ≤ p)]
  congr 2

end ModP

include hk hk2 in
/-- If `k ≥ 3` is even, then `G_k` is `-B_k / (2k)` times the normalized Eisenstein
series `E_k`. -/
theorem G_rat_eq_smul_E_rat : G_rat k = -(bernoulli k / (2 * k) : ℚ) • E_rat k := by
  ext n
  by_cases hn : n = 0
  · simp [G_rat, E_rat, hn]
  · grind [coeff_smul, G_rat, E_rat, coeff_mk, smul_eq_mul, show (k : ℚ) ≠ 0 by positivity,
      bernoulli_ne_zero_of_even hk hk2]

include hk2 in
/-- If `k ≥ 3` is even, then `E_rat k` maps to the `q`-expansion of mathlib's
normalized Eisenstein series `E hk`. -/
theorem qExpansion_E_eq_E_rat_map : qExpansion 1 (E hk) = (E_rat k).map (algebraMap ℚ ℂ) := by
  ext n
  rw [coeff_map, EisensteinSeries.E_qExpansion_coeff hk hk2 n]
  by_cases hn : n = 0 <;> simp [E_rat, hn]

include hk hk2 in
/-- If `k ≥ 3` is even, then the scalar extension of `G_rat k` is the `q`-expansion of
`-B_k / (2k)` times the normalized Eisenstein series. -/
theorem qExpansion_G_eq_G_rat_map :
    qExpansion 1 ((-bernoulli k / (2 * k) : ℂ) • E hk) =
      (G_rat k).map (algebraMap ℚ ℂ) := by
  have hk0C : (k : ℂ) ≠ 0 := by exact_mod_cast (by positivity)
  have hB := bernoulli_ne_zero_of_even hk hk2
  ext n
  rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, coeff_smul, coeff_map,
    EisensteinSeries.E_qExpansion_coeff hk hk2 n]
  by_cases hn : n = 0
  · simp [G_rat, hn]
    ring
  · simp [G_rat, hn, smul_eq_mul]
    field_simp

include hk hk2 in
/-- The rational series `E_rat k` is a classical modular form if `k ≥ 3` is even. -/
theorem E_rat_isModularForm : (E_rat k).isModularForm k :=
  ⟨E hk, qExpansion_E_eq_E_rat_map hk hk2⟩

include hk hk2 in
/-- The rational series `G_rat k` is a classical modular if `k ≥ 3` is even. -/
theorem G_rat_isModularForm : (G_rat k).isModularForm k :=
  ⟨(-bernoulli k / (2 * k) : ℂ) • E hk, qExpansion_G_eq_G_rat_map hk hk2⟩

variable (p)

include hk hk2 in
theorem E_rat_map_isPAdicModularForm :
    isPAdicModularForm p ((E_rat k).map (algebraMap ℚ ℚ_[p])) :=
  powerSeries_isPAdicModularForm_of_qExpansion_eq_map p ⟨k, E_rat_isModularForm hk hk2⟩

include hk hk2 in
theorem G_rat_map_isPAdicModularForm :
    isPAdicModularForm p ((G_rat k).map (algebraMap ℚ ℚ_[p])) :=
  powerSeries_isPAdicModularForm_of_qExpansion_eq_map p ⟨k, G_rat_isModularForm hk hk2⟩

theorem Q_isPAdicModularForm : isPAdicModularForm p Q := by
  simpa [Q] using E_rat_map_isPAdicModularForm p (k := 4) (by norm_num) ⟨2, rfl⟩

theorem R_isPAdicModularForm : isPAdicModularForm p R := by
  simpa [R] using E_rat_map_isPAdicModularForm p (k := 6) (by norm_num) ⟨3, rfl⟩

end EisensteinSeries
