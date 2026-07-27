/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import PadicModForms.ForMathlib.Bernoulli
public import PadicModForms.Rational.Basic

/-!
# Rational Eisenstein series

This file defines the rational `q`-expansions of normalized Eisenstein series and proves their
coefficient formulas and modularity.
-/

@[expose] public noncomputable section

open UpperHalfPlane PowerSeries ArithmeticFunction sigma ModularForm

namespace EisensteinSeries

/-- The rational `q`-expansion of the normalized Eisenstein series of weight `k`. -/
noncomputable def E_rat (k : ℕ) : ℚ⟦X⟧ :=
  mk fun n ↦ if n = 0 then 1 else -(2 * k / bernoulli k : ℚ) * σ (k - 1) n

/-- The rational `q`-expansion of Serre's Eisenstein series `G_k`, normalized so that its
coefficient of `q` is one. -/
noncomputable def G_rat (k : ℕ) : ℚ⟦X⟧ :=
  mk fun n ↦ if n = 0 then -(bernoulli k / (2 * k) : ℚ) else σ (k - 1) n

variable (n : ℕ)

@[simp] theorem coeff_E_rat (k : ℕ) :
    coeff n (E_rat k) = if n = 0 then 1 else -(2 * k / bernoulli k : ℚ) * σ (k - 1) n :=
  coeff_mk ..

@[simp] theorem coeff_G_rat (k : ℕ) :
    coeff n (G_rat k) =
      if n = 0 then -(bernoulli k / (2 * k) : ℚ) else σ (k - 1) n :=
  coeff_mk ..

variable {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k)

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
theorem qExpansion_G_eq_G_rat_map : qExpansion 1 ((-bernoulli k / (2 * k) : ℂ) • E hk) =
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
/-- The rational series `G_rat k` is a classical modular form if `k ≥ 3` is even. -/
theorem G_rat_isModularForm : (G_rat k).isModularForm k :=
  ⟨(-bernoulli k / (2 * k) : ℂ) • E hk, qExpansion_G_eq_G_rat_map hk hk2⟩

/-- The coefficients of the normalized complex Eisenstein series. -/
theorem qExpansion_coeff (n : ℕ) (hk2 : Even k) :
    coeff n (qExpansion 1 (ModularForm.E hk)) =
      if n = 0 then 1 else -(2 * k / bernoulli k : ℂ) * σ (k - 1) n := by
  simpa using EisensteinSeries.E_qExpansion_coeff hk hk2 n

end EisensteinSeries
