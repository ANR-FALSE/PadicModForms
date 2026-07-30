/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.Rational.Basic

/-!
# Rational Eisenstein series

This file introduces the rational `q`-expansions of the normalized Eisenstein series `Eₖ` and of
Serre's Eisenstein series `Gₖ`, shows that they are rational modular forms of weight `k` for `k ≥ 3`
even, and singles out `E₄`, `E₆` and the weight-two series `E₂`.
-/

noncomputable section

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups SetLike DirectSum PowerSeries
  ArithmeticFunction sigma EisensteinSeries Module Free

open scoped MatrixGroups PowerSeries

namespace EisensteinSeries

/-- The auxiliary rational `q`-series underlying the normalized Eisenstein series of weight
`k`. -/
noncomputable def ERatAux (k : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n ↦ if n = 0 then 1 else -(2 * k / bernoulli k : ℚ) * σ (k - 1) n

/-- The rational `q`-expansion of the weight-two Eisenstein series. -/
public noncomputable def E₂Rat : ℚ⟦X⟧ := ERatAux 2

/-- The rational `q`-expansion of Serre's Eisenstein series `G_k`, normalized so that its
coefficient of `q` is one. -/
noncomputable def G_rat (k : ℕ) : ℚ⟦X⟧ :=
  mk fun n ↦ if n = 0 then -(bernoulli k / (2 * k) : ℚ) else σ (k - 1) n

@[simp]
theorem coeff_ERatAux (n k : ℕ) : PowerSeries.coeff n (ERatAux k) =
    if n = 0 then 1 else -(2 * k / bernoulli k : ℚ) * σ (k - 1) n :=
  PowerSeries.coeff_mk ..

@[simp]
public theorem coeff_E₂Rat (n : ℕ) : coeff n E₂Rat = if n = 0 then 1 else (-24 : ℚ) * σ 1 n := by
  by_cases hn : n = 0
  · simp [E₂Rat, hn]
  · simp [E₂Rat, hn, bernoulli_two]
    norm_num

@[simp]
theorem coeff_G_rat (n k : ℕ) : coeff n (G_rat k) =
      if n = 0 then -(bernoulli k / (2 * k) : ℚ) else σ (k - 1) n :=
  coeff_mk ..

variable {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k)

include hk2 in
/-- If `k ≥ 3` is even, then `ERatAux k` maps to the `q`-expansion of mathlib's
normalized Eisenstein series `E hk`. -/
theorem qExpansion_E_eq_ERatAux_map :
    qExpansion 1 (E hk) = (ERatAux k).map (algebraMap ℚ ℂ) := by
  ext n
  rw [PowerSeries.coeff_map, EisensteinSeries.E_qExpansion_coeff hk hk2 n]
  by_cases hn : n = 0 <;> simp [ERatAux, hn]

include hk hk2 in
/-- The rational series `ERatAux k` is a classical modular form if `k ≥ 3` is even. -/
theorem ERatAux_isModularForm : (ERatAux k).isModularForm k :=
  ⟨E hk, qExpansion_E_eq_ERatAux_map hk hk2⟩

include hk hk2 in
/-- If `k ≥ 3` is even, then `G_k` is `-B_k / (2k)` times the normalized Eisenstein
series `E_k`. -/
theorem G_rat_eq_smul_ERatAux : G_rat k = -(bernoulli k / (2 * k) : ℚ) • ERatAux k := by
  ext n
  by_cases hn : n = 0
  · simp [G_rat, ERatAux, hn]
  · grind [coeff_smul, G_rat, ERatAux, coeff_mk, smul_eq_mul,
      show (k : ℚ) ≠ 0 by positivity, bernoulli_ne_zero_of_even hk hk2]

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
/-- The rational series `G_rat k` is a classical modular form if `k ≥ 3` is even. -/
theorem G_rat_isModularForm : (G_rat k).isModularForm k :=
  ⟨(-bernoulli k / (2 * k) : ℂ) • E hk, qExpansion_G_eq_G_rat_map hk hk2⟩

/-- The coefficients of the normalized complex Eisenstein series. -/
theorem qExpansion_coeff (n : ℕ) (hk2 : Even k) : coeff n (qExpansion 1 (ModularForm.E hk)) =
      if n = 0 then 1 else -(2 * k / bernoulli k : ℂ) * σ (k - 1) n := by
  simpa using EisensteinSeries.E_qExpansion_coeff hk hk2 n

end EisensteinSeries

namespace ModularForm

/-- The rational `q`-expansion of `Eₖ`, regarded as a rational modular form of weight `k`. -/
public def ERat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) : rationalModularForms k :=
  ⟨ERatAux k, ERatAux_isModularForm hk hk2⟩

/-- The rational `q`-expansion of `Gₖ`, regarded as a rational modular form of weight `k`. -/
public def GRat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) : rationalModularForms k :=
  ⟨G_rat k, G_rat_isModularForm hk hk2⟩

@[simp]
theorem coe_ERat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    (ERat hk hk2 : ℚ⟦X⟧) = ERatAux k := rfl

@[simp]
theorem coe_GRat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    (GRat hk hk2 : ℚ⟦X⟧) = G_rat k := rfl

@[simp]
public theorem coeff_ERat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (n : ℕ) :
    coeff n (ERat hk hk2 : ℚ⟦X⟧) =
      if n = 0 then 1 else -(2 * k / bernoulli k : ℚ) * σ (k - 1) n :=
  coeff_ERatAux n k

@[simp]
public theorem coeff_GRat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (n : ℕ) :
    coeff n (GRat hk hk2 : ℚ⟦X⟧) =
      if n = 0 then -(bernoulli k / (2 * k) : ℚ) else σ (k - 1) n :=
  coeff_G_rat n k

public theorem ERat_map_complex {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    (ERat hk hk2 : ℚ⟦X⟧).map (algebraMap ℚ ℂ) = qExpansion 1 (E hk) := by
  simpa using (qExpansion_E_eq_ERatAux_map hk hk2).symm

public abbrev E₄Rat : rationalModularForms 4 := ERat (by norm_num) ⟨2, rfl⟩

public abbrev E₆Rat : rationalModularForms 6 := ERat (by norm_num) ⟨3, rfl⟩

@[simp]
theorem rationalModularFormToComplex_ERat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    rationalModularFormToComplex (ERat hk hk2) = E hk := by
  rw [← qExpansion_inj one_pos one_mem_strictPeriods_SL, qExpansion_rationalModularFormToComplex,
    ERat_map_complex]

@[simp]
public theorem rationalModularFormToComplex_E₄Rat : rationalModularFormToComplex E₄Rat = E₄ :=
  rationalModularFormToComplex_ERat (by norm_num) ⟨2, rfl⟩

@[simp]
public theorem rationalModularFormToComplex_E₆Rat : rationalModularFormToComplex E₆Rat = E₆ :=
  rationalModularFormToComplex_ERat (by norm_num) ⟨3, rfl⟩

end ModularForm
