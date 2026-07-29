/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import PadicModForms.ForMathlib.Bernoulli
public import PadicModForms.ForMathlib.QExpansion

/-!
# Rational modular forms

This file defines rational modular forms in terms of their `q`-expansions and gives the rational
modular forms of fixed weight their linear structure.
-/

noncomputable section

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups SetLike DirectSum PowerSeries
  ArithmeticFunction sigma EisensteinSeries

open scoped MatrixGroups PowerSeries

namespace PowerSeries

/-- A rational power series is a modular form of weight `k` if it is the `q`-expansion of a
classical modular form of level one and weight `k`. -/
def isModularForm (k : ℤ) (f : ℚ⟦X⟧) : Prop :=
  ∃ g : ModularForm 𝒮ℒ k, qExpansion 1 g = f.map (algebraMap ℚ ℂ)

theorem zero_isModularForm (k : ℤ) : isModularForm k 0 :=
  ⟨0, by simpa using UpperHalfPlane.qExpansion_zero 1⟩

variable {k l : ℤ} {f g : ℚ⟦X⟧} (hf : f.isModularForm k) (hg : g.isModularForm k)

theorem one_isModularForm : (1 : ℚ⟦X⟧).isModularForm 0 :=
  ⟨1, by simpa using UpperHalfPlane.qExpansion_one 1⟩

include hf

theorem IsModularForm.neg : (-f).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  exact ⟨-F, by simp [ModularForm.qExpansion_neg one_pos one_mem_strictPeriods_SL, hF]⟩

theorem IsModularForm.smul (a : ℚ) : (a • f).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  exact ⟨(a : ℂ) • F, by simp [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hF,
    smul_eq_C_mul]⟩

theorem IsModularForm.mul (hg : g.isModularForm l) : (f * g).isModularForm (k + l) := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨F.mul G, by
    simp only [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, hF, hG, map_mul]⟩

include hg

theorem IsModularForm.add : (f + g).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨F + G, by simp [ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL, hF, hG]⟩

theorem IsModularForm.sub : (f - g).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨F - G, by simp [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, hF, hG]⟩

public def _root_.rationalModularForms (k : ℤ) : Submodule ℚ ℚ⟦X⟧ where
  carrier := {f | f.isModularForm k}
  zero_mem' := zero_isModularForm k
  add_mem' := IsModularForm.add
  smul_mem' a _ hf := IsModularForm.smul hf a

omit hf hg

@[simp]
theorem mem_rationalModularForms : f ∈ rationalModularForms k ↔ f.isModularForm k := .rfl

end PowerSeries

namespace EisensteinSeries

/-- The rational `q`-expansion of the normalized Eisenstein series of weight `k`. -/
noncomputable def E_rat (k : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun n ↦ if n = 0 then 1 else -(2 * k / bernoulli k : ℚ) * σ (k - 1) n

/-- The rational `q`-expansion of Serre's Eisenstein series `G_k`, normalized so that its
coefficient of `q` is one. -/
noncomputable def G_rat (k : ℕ) : ℚ⟦X⟧ :=
  mk fun n ↦ if n = 0 then -(bernoulli k / (2 * k) : ℚ) else σ (k - 1) n

@[simp]
theorem coeff_E_rat (n k : ℕ) : PowerSeries.coeff n (E_rat k) =
    if n = 0 then 1 else -(2 * k / bernoulli k : ℚ) * σ (k - 1) n :=
  PowerSeries.coeff_mk ..

@[simp]
theorem coeff_G_rat (n k : ℕ) : coeff n (G_rat k) =
      if n = 0 then -(bernoulli k / (2 * k) : ℚ) else σ (k - 1) n :=
  coeff_mk ..

variable {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k)

include hk2 in
/-- If `k ≥ 3` is even, then `E_rat k` maps to the `q`-expansion of mathlib's
normalized Eisenstein series `E hk`. -/
theorem qExpansion_E_eq_E_rat_map : qExpansion 1 (E hk) = (E_rat k).map (algebraMap ℚ ℂ) := by
  ext n
  rw [PowerSeries.coeff_map, EisensteinSeries.E_qExpansion_coeff hk hk2 n]
  by_cases hn : n = 0 <;> simp [E_rat, hn]

include hk hk2 in
/-- The rational series `E_rat k` is a classical modular form if `k ≥ 3` is even. -/
theorem E_rat_isModularForm : (E_rat k).isModularForm k :=
  ⟨E hk, qExpansion_E_eq_E_rat_map hk hk2⟩

include hk hk2 in
/-- If `k ≥ 3` is even, then `G_k` is `-B_k / (2k)` times the normalized Eisenstein
series `E_k`. -/
theorem G_rat_eq_smul_E_rat : G_rat k = -(bernoulli k / (2 * k) : ℚ) • E_rat k := by
  ext n
  by_cases hn : n = 0
  · simp [G_rat, E_rat, hn]
  · grind [coeff_smul, G_rat, E_rat, coeff_mk, smul_eq_mul, show (k : ℚ) ≠ 0 by positivity,
      bernoulli_ne_zero_of_even hk hk2]

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
theorem qExpansion_coeff (n : ℕ) (hk2 : Even k) :
    coeff n (qExpansion 1 (ModularForm.E hk)) =
      if n = 0 then 1 else -(2 * k / bernoulli k : ℂ) * σ (k - 1) n := by
  simpa using EisensteinSeries.E_qExpansion_coeff hk hk2 n

end EisensteinSeries

namespace ModularForm

public instance {n : ℤ} : Module ℚ (ModularForm 𝒮ℒ n) := Module.restrictScalars ℚ ℂ _

public instance : Algebra ℚ (⨁ k : ℤ, ModularForm 𝒮ℒ k) := Algebra.restrictScalars ℚ ℂ _

variable {n : ℤ} (f g : rationalModularForms n)

def rationalModularFormToComplexAux : ModularForm 𝒮ℒ n := f.property.choose

@[simp]
theorem qExpansion_rationalModularFormToComplexAux :
    qExpansion 1 (rationalModularFormToComplexAux f) = (f : ℚ⟦X⟧).map (algebraMap ℚ ℂ) :=
  f.property.choose_spec

theorem rationalModularFormToComplexAux_add : rationalModularFormToComplexAux (f + g) =
      rationalModularFormToComplexAux f + rationalModularFormToComplexAux g := by
  simp [← qExpansion_inj one_pos one_mem_strictPeriods_SL, ModularForm.qExpansion_add one_pos
    one_mem_strictPeriods_SL]

/-- The complex modular form whose `q`-expansion is the rational modular form. -/
public def rationalModularFormToComplex : rationalModularForms n →ₗ[ℚ] ModularForm 𝒮ℒ n :=
  (AddMonoidHom.mk' rationalModularFormToComplexAux
    (rationalModularFormToComplexAux_add (n := n))).toRatLinearMap

@[simp]
public theorem qExpansion_rationalModularFormToComplex :
    qExpansion 1 (rationalModularFormToComplex f) = (f : ℚ⟦X⟧).map (algebraMap ℚ ℂ) :=
  qExpansion_rationalModularFormToComplexAux f

/-- The rational `q`-expansion of `Eₖ`, regarded as a rational modular form of weight `k`. -/
public def ERat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) : rationalModularForms k :=
  ⟨E_rat k, E_rat_isModularForm hk hk2⟩

@[simp]
theorem coe_ERat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    (ERat hk hk2 : ℚ⟦X⟧) = E_rat k := rfl

public theorem ERat_map_complex {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    (ERat hk hk2 : ℚ⟦X⟧).map (algebraMap ℚ ℂ) = qExpansion 1 (E hk) := by
  simpa using (qExpansion_E_eq_E_rat_map hk hk2).symm

public abbrev E₄Rat : rationalModularForms 4 := ERat (by norm_num) ⟨2, rfl⟩

public abbrev E₆Rat : rationalModularForms 6 := ERat (by norm_num) ⟨3, rfl⟩

@[simp]
theorem rationalModularFormToComplex_ERat {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    rationalModularFormToComplex (ERat hk hk2) = E hk := by
  rw [← qExpansion_inj one_pos one_mem_strictPeriods_SL, qExpansion_rationalModularFormToComplex,
    ERat_map_complex]

@[simp]
public theorem rationalModularFormToComplex_E₄Rat :
    rationalModularFormToComplex E₄Rat = E₄ :=
  rationalModularFormToComplex_ERat (by norm_num) ⟨2, rfl⟩

@[simp]
public theorem rationalModularFormToComplex_E₆Rat :
    rationalModularFormToComplex E₆Rat = E₆ :=
  rationalModularFormToComplex_ERat (by norm_num) ⟨3, rfl⟩

/-- The submodules of rational modular forms form a graded monoid under multiplication. -/
public instance : GradedMonoid rationalModularForms where
  one_mem := PowerSeries.one_isModularForm
  mul_mem _ _ := PowerSeries.IsModularForm.mul

/-- Forgetting the weight gives the `q`-expansion homomorphism from the graded ring of rational
modular forms to rational power series. -/
public def rationalQExpansion : (⨁ i, rationalModularForms i) →ₐ[ℚ] ℚ⟦X⟧ :=
  coeAlgHom rationalModularForms

variable {n : ℤ} (f : rationalModularForms n)

@[simp]
public theorem rationalQExpansion_of : rationalQExpansion (of _ n f) = f := coeAlgHom_of ..

end ModularForm
