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

import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import PadicModForms.ForMathlib.LinearIndependent

/-!
# Rational modular forms

This file defines rational modular forms in terms of their `q`-expansions and gives the rational
modular forms of fixed weight their linear structure.
-/

noncomputable section

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups SetLike DirectSum PowerSeries
  ArithmeticFunction sigma EisensteinSeries Module Free

open scoped MatrixGroups PowerSeries

namespace PowerSeries

/-- A rational power series is a modular form of weight `k` if it is the `q`-expansion of a
classical modular form of level one and weight `k`. -/
@[expose] public def isModularForm (k : ℤ) (f : ℚ⟦X⟧) : Prop :=
  ∃ g : ModularForm 𝒮ℒ k, qExpansion 1 g = f.map (algebraMap ℚ ℂ)

public theorem zero_isModularForm (k : ℤ) : isModularForm k 0 :=
  ⟨0, by simpa using qExpansion_zero 1⟩

variable {k l : ℤ} {f g : ℚ⟦X⟧} (hf : f.isModularForm k) (hg : g.isModularForm k)

theorem one_isModularForm : (1 : ℚ⟦X⟧).isModularForm 0 :=
  ⟨1, by simpa using qExpansion_one 1⟩

include hf

theorem IsModularForm.neg : (-f).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  exact ⟨-F, by simp [ModularForm.qExpansion_neg one_pos one_mem_strictPeriods_SL, hF]⟩

public theorem IsModularForm.smul (a : ℚ) : (a • f).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  exact ⟨(a : ℂ) • F, by simp [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hF,
    smul_eq_C_mul]⟩

theorem IsModularForm.mul (hg : g.isModularForm l) : (f * g).isModularForm (k + l) := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨F.mul G, by
    simp only [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, hF, hG, map_mul]⟩

include hg

public theorem IsModularForm.add : (f + g).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨F + G, by simp [ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL, hF, hG]⟩

theorem IsModularForm.sub : (f - g).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨F - G, by simp [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, hF, hG]⟩

@[expose] public def _root_.rationalModularForms (k : ℤ) : Submodule ℚ ℚ⟦X⟧ where
  carrier := {f | f.isModularForm k}
  zero_mem' := zero_isModularForm k
  add_mem' := IsModularForm.add
  smul_mem' a _ hf := IsModularForm.smul hf a

omit hf hg

@[simp]
theorem mem_rationalModularForms : f ∈ rationalModularForms k ↔ f.isModularForm k := .rfl

end PowerSeries

namespace ModularForm

public instance {n : ℤ} : Module ℚ (ModularForm 𝒮ℒ n) := restrictScalars ℚ ℂ _

public instance : Algebra ℚ (⨁ k, ModularForm 𝒮ℒ k) := Algebra.restrictScalars ℚ ℂ _

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

def rationalModularFormToComplexLinear : rationalModularForms n →ₗ[ℚ] ModularForm 𝒮ℒ n :=
  (AddMonoidHom.mk' rationalModularFormToComplexAux
    (rationalModularFormToComplexAux_add (n := n))).toRatLinearMap

/-- Scalar extension from rational modular forms to complex modular forms. -/
public def rationalModularFormToComplex :
    rationalModularForms n →ₛₗ[algebraMap ℚ ℂ] ModularForm 𝒮ℒ n where
  toFun := rationalModularFormToComplexLinear
  map_add' := map_add _
  map_smul' q f := by simp [Rat.cast_smul_eq_qsmul]

@[simp]
public theorem qExpansion_rationalModularFormToComplex :
    qExpansion 1 (rationalModularFormToComplex f) = (f : ℚ⟦X⟧).map (algebraMap ℚ ℂ) :=
  qExpansion_rationalModularFormToComplexAux f

public theorem rationalModularFormToComplex_injective {k : ℤ} :
    Function.Injective (rationalModularFormToComplex (n := k)) := fun f g h ↦ by
  refine Subtype.ext (PowerSeries.map_injective _ (algebraMap ℚ ℂ).injective ?_)
  rw [← qExpansion_rationalModularFormToComplex, ← qExpansion_rationalModularFormToComplex, h]

public theorem linearIndependent_rationalModularFormToComplex {κ : Type*} {k : ℤ}
    (v : κ → rationalModularForms k) (hv : LinearIndependent ℚ v) :
    LinearIndependent ℂ (rationalModularFormToComplex ∘ v) := by
  have hvq : LinearIndependent ℚ (fun i ↦ (v i : ℚ⟦X⟧)) := by
    simpa [Function.comp_def] using hv.map' (rationalModularForms k).subtype
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  have hvc : LinearIndependent ℂ (fun i ↦ (v i : ℚ⟦X⟧).map (algebraMap ℚ ℂ)) :=
    linearIndependent_map (fun i ↦ (v i : ℚ⟦X⟧)) hvq
  let qexp : ModularForm 𝒮ℒ k →ₗ[ℂ] ℂ⟦X⟧ :=
    (qExpansionLinearMap one_pos one_mem_strictPeriods_SL).comp
      (lof ℂ ℤ (fun k ↦ ModularForm 𝒮ℒ k) k)
  apply LinearIndependent.of_comp qexp
  simpa [qexp, Function.comp_def, lof_eq_of,
    qExpansionLinearMap_apply, qExpansionRingHom_apply,
    qExpansion_rationalModularFormToComplex] using hvc

public theorem rationalModularForms_rank_le (k : ℤ) :
    Module.rank ℚ (rationalModularForms k) ≤ Module.rank ℂ (ModularForm 𝒮ℒ k) := by
  rw [rank_eq_card_chooseBasisIndex]
  exact (linearIndependent_rationalModularFormToComplex (chooseBasis ℚ (rationalModularForms k))
    (chooseBasis ℚ (rationalModularForms k)).linearIndependent).cardinal_le_rank

public noncomputable instance rationalModularForms_finiteDimensional (k : ℤ) :
    FiniteDimensional ℚ (rationalModularForms k) := by
  rw [FiniteDimensional, ← rank_lt_aleph0_iff]
  exact (rationalModularForms_rank_le k).trans_lt (rank_lt_aleph0 ℂ (ModularForm 𝒮ℒ k))

public theorem rationalModularForms_finrank_le (k : ℤ) :
    finrank ℚ (rationalModularForms k) ≤ finrank ℂ (ModularForm 𝒮ℒ k) := by
  have h : (finrank ℚ (rationalModularForms k) : Cardinal) ≤ finrank ℂ (ModularForm 𝒮ℒ k) := by
    rw [finrank_eq_rank, finrank_eq_rank]
    exact rationalModularForms_rank_le k
  exact_mod_cast h

/-- The submodules of rational modular forms form a graded monoid under multiplication. -/
public instance : GradedMonoid rationalModularForms where
  one_mem := PowerSeries.one_isModularForm
  mul_mem _ _ := PowerSeries.IsModularForm.mul

/-- Forgetting the weight gives the `q`-expansion homomorphism from the graded ring of rational
modular forms to rational power series. -/
public def rationalQExpansionAlgHom : (⨁ i, rationalModularForms i) →ₐ[ℚ] ℚ⟦X⟧ :=
  coeAlgHom rationalModularForms

/-- The `q`-expansion linear map on rational modular forms of a fixed weight. -/
public abbrev rationalQExpansion {n : ℤ} : rationalModularForms n →ₗ[ℚ] ℚ⟦X⟧ :=
  rationalQExpansionAlgHom.toLinearMap.comp
    (lof ℚ ℤ (fun i ↦ rationalModularForms i) n)

variable {n : ℤ} (f : rationalModularForms n)

@[simp]
public theorem rationalQExpansionAlgHom_of :
    rationalQExpansionAlgHom (of _ n f) = f := coeAlgHom_of ..

@[simp]
public theorem rationalQExpansion_apply : rationalQExpansion f = f :=
  rationalQExpansionAlgHom_of f

end ModularForm
