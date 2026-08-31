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

open UpperHalfPlane SetLike DirectSum PowerSeries EisensteinSeries Module Free MatrixGroups

variable (k : ℤ)

namespace PowerSeries

/-- A rational power series is a modular form of weight `k` if it is the `q`-expansion of a
classical modular form of level one and weight `k`. -/
@[expose] public def isModularForm (f : ℚ⟦X⟧) : Prop :=
  ∃ g : ModularForm 𝒮ℒ k, qExpansion 1 g = f.map (algebraMap ℚ ℂ)

public theorem zero_isModularForm : isModularForm k 0 :=
  ⟨0, by simpa using qExpansion_zero 1⟩

theorem one_isModularForm : (1 : ℚ⟦X⟧).isModularForm 0 :=
  ⟨1, by simpa using qExpansion_one 1⟩

variable {k} {l : ℤ} {f g : ℚ⟦X⟧} (hf : f.isModularForm k) (hg : g.isModularForm k)

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

/-- The rational modular forms of weight `k`, as a `ℚ`-submodule of rational power series. -/
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

/-! ### Comparison with complex modular forms -/

public instance {n : ℤ} : Module ℚ (ModularForm 𝒮ℒ n) := restrictScalars ℚ ℂ _

public instance : Algebra ℚ (⨁ k, ModularForm 𝒮ℒ k) := Algebra.restrictScalars ℚ ℂ _

variable {n : ℤ} (f g : rationalModularForms n)

/-- A choice of complex modular form with the given rational `q`-expansion. -/
def rationalModularFormToComplexAux : ModularForm 𝒮ℒ n := f.property.choose

@[simp]
theorem qExpansion_rationalModularFormToComplexAux :
    qExpansion 1 (rationalModularFormToComplexAux f) = (f : ℚ⟦X⟧).map (algebraMap ℚ ℂ) :=
  f.property.choose_spec

theorem rationalModularFormToComplexAux_add : rationalModularFormToComplexAux (f + g) =
      rationalModularFormToComplexAux f + rationalModularFormToComplexAux g := by
  simp [← qExpansion_inj one_pos one_mem_strictPeriods_SL, ModularForm.qExpansion_add one_pos
    one_mem_strictPeriods_SL]

/-- Scalar extension to complex modular forms, as a `ℚ`-linear map. -/
def rationalModularFormToComplexLinear : rationalModularForms n →ₗ[ℚ] ModularForm 𝒮ℒ n :=
  (AddMonoidHom.mk' rationalModularFormToComplexAux
    (rationalModularFormToComplexAux_add (n := n))).toRatLinearMap

/-- Scalar extension from rational modular forms to complex modular forms. -/
public def rationalModularFormToComplex :
    rationalModularForms n →ₛₗ[algebraMap ℚ ℂ] ModularForm 𝒮ℒ n where
  toFun := rationalModularFormToComplexLinear
  map_add' := map_add _
  map_smul' q f := by simp [Rat.cast_smul_eq_qsmul]

/-- The `q`-expansion of the complex modular form attached to `f` is obtained from `f` by
extending the coefficients to `ℂ`. -/
@[simp]
public theorem qExpansion_rationalModularFormToComplex :
    qExpansion 1 (rationalModularFormToComplex f) = (f : ℚ⟦X⟧).map (algebraMap ℚ ℂ) :=
  qExpansion_rationalModularFormToComplexAux f

/-- Scalar extension to complex modular forms is injective. -/
public theorem rationalModularFormToComplex_injective (n) :
    Function.Injective (rationalModularFormToComplex (n := n)) := fun f g h ↦ by
  refine Subtype.ext (PowerSeries.map_injective _ (algebraMap ℚ ℂ).injective ?_)
  rw [← qExpansion_rationalModularFormToComplex, ← qExpansion_rationalModularFormToComplex, h]

/-- Scalar extension to complex modular forms takes `ℚ`-linearly independent families to
`ℂ`-linearly independent ones. -/
public theorem linearIndependent_rationalModularFormToComplex {κ : Type*}
    (v : κ → rationalModularForms n) (hv : LinearIndependent ℚ v) :
    LinearIndependent ℂ (rationalModularFormToComplex ∘ v) := by
  have hvq : LinearIndependent ℚ (fun i ↦ (v i : ℚ⟦X⟧)) := by
    simpa [Function.comp_def] using hv.map' (rationalModularForms n).subtype
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  have hvc : LinearIndependent ℂ (fun i ↦ (v i : ℚ⟦X⟧).map (algebraMap ℚ ℂ)) :=
    linearIndependent_map (fun i ↦ (v i : ℚ⟦X⟧)) hvq
  let := (qExpansionAlgHom 1 one_pos one_mem_strictPeriods_SL).toLinearMap.comp
    (lof ℂ ℤ (ModularForm 𝒮ℒ ·) n)
  apply LinearIndependent.of_comp this
  simpa [this, Function.comp_def, lof_eq_of, qExpansion_rationalModularFormToComplex] using hvc

/-- Scalar extension to complex modular forms takes `ℚ`-linearly independent sets to `ℂ`-linearly
independent ones. This is the hypothesis needed by `Module.Basis.ofCompSemilinear`. -/
public theorem linearIndepOn_rationalModularFormToComplex (s : Set (rationalModularForms n))
    (hs : LinearIndepOn ℚ id s) :
    LinearIndepOn ℂ (rationalModularFormToComplex) s :=
  linearIndependent_rationalModularFormToComplex _ hs

/-! ### Descent of bases and finite dimensionality -/

/-- Descent of a basis: a `ℂ`-basis of the complex modular forms of weight `n` whose members are
scalar extensions of rational modular forms yields a `ℚ`-basis of `rationalModularForms n`. -/
public def basisOfComplexBasis {ι : Type*} (b : ι → rationalModularForms n)
    (c : Basis ι ℂ (ModularForm 𝒮ℒ n)) (hc : c = rationalModularFormToComplex ∘ b) :
    Basis ι ℚ (rationalModularForms n) :=
  .ofCompSemilinear _ linearIndepOn_rationalModularFormToComplex b c hc

@[simp]
public theorem coe_basisOfComplexBasis {ι : Type*} (b : ι → rationalModularForms n)
    (c : Basis ι ℂ (ModularForm 𝒮ℒ n)) (hc : c = rationalModularFormToComplex ∘ b) :
    basisOfComplexBasis b c hc = b :=
  Basis.coe_ofCompSemilinear ..

/-- Rational modular forms of weight `k` have rank over `ℚ` at most the rank over `ℂ` of the
complex modular forms of the same weight. -/
public theorem rationalModularForms_rank_le (k : ℤ) :
    Module.rank ℚ (rationalModularForms k) ≤ Module.rank ℂ (ModularForm 𝒮ℒ k) := by
  rw [rank_eq_card_chooseBasisIndex]
  exact (linearIndependent_rationalModularFormToComplex (chooseBasis ℚ (rationalModularForms k))
    (chooseBasis ℚ (rationalModularForms k)).linearIndependent).cardinal_le_rank

/-- Rational modular forms of a fixed weight form a finite-dimensional `ℚ`-vector space. -/
public noncomputable instance rationalModularForms_finiteDimensional (k : ℤ) :
    FiniteDimensional ℚ (rationalModularForms k) := by
  simpa [← rank_lt_aleph0_iff] using (rationalModularForms_rank_le k).trans_lt (rank_lt_aleph0 ℂ _)

/-- The `ℚ`-dimension of the rational modular forms of weight `k` is at most the `ℂ`-dimension of
the complex modular forms of the same weight. -/
public theorem rationalModularForms_finrank_le (k : ℤ) :
    finrank ℚ (rationalModularForms k) ≤ finrank ℂ (ModularForm 𝒮ℒ k) := by
  rw [← Nat.cast_le (α := Cardinal), finrank_eq_rank, finrank_eq_rank]
  exact rationalModularForms_rank_le k

variable {k}

/-- If there are no nonzero complex modular forms of weight `k`, there are no nonzero rational
ones either. -/
public theorem rationalModularForms_eq_bot (h : Subsingleton (ModularForm 𝒮ℒ k)) :
    rationalModularForms k = ⊥ :=
  have := (rationalModularFormToComplex_injective k).subsingleton
  Submodule.eq_bot_of_subsingleton

/-- There are no nonzero rational modular forms of negative weight. In particular the weight of a
nonzero rational modular form is a natural number. -/
public theorem rationalModularForms_eq_bot_of_neg (hk : k < 0) : rationalModularForms k = ⊥ :=
  rationalModularForms_eq_bot (rank_zero_iff.1 (ModularForm.levelOne_neg_weight_rank_zero hk))

/-- There are no nonzero rational modular forms of odd weight. -/
public theorem rationalModularForms_eq_bot_of_odd (hk : Odd k) : rationalModularForms k = ⊥ :=
  rationalModularForms_eq_bot (rank_zero_iff.1 (ModularForm.levelOne_odd_weight_rank_zero hk))

/-- There are no nonzero rational modular forms of weight `2`. -/
public theorem rationalModularForms_two_eq_bot : rationalModularForms 2 = ⊥ :=
  rationalModularForms_eq_bot (rank_zero_iff.1 ModularForm.levelOne_weight_two_rank_zero)

/-- The weight of a nonzero rational modular form is nonnegative, so it is a natural number. -/
public theorem nonneg_of_mem_rationalModularForms {f : ℚ⟦X⟧} (hf : f ∈ rationalModularForms k)
    (hf0 : f ≠ 0) : 0 ≤ k := by
  by_contra hk
  exact hf0 (by simpa [rationalModularForms_eq_bot_of_neg (not_le.1 hk)] using hf)

/-! ### The graded structure -/

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
  rationalQExpansionAlgHom.toLinearMap.comp (lof ℚ ℤ (fun i ↦ rationalModularForms i) n)

/-- Forgetting the weight of a form concentrated in weight `n` gives back its power series. -/
@[simp]
public theorem rationalQExpansionAlgHom_of :
    rationalQExpansionAlgHom (of _ n f) = f := coeAlgHom_of ..

/-- The `q`-expansion of a rational modular form of weight `n` is its underlying power series. -/
@[simp]
public theorem rationalQExpansion_apply : rationalQExpansion f = f :=
  rationalQExpansionAlgHom_of f

end ModularForm
