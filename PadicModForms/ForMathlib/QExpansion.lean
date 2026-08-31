/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Additional results about `q`-expansions of modular forms

This file contains results about `q`-expansions.
-/

@[expose] public noncomputable section

open UpperHalfPlane MatrixGroups CongruenceSubgroup DirectSum Polynomial Set

open scoped Manifold MatrixGroups Polynomial PowerSeries

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} {k : ℤ} {f g : ℍ → ℂ}

/-! ### Analyticity of cusp functions

Mathlib knows that `cuspFunction` turns products and differences of functions on `ℍ` into products
and differences of functions on the `q`-disc; these are the resulting closure properties of
analyticity at `q = 0`, which is the hypothesis all the `qExpansion_*` algebra lemmas take.
-/

-- should go to Mathlib.NumberTheory.ModularForms.QExpansion
/-- Analyticity of the cusp function at `q = 0` is preserved by products. -/
theorem AnalyticAt.cuspFunction_mul (hf : AnalyticAt ℂ (cuspFunction h f) 0)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0) : AnalyticAt ℂ (cuspFunction h (f * g)) 0 := by
  rw [UpperHalfPlane.cuspFunction_mul hf.continuousAt hg.continuousAt]
  exact hf.mul hg

-- should go to Mathlib.NumberTheory.ModularForms.QExpansion
/-- Analyticity of the cusp function at `q = 0` is preserved by differences. -/
theorem AnalyticAt.cuspFunction_sub (hf : AnalyticAt ℂ (cuspFunction h f) 0)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0) : AnalyticAt ℂ (cuspFunction h (f - g)) 0 := by
  rw [UpperHalfPlane.cuspFunction_sub hf.continuousAt hg.continuousAt]
  exact hf.sub hg

-- should go to Mathlib.NumberTheory.ModularForms.QExpansion
/-- The cusp function of a level-one modular form is analytic at `q = 0`, for the period `1`. -/
theorem ModularFormClass.analyticAt_cuspFunction_zero_levelOne {F : Type*} [FunLike F ℍ ℂ]
    {k} [ModularFormClass F 𝒮ℒ k] (f : F) : AnalyticAt ℂ (cuspFunction 1 (f : ℍ → ℂ)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL

namespace ModularForm

/-!
### Injectivity of the `q`-expansion on the graded ring of level one modular forms

The proof has two steps. The map `levelOneCoeAddHom` sends `F : ⨁ k, ModularForm 𝒮ℒ k` to the
function `∑ k, F k : ℍ → ℂ`, which is periodic, holomorphic and bounded at infinity, and whose
`q`-expansion is `qExpansionRingHom F`. Hence `qExpansionRingHom F = 0` gives `∑ k, F k = 0`.

It remains to see that modular forms of distinct weights are linearly independent, i.e. that
`levelOneCoeAddHom` is injective. Fixing `z`, the slash equations say that `∑ k, F k` evaluated at
`γ • z` is the polynomial `∑ k, (F k z) • X ^ k` evaluated at `denom γ z`. Taking
`γ = !![0, -1; 1, n]`, whose `denom` at `z` is `z + n`, exhibits infinitely many roots of that
polynomial, so all its coefficients `F k z` vanish.
-/

/-- Sending `F : ⨁ k, ModularForm 𝒮ℒ k` to the function `∑ k, F k : ℍ → ℂ`, forgetting the
weights. -/
private def levelOneCoeAddHom : (⨁ k, ModularForm 𝒮ℒ k) →+ (ℍ → ℂ) :=
  toAddMonoid fun _ ↦
    { toFun := fun f ↦ f
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

@[simp]
private theorem levelOneCoeAddHom_of (k) (f : ModularForm 𝒮ℒ k) :
    levelOneCoeAddHom (of _ k f) = f := by
  simp [levelOneCoeAddHom]

private theorem levelOneCoeAddHom_periodic (F : ⨁ k, ModularForm 𝒮ℒ k) :
    Function.Periodic (levelOneCoeAddHom F ∘ ofComplex) 1 := by
  induction F using DirectSum.induction_on with
  | zero => simp [levelOneCoeAddHom, Function.Periodic]
  | of k f =>
      simpa using (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
  | add F G hF hG =>
      intro z
      simpa using congrArg₂ (· + ·) (hF z) (hG z)

private theorem levelOneCoeAddHom_holo (F : ⨁ k, ModularForm 𝒮ℒ k) :
    MDiff (levelOneCoeAddHom F) := by
  induction F using DirectSum.induction_on with
  | zero => exact mdifferentiable_const
  | of k f => simpa using ModularFormClass.holo f
  | add F G hF hG => simpa using hF.add hG

private theorem levelOneCoeAddHom_bdd (F : ⨁ k, ModularForm 𝒮ℒ k) :
    IsBoundedAtImInfty (levelOneCoeAddHom F) := by
  induction F using DirectSum.induction_on with
  | zero => exact Asymptotics.isBigO_zero _ atImInfty
  | of k f => simpa using ModularFormClass.bdd_at_infty f
  | add F G hF hG => exact map_add levelOneCoeAddHom F G ▸ hF.add hG

private theorem levelOneCoeAddHom_analyticAt (F : ⨁ k, ModularForm 𝒮ℒ k) :
    AnalyticAt ℂ (cuspFunction 1 (levelOneCoeAddHom F)) 0 :=
  analyticAt_cuspFunction_zero one_pos (levelOneCoeAddHom_periodic F) (levelOneCoeAddHom_holo F)
    (levelOneCoeAddHom_bdd F)

private theorem qExpansion_levelOneCoeAddHom (F : ⨁ k, ModularForm 𝒮ℒ k) :
    qExpansion 1 (levelOneCoeAddHom F) =
      qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL F := by
  induction F using DirectSum.induction_on with
  | zero => exact qExpansion_zero 1
  | of k f => simp
  | add F G hF hG =>
      rw [map_add, map_add, qExpansion_add (levelOneCoeAddHom_analyticAt F)
        (levelOneCoeAddHom_analyticAt G), hF, hG]

/-- The polynomial `∑ k, (F k z) • X ^ k`, recording the values at `z` of the components of
`F` together with their weights. -/
private noncomputable def levelOneWeightPolynomial (z : ℍ) : (⨁ k, ModularForm 𝒮ℒ k) →+ ℂ[X] :=
  toAddMonoid fun k ↦ if hk : 0 ≤ k then
    { toFun := fun f ↦ Polynomial.monomial k.toNat (f z)
      map_zero' := by simp
      map_add' := by simp }
  else 0

/-- Evaluating the weight polynomial of `F` at `denom γ z` gives the value at `γ • z` of the
(mixed weight) function attached to `F`: this is just the slash equation, weight by weight. -/
private theorem levelOneWeightPolynomial_eval (F : ⨁ k, ModularForm 𝒮ℒ k) (z : ℍ)
    (γ : SL(2, ℤ)) :
    (levelOneWeightPolynomial z F).eval (denom γ z) = levelOneCoeAddHom F (γ • z) := by
  induction F using DirectSum.induction_on with
  | zero => simp
  | of k f =>
      by_cases hk : 0 ≤ k
      · let : SlashInvariantFormClass (ModularForm 𝒮ℒ k) Γ(1) k :=
          Gamma_one_coe_eq_SL ▸ inferInstance
        have hf := SlashInvariantForm.slash_action_eqn_SL'' f (mem_Gamma_one γ) z
        have hp : (denom γ z) ^ k = (denom γ z) ^ k.toNat := by
          rw [← zpow_natCast, Int.toNat_of_nonneg hk]
        rw [hp] at hf
        simpa [levelOneWeightPolynomial, hk, Polynomial.eval_monomial, mul_comm] using hf.symm
      · have hf : f = 0 := (FunLike.coe_zero_iff f).mp
          (ModularFormClass.levelOne_neg_weight_eq_zero (lt_of_not_ge hk) f)
        simp [levelOneWeightPolynomial, hf]
  | add F G hF hG => simpa using congrArg₂ (· + ·) hF hG

private theorem levelOneWeightPolynomial_coeff
    (F : ⨁ k, ModularForm 𝒮ℒ k) (z : ℍ) (hk : 0 ≤ k) :
    (levelOneWeightPolynomial z F).coeff k.toNat = F k z := by
  induction F using DirectSum.induction_on with
  | zero => simp
  | of j f =>
      rcases eq_or_ne j k with rfl | hjk
      · simp [levelOneWeightPolynomial, hk]
      · rw [of_eq_of_ne j k f (fun h ↦ hjk h.symm)]
        by_cases hj : 0 ≤ j
        · have hnat : j.toNat ≠ k.toNat := by lia
          simp [levelOneWeightPolynomial, hj, Polynomial.coeff_monomial, hnat]
        · simp [levelOneWeightPolynomial, hj]
  | add F G hF hG => simpa using congrArg₂ (· + ·) hF hG

/-- The matrix `!![0, -1; 1, n] ∈ SL(2, ℤ)`, whose `denom` at `z` is `z + n`. -/
private def levelOneShift (n : ℕ) : SL(2, ℤ) := ⟨!![0, -1; 1, n], by simp [Matrix.det_fin_two]⟩

private theorem denom_levelOneShift (n : ℕ) (z : ℍ) : denom (levelOneShift n) z = (z : ℂ) + n := by
  rw [ModularGroup.denom_apply]
  simp [levelOneShift]

private theorem levelOneCoeAddHom_injective : Function.Injective levelOneCoeAddHom := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  refine DirectSum.ext fun k ↦ ?_
  by_cases hk : 0 ≤ k
  · refine ext fun z ↦ ?_
    have hpoly : levelOneWeightPolynomial z F = 0 :=
      Polynomial.eq_zero_of_infinite_isRoot _ <| Set.infinite_of_injective_forall_mem
        (f := fun n : ℕ ↦ (z : ℂ) + n) (fun n m hnm ↦ by exact_mod_cast add_left_cancel hnm)
        fun n ↦ by
          simpa [IsRoot, ← denom_levelOneShift n z, levelOneWeightPolynomial_eval] using
            congrFun hF (levelOneShift n • z)
    simpa [hpoly] using (levelOneWeightPolynomial_coeff F z hk).symm
  · exact (FunLike.coe_zero_iff (F k)).mp
      (ModularFormClass.levelOne_neg_weight_eq_zero (lt_of_not_ge hk) (F k))

/-- The `q`-expansion homomorphism on the graded ring of level-one modular forms is injective. -/
theorem levelOne_qExpansionRingHom_injective : Function.Injective
      (qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL) := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  refine levelOneCoeAddHom_injective (map_zero levelOneCoeAddHom ▸ ?_)
  refine (qExpansion_eq_zero_iff one_pos (levelOneCoeAddHom_periodic F)
    (levelOneCoeAddHom_holo F) (levelOneCoeAddHom_bdd F)).mp ?_
  rw [qExpansion_levelOneCoeAddHom, hF]

end ModularForm
