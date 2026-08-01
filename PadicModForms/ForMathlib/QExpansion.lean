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

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (k : ℤ)

@[simp]
theorem qExpansionAddHom_apply (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (f : ModularForm Γ k) : qExpansionAddHom hh hΓ k f = qExpansion h f := rfl

variable {k}

/-- The `q`-expansion map is injective on modular forms of a fixed weight. -/
theorem qExpansion_injective (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    Function.Injective (fun (f : ModularForm Γ k) ↦ qExpansion h f) := by
  simp only [← qExpansionAddHom_apply _ hh hΓ]
  refine (AddMonoidHom.ker_eq_bot_iff _).1 (AddSubgroup.ext fun F ↦ ?_)
  exact ModularForm.qExpansion_eq_zero_iff hh hΓ F

@[simp]
theorem qExpansion_inj (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    {f g : ModularForm Γ k} : qExpansion h f = qExpansion h g ↔ f = g :=
  (qExpansion_injective hh hΓ).eq_iff

/-- The `q`-expansion map on the graded ring of modular forms, as a linear map. -/
def qExpansionLinearMap [Γ.HasDetOne] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    (⨁ k, ModularForm Γ k) →ₗ[ℂ] ℂ⟦X⟧ :=
  toModule ℂ ℤ ℂ⟦X⟧ fun k ↦
    { toFun := fun (f : ModularForm Γ k) ↦ qExpansion h f
      map_add' := fun f g ↦ by simpa using ModularForm.qExpansion_add hh hΓ f g
      map_smul' := fun c f ↦ by simpa using ModularForm.qExpansion_smul hh hΓ c f }

@[simp]
theorem qExpansionLinearMap_of [Γ.HasDetOne] (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ)
    (f : ModularForm Γ k) : qExpansionLinearMap hh hΓ (of _ k f) = qExpansion h f :=
  toModule_lof ..

@[simp]
theorem qExpansionLinearMap_apply [Γ.HasDetOne] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (F : ⨁ k, ModularForm Γ k) :
    qExpansionLinearMap hh hΓ F = qExpansionRingHom h hh hΓ F := by
  induction F using DirectSum.induction_on with
  | zero => simp
  | of k f => rw [qExpansionLinearMap_of, qExpansionRingHom_apply]
  | add F G hF hG => simpa using congrArg₂ (· + ·) hF hG

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
  | add F G hF hG =>
      rw [map_add]
      rw [IsBoundedAtImInfty, Filter.BoundedAtFilter] at hF hG ⊢
      exact hF.add hG

private theorem qExpansion_levelOneCoeAddHom (F : ⨁ k, ModularForm 𝒮ℒ k) :
    qExpansion 1 (levelOneCoeAddHom F) =
      qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL F := by
  induction F using DirectSum.induction_on with
  | zero => exact qExpansion_zero 1
  | of k f => simp
  | add F G hF hG =>
      calc _ = qExpansion 1 (levelOneCoeAddHom F) + qExpansion 1 (levelOneCoeAddHom G) := by simp
        [qExpansion_add (analyticAt_cuspFunction_zero one_pos (levelOneCoeAddHom_periodic F)
          (levelOneCoeAddHom_holo F) (levelOneCoeAddHom_bdd F))
          (analyticAt_cuspFunction_zero one_pos (levelOneCoeAddHom_periodic G)
          (levelOneCoeAddHom_holo G) (levelOneCoeAddHom_bdd G))]
        _ = _ := by rw [map_add, hF, hG]

private noncomputable def levelOneWeightPolynomial (z : ℍ) : (⨁ k, ModularForm 𝒮ℒ k) →+ ℂ[X] :=
  toAddMonoid fun k ↦ if hk : 0 ≤ k then
    { toFun := fun f ↦ Polynomial.monomial k.toNat (f z)
      map_zero' := by simp
      map_add' := by simp }
  else 0

private theorem levelOneWeightPolynomial_eval (F : ⨁ k, ModularForm 𝒮ℒ k) (z : ℍ) (n : ℕ) :
      letI γ : SL(2, ℤ) := ⟨!![0, -1; 1, n], by simp [Matrix.det_fin_two]⟩
    (levelOneWeightPolynomial z F).eval ((z : ℂ) + n) = levelOneCoeAddHom F (γ • z) := by
  set γ : SL(2, ℤ) := ⟨!![0, -1; 1, n], by simp [Matrix.det_fin_two]⟩
  have hdenom : denom γ z = (z : ℂ) + n :=
    calc denom γ z = (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) := ModularGroup.denom_apply γ z
      _ = _ := by simp [γ]
  induction F using DirectSum.induction_on with
  | zero => simp
  | of k f =>
      by_cases hk : 0 ≤ k
      · let : SlashInvariantFormClass (ModularForm 𝒮ℒ k) Γ(1) k :=
          Gamma_one_coe_eq_SL ▸ inferInstance
        have hf := SlashInvariantForm.slash_action_eqn_SL'' f (mem_Gamma_one γ) z
        rw [hdenom] at hf
        have hp : ((z : ℂ) + n) ^ k = ((z : ℂ) + n) ^ k.toNat := by
          calc _ = ((z : ℂ) + n) ^ (k.toNat : ℤ) :=
              congrArg (fun e : ℤ ↦ ((z : ℂ) + n) ^ e) (Int.toNat_of_nonneg hk).symm
            _ = _ := zpow_natCast _ _
        rw [hp] at hf
        simpa [levelOneWeightPolynomial, hk, Polynomial.eval_monomial, mul_comm] using hf.symm
      · have hf : f = 0 := (coe_eq_zero_iff f).mp
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
        · have hnat : j.toNat ≠ k.toNat := fun h ↦ hjk <| by
            calc j = j.toNat := (Int.toNat_of_nonneg hj).symm
                 _ = k.toNat := congrArg (fun n : ℕ ↦ (n : ℤ)) h
                 _ = k := Int.toNat_of_nonneg hk
          simp [levelOneWeightPolynomial, hj, Polynomial.coeff_monomial, hnat]
        · simp [levelOneWeightPolynomial, hj]
  | add F G hF hG => simpa using congrArg₂ (· + ·) hF hG

private theorem levelOneCoeAddHom_injective : Function.Injective levelOneCoeAddHom := by
  suffices hker : ∀ F, levelOneCoeAddHom F = 0 → F = 0 by
    intro F G hFG
    rw [← sub_eq_zero]
    apply hker (F - G)
    rw [map_sub, hFG, sub_self]
  intro F hF
  apply DirectSum.ext fun k ↦ ?_
  by_cases hk : 0 ≤ k
  · apply ext fun z ↦ ?_
    have hpoly : levelOneWeightPolynomial z F = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.Infinite.mono (t := {x | (levelOneWeightPolynomial z F).IsRoot x})
        (s := Set.range fun n : ℕ ↦ (z : ℂ) + n) ?_
        (Set.infinite_range_of_injective fun n m hnm ↦ ?_)
      · rintro x ⟨n, rfl⟩
        let γ : SL(2, ℤ) := ⟨!![0, -1; 1, n], by simp [Matrix.det_fin_two]⟩
        have hz := congrFun hF (γ • z)
        simpa [levelOneWeightPolynomial_eval, γ] using hz
      · exact_mod_cast (add_left_cancel hnm)
    simpa [hpoly] using (levelOneWeightPolynomial_coeff F z hk).symm
  · exact (coe_eq_zero_iff (F k)).mp
      (ModularFormClass.levelOne_neg_weight_eq_zero (lt_of_not_ge hk) (F k))

/-- The `q`-expansion homomorphism on the graded ring of level-one modular forms is injective. -/
theorem levelOne_qExpansionRingHom_injective : Function.Injective
      (qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL) := by
  intro F G hFG
  apply levelOneCoeAddHom_injective
  rw [← sub_eq_zero, ← map_sub]
  apply (qExpansion_eq_zero_iff one_pos (levelOneCoeAddHom_periodic (F - G))
    (levelOneCoeAddHom_holo (F - G)) (levelOneCoeAddHom_bdd (F - G))).mp
  rw [qExpansion_levelOneCoeAddHom, map_sub, hFG, sub_self]

end ModularForm
