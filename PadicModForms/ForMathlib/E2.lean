/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
public import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# The q-expansion of the weight-two Eisenstein series

This file proves that mathlib's normalized weight-two Eisenstein series `E2` is bounded at
infinity and computes its ordinary level-one `q`-expansion. This does not make `E2` a modular
form: its transformation law still has the usual quasimodular correction term.
-/

@[expose] public section

open UpperHalfPlane PowerSeries ArithmeticFunction sigma Filter Function Complex

open scoped Topology ModularForm Real

namespace EisensteinSeries

private lemma summable_sigma_one_mul_exp_neg_pi :
    Summable fun n : ℕ+ ↦ (σ 1 n : ℂ) * (Real.exp (-π) : ℂ) ^ (n : ℕ) := by
  refine Summable.of_norm_bounded ((summable_norm_pow_mul_geometric_of_norm_lt_one 2
      (r := (Real.exp (-π) : ℂ)) (by
        rw [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
        exact neg_lt_zero.mpr Real.pi_pos)).subtype _) (fun n ↦ ?_)
  simp only [norm_mul, norm_natCast, norm_pow, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Real.exp_pos _).le _)
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 1 n).trans_eq (by congr 1)

-- should go to Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.QExpansion
lemma E2_sub_one_isZeroAtImInfty : IsZeroAtImInfty (E2 · - 1) := by
  rw [IsZeroAtImInfty, Filter.ZeroAtFilter]
  rw [show (fun z : ℍ => E2 z - 1) = fun (z : ℍ) =>
      -24 * ∑' n : ℕ+, (σ 1 n : ℂ) * Periodic.qParam 1 z ^ (n : ℕ) by
    funext z
    rw [E2_eq_tsum_cexp]
    simp only [Periodic.qParam, ofReal_one, div_one]
    ring]
  have h : Tendsto (fun z : ℍ => ∑' n : ℕ+,
      (σ 1 n : ℂ) * Periodic.qParam 1 z ^ (n : ℕ)) atImInfty (nhds 0) := by
    rw [← tsum_zero]
    refine tendsto_tsum_of_dominated_convergence
      (f := fun (z : ℍ) (n : ℕ+) ↦ (σ 1 n : ℂ) * Periodic.qParam 1 z ^ (n : ℕ))
      (bound := fun n ↦ ‖(σ 1 n : ℂ) * (Real.exp (-π) : ℂ) ^ (n : ℕ)‖) (g := 0)
      (summable_sigma_one_mul_exp_neg_pi.norm) (fun n ↦ ?_) ?_
    · have hq := UpperHalfPlane.qParam_tendsto_atImInfty (h := (1 : ℝ)) zero_lt_one
      have hpow : Tendsto (fun z : ℍ ↦ Periodic.qParam 1 z ^ (n : ℕ)) atImInfty
          (nhds (0 ^ (n : ℕ))) := Filter.Tendsto.pow hq _
      simpa using (tendsto_const_nhds.mul hpow)
    · filter_upwards [UpperHalfPlane.atImInfty_mem
        (UpperHalfPlane.im ⁻¹' Set.Ici (1 / 2)) |>.mpr ⟨1 / 2, fun _ hz => hz⟩] with z hz
      simp only [Set.mem_preimage, Set.mem_Ici] at hz
      intro k
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      gcongr
      rw [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Periodic.norm_qParam_le_of_one_half_le_im hz
  simpa using h.const_mul (-24)

private lemma E2_periodic : Periodic (E2 ∘ UpperHalfPlane.ofComplex) 1 := by
  have hT : E2 ∣[(2 : ℤ)] ModularGroup.T = E2 := by
    simpa [D2_T] using E2_slash_action ModularGroup.T
  have hvadd (z : ℍ) : E2 ((1 : ℝ) +ᵥ z) = E2 z := by
    have hz := congrFun hT z
    rw [ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_smul] at hz
    simpa [ModularGroup.T, ModularGroup.denom_apply] using hz
  intro z
  by_cases hz : 0 < z.im
  · have hz1 : 0 < (z + 1).im := by simpa using hz
    simp only [comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz1,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have heq : (⟨z + 1, hz1⟩ : ℍ) = (1 : ℝ) +ᵥ ⟨z, hz⟩ := by
      apply UpperHalfPlane.ext
      simp [add_comm]
    exact heq ▸ hvadd _
  · have hz1 : (z + 1).im ≤ 0 := by simpa using le_of_not_gt hz
    simp [comp_apply, UpperHalfPlane.ofComplex_apply_of_im_nonpos hz1,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos (le_of_not_gt hz)]

-- should go to Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.QExpansion
lemma E2_isBoundedAtImInfty : IsBoundedAtImInfty E2 := by
  have h := E2_sub_one_isZeroAtImInfty.isBoundedAtImInfty.add
    (Filter.const_boundedAtFilter atImInfty 1)
  have heq : (E2 · - 1) + Function.const ℍ 1 = E2 := by
    funext z
    simp
  exact heq ▸ h

private lemma summable_sigma_one_mul_qParam (z : ℍ) :
    Summable fun n : ℕ ↦ (σ 1 n) * Periodic.qParam 1 z ^ n := by
  refine Summable.of_norm_bounded (summable_norm_pow_mul_geometric_of_norm_lt_one 2
    (UpperHalfPlane.norm_qParam_lt_one 1 z)) (fun n ↦ ?_)
  simp only [norm_mul, norm_natCast, norm_pow, Nat.cast_one]
  gcongr
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 1 n).trans_eq rfl

private lemma hasSum_E2_coeff (z : ℍ) : HasSum (fun m : ℕ ↦
      (if m = 0 then 1 else -24 * (σ 1 m : ℂ)) • Periodic.qParam 1 z ^ m) (E2 z) := by
  have hS : Summable fun n : ℕ ↦ (σ 1 (n + 1) : ℂ) * Periodic.qParam 1 z ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_one_mul_qParam z)
  have hval : E2 z - 1 = -24 * ∑' n : ℕ, (σ 1 (n + 1) : ℂ) * Periodic.qParam 1 z ^ (n + 1) := by
    rw [E2_eq_tsum_cexp, ← tsum_pnat_eq_tsum_succ (f := fun n ↦ (σ 1 n) * Periodic.qParam 1 z ^ n)]
    simp only [Periodic.qParam, ofReal_one, div_one]
    ring
  rw [← hasSum_nat_add_iff' 1]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, smul_eq_mul,
    Finset.range_one, ite_mul, one_mul, Finset.sum_singleton, pow_zero, hval]
  convert! (hS.mul_left (-24)).hasSum using 1
  · funext i
    ring
  · rw [tsum_mul_left]

-- should go to Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.QExpansion
/-- The coefficients of the ordinary level-one `q`-expansion of `E2`. -/
lemma E2_qExpansion_coeff (m : ℕ) :
    (qExpansion 1 E2).coeff m = if m = 0 then 1 else -24 * (σ 1 m : ℂ) :=
  (UpperHalfPlane.qExpansion_coeff_unique E2c one_pos (UpperHalfPlane.analyticAt_cuspFunction_zero
    one_pos E2_periodic E2_mdifferentiable E2_isBoundedAtImInfty) hasSum_E2_coeff m).symm

end EisensteinSeries
