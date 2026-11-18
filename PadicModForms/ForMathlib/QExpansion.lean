/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-!
# Additional results about `q`-expansions of modular forms

This file contains results about `q`-expansions.
-/

public noncomputable section

open UpperHalfPlane MatrixGroups

open scoped MatrixGroups

variable {h : ℝ} {f g : ℍ → ℂ}

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
    {k : ℤ} [ModularFormClass F 𝒮ℒ k] (f : F) : AnalyticAt ℂ (cuspFunction 1 (f : ℍ → ℂ)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL

end
