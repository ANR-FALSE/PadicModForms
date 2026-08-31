/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The q-expansion of the weight-two Eisenstein series

Mathlib knows that its normalized weight-two Eisenstein series `E2` is `1`-periodic and bounded
at infinity; this file records that its cusp function is therefore analytic at `q = 0` and
computes its ordinary level-one `q`-expansion. This does not make `E2` a modular form: its
transformation law still has the usual quasimodular correction term.
-/

@[expose] public section

open UpperHalfPlane PowerSeries ArithmeticFunction sigma Function Complex

namespace EisensteinSeries

-- should go to Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.QExpansion
/-- The cusp function of `E2` is analytic at `q = 0`, for the period `1`. -/
lemma E2_analyticAt_cuspFunction_zero : AnalyticAt ℂ (cuspFunction 1 E2) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero one_pos E2_periodic E2_mdifferentiable
    isBoundedAtImInfty_E2

private lemma hasSum_E2_coeff (z : ℍ) : HasSum (fun m : ℕ ↦
    (if m = 0 then 1 else -24 * (σ 1 m : ℂ)) • Periodic.qParam 1 z ^ m) (E2 z) := by
  simpa only [Periodic.qParam, Complex.ofReal_one, div_one] using hasSum_qExpansion_E2 z

-- should go to Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.QExpansion
/-- The coefficients of the ordinary level-one `q`-expansion of `E2`. -/
lemma E2_qExpansion_coeff (m : ℕ) :
    (qExpansion 1 E2).coeff m = if m = 0 then 1 else -24 * (σ 1 m : ℂ) :=
  let E2c : C(ℍ, ℂ) := ⟨E2, E2_mdifferentiable.continuous⟩
  (UpperHalfPlane.qExpansion_coeff_unique E2c one_pos E2_analyticAt_cuspFunction_zero
    hasSum_E2_coeff m).symm

end EisensteinSeries
