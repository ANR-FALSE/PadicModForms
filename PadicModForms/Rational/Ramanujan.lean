/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.Theta
public import PadicModForms.Rational.E2

import Mathlib.NumberTheory.ModularForms.RamanujanFormula
import PadicModForms.ForMathlib.QExpansionDeriv

/-!
# Ramanujan's identities on rational `q`-expansions

Mathlib proves Ramanujan's identities analytically, as identities between functions on the upper
half plane involving the normalized derivative `D = (2πi)⁻¹ d/dz`. This file transports them to
the algebraic setting the `p`-adic theory works in: identities in `ℚ⟦X⟧` between the rational
`q`-expansions `E₂Rat`, `E₄Rat`, `E₆Rat` and the operator `Θ = q d/dq`.

## Main results

* `EisensteinSeries.Θ_E₂Rat`: `12 Θ E₂ = E₂² - E₄`
* `EisensteinSeries.Θ_E₄Rat`: `3 Θ E₄ = E₂E₄ - E₆`
* `EisensteinSeries.Θ_E₆Rat`: `2 Θ E₆ = E₂E₆ - E₄²`
-/

noncomputable section

open PowerSeries UpperHalfPlane ModularForm EisensteinSeries Derivative

namespace EisensteinSeries

/-! ### The identities over `ℂ` -/

theorem analyticAt_E₄ : AnalyticAt ℂ (cuspFunction 1 E₄) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero_levelOne E₄

theorem analyticAt_E₆ : AnalyticAt ℂ (cuspFunction 1 E₆) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero_levelOne E₆

theorem analyticAt_E2 : AnalyticAt ℂ (cuspFunction 1 E2) 0 :=
  E2_analyticAt_cuspFunction_zero

/-- Ramanujan's identity for `E₂` on `q`-expansions over `ℂ`. -/
theorem Θ_qExpansion_E2 : Θ (qExpansion 1 E2) =
    (12⁻¹ : ℂ) • (qExpansion 1 E2 * qExpansion 1 E2 - qExpansion 1 E₄) := by
  have h := analyticAt_E2.cuspFunction_mul analyticAt_E2
  calc _ = qExpansion 1 (D E2) :=
        (qExpansion_normalizedDeriv_one E2_periodic E2_mdifferentiable isBoundedAtImInfty_E2).symm
    _ = qExpansion 1 ((12⁻¹ : ℂ) • (E2 * E2 - E₄)) := by
        rw [normalizedDerivOfComplex_E₂, pow_two]
    _ = 12⁻¹ • qExpansion 1 (E2 * E2 - E₄) := qExpansion_smul (h.cuspFunction_sub analyticAt_E₄) _
    _ = _ := by rw [qExpansion_sub h analyticAt_E₄, qExpansion_mul analyticAt_E2 analyticAt_E2]

/-- Ramanujan's identity for `E₄` on `q`-expansions over `ℂ`. -/
theorem Θ_qExpansion_E₄ : Θ (qExpansion 1 E₄) =
    (3⁻¹ : ℂ) • (qExpansion 1 E2 * qExpansion 1 E₄ - qExpansion 1 E₆) := by
  have h := analyticAt_E2.cuspFunction_mul analyticAt_E₄
  calc _ = qExpansion 1 (D E₄) := (qExpansion_normalizedDeriv_levelOne E₄).symm
    _ = qExpansion 1 ((3⁻¹ : ℂ) • (E2 * E₄ - E₆)) := by rw [normalizedDerivOfComplex_E₄]
    _ = 3⁻¹ • qExpansion 1 (E2 * E₄ - E₆) := qExpansion_smul (h.cuspFunction_sub analyticAt_E₆) _
    _ = _ := by rw [qExpansion_sub h analyticAt_E₆, qExpansion_mul analyticAt_E2 analyticAt_E₄]

/-- Ramanujan's identity for `E₆` on `q`-expansions over `ℂ`. -/
theorem Θ_qExpansion_E₆ : Θ (qExpansion 1 E₆) =
    (2⁻¹ : ℂ) • (qExpansion 1 E2 * qExpansion 1 E₆ - qExpansion 1 E₄ * qExpansion 1 E₄) := by
  have h := analyticAt_E2.cuspFunction_mul analyticAt_E₆
  have hsq := analyticAt_E₄.cuspFunction_mul analyticAt_E₄
  calc _ = qExpansion 1 (D E₆) := (qExpansion_normalizedDeriv_levelOne E₆).symm
    _ = qExpansion 1 ((2⁻¹ : ℂ) • (E2 * E₆ - E₄ * E₄)) := by
        rw [normalizedDerivOfComplex_E₆, pow_two]
    _ = 2⁻¹ • qExpansion 1 (E2 * E₆ - E₄ * E₄) := qExpansion_smul (h.cuspFunction_sub hsq) _
    _ = _ := by rw [qExpansion_sub h hsq, qExpansion_mul analyticAt_E2 analyticAt_E₆,
      qExpansion_mul analyticAt_E₄ analyticAt_E₄]

/-! ### The identities over `ℚ` -/

/-- **Ramanujan's identity** for `E₂`: `12 Θ E₂ = E₂² - E₄`. -/
public theorem Θ_E₂Rat : 12 * Θ E₂Rat = E₂Rat * E₂Rat - E₄Rat := by
  refine map_injective _ (algebraMap ℚ ℂ).injective ?_
  rw [map_mul, map_Θ, ← qExpansion_E2_eq_E₂Rat_map, Θ_qExpansion_E2, map_sub, map_mul,
    ← qExpansion_E2_eq_E₂Rat_map, E₄Rat_map_complex, map_ofNat, smul_eq_C_mul, ← mul_assoc,
    ← map_ofNat C, ← map_mul]
  norm_num

/-- **Ramanujan's identity** for `E₄`: `3 Θ E₄ = E₂E₄ - E₆`. -/
public theorem Θ_E₄Rat : 3 * Θ (R := ℚ) E₄Rat = E₂Rat * E₄Rat - E₆Rat := by
  refine map_injective _ (algebraMap ℚ ℂ).injective ?_
  rw [map_mul, map_Θ, E₄Rat_map_complex, Θ_qExpansion_E₄, map_sub, map_mul,
    ← qExpansion_E2_eq_E₂Rat_map, E₄Rat_map_complex, E₆Rat_map_complex, map_ofNat, smul_eq_C_mul,
    ← mul_assoc, ← map_ofNat C 3, ← map_mul]
  norm_num

/-- **Ramanujan's identity** for `E₆`: `2 Θ E₆ = E₂E₆ - E₄²`. -/
public theorem Θ_E₆Rat : 2 * Θ (R := ℚ) E₆Rat = E₂Rat * E₆Rat - E₄Rat * E₄Rat := by
  refine map_injective _ (algebraMap ℚ ℂ).injective ?_
  rw [map_mul, map_Θ, E₆Rat_map_complex, Θ_qExpansion_E₆, map_sub, map_mul, map_mul,
    ← qExpansion_E2_eq_E₂Rat_map, E₄Rat_map_complex, E₆Rat_map_complex, map_ofNat,
    smul_eq_C_mul, ← mul_assoc, ← map_ofNat C, ← map_mul]
  norm_num

end EisensteinSeries
