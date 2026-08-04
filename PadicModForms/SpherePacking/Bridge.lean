/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ModularForms.Derivative
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import PadicModForms.SpherePacking.ModularForms.RamanujanIdentities

/-!
# Ramanujan's identities: the interface to the vendored Sphere-Packing-Lean material

This file is the **only** part of `PadicModForms/SpherePacking/` that the rest of the project
may import.  Everything else in that directory is vendored third-party code (see
`PadicModForms/SpherePacking/README.md`); the import of it below is deliberately *private*, so
none of it leaks downstream.

Consequently this file is the whole contract with Sphere-Packing-Lean.  The statements below
mention only Mathlib notions — `Derivative.normalizedDerivOfComplex`, `EisensteinSeries.E2`,
`ModularForm.E₄`, `ModularForm.E₆` — so when Mathlib acquires Ramanujan's identities (they are
a `TODO` in `Mathlib/NumberTheory/ModularForms/Derivative.lean`) it suffices to reprove this
one file and delete the rest of the directory.  Nothing else in the project changes.

## Main results

* `ModularForm.normalizedDeriv_E2`: `D E₂ = (E₂² - E₄) / 12`
* `ModularForm.normalizedDeriv_E₄`: `D E₄ = (E₂E₄ - E₆) / 3`
* `ModularForm.normalizedDeriv_E₆`: `D E₆ = (E₂E₆ - E₄²) / 2`

Here `D = (2πi)⁻¹ d/dz` is `Derivative.normalizedDerivOfComplex`; on `q`-expansions it acts as
`PowerSeries.Θ`, which is what makes these usable in the `p`-adic theory.
-/

public section

open UpperHalfPlane EisensteinSeries Derivative

namespace ModularForm

/-- Ramanujan's identity for `E₂`: `12 D E₂ = E₂² - E₄`. -/
theorem normalizedDeriv_E2 : D E2 = 12⁻¹ * (E2 * E2 - E₄) :=
  ramanujan_E₂

/-- Ramanujan's identity for `E₄`: `3 D E₄ = E₂E₄ - E₆`. -/
theorem normalizedDeriv_E₄ : D E₄ = 3⁻¹ * (E2 * E₄ - E₆) :=
  ramanujan_E₄

/-- Ramanujan's identity for `E₆`: `2 D E₆ = E₂E₆ - E₄²`. -/
theorem normalizedDeriv_E₆ : D E₆ = 2⁻¹ * (E2 * (E₆) - E₄ * E₄) :=
  ramanujan_E₆

end ModularForm
