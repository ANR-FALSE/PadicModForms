/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.Theta
public import PadicModForms.Rational.Ramanujan
public import PadicModForms.pLocalInt.Eisenstein

/-!
# Ramanujan's identities over the localization of `ℤ` at `p`

## Main results

* `EisensteinSeries.Θ_E₂_int`: `12 Θ E₂ = E₂² - E₄`
* `EisensteinSeries.Θ_E₄_int`: `3 Θ E₄ = E₂E₄ - E₆`
* `EisensteinSeries.Θ_E₆_int`: `2 Θ E₆ = E₂E₆ - E₄²`
-/

@[expose] public noncomputable section

open PowerSeries ModularForm

variable {p : ℕ} [Fact p.Prime]

namespace EisensteinSeries

/-- **Ramanujan's identity** for `E₂` over `pLocalInt p`. -/
theorem Θ_E₂_int : 12 * Θ (R := pLocalInt p) E₂_int = E₂_int * E₂_int - E₄_int := by
  refine map_injective _ pLocalInt.algebraMap_injective ?_
  simpa [map_Θ, E₂_int_map, E₄_int_map, map_ofNat] using Θ_E₂Rat

/-- **Ramanujan's identity** for `E₄` over `pLocalInt p`. -/
theorem Θ_E₄_int : 3 * Θ (R := pLocalInt p) E₄_int = E₂_int * E₄_int - E₆_int := by
  refine map_injective _ pLocalInt.algebraMap_injective ?_
  simpa [map_Θ, E₄_int_map, E₂_int_map, E₆_int_map, map_ofNat] using Θ_E₄Rat

/-- **Ramanujan's identity** for `E₆` over `pLocalInt p`. -/
theorem Θ_E₆_int : 2 * Θ (R := pLocalInt p) E₆_int = E₂_int * E₆_int - E₄_int * E₄_int := by
  refine map_injective _ pLocalInt.algebraMap_injective ?_
  simpa [map_Θ, E₆_int_map, map_sub, E₂_int_map, E₄_int_map, E₆_int_map, map_ofNat] using Θ_E₆Rat

end EisensteinSeries
