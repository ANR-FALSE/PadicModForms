/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ModP.Congruences
public import PadicModForms.pLocalInt.Ramanujan

/-!
# Ramanujan's identities modulo `p`

The reductions of `E₂`, `E₄`, `E₆` modulo `p` are the series Serre writes `P`, `Q`, `R`. The
`12 Θ` forms are the ones used by the differential identity, where the coefficient of `E₂` is the
weight.

## Main results

* `EisensteinSeries.Θ_E₂ModP`: `12 Θ E₂ = E₂² - E₄`
* `EisensteinSeries.Θ_E₄ModP`, `EisensteinSeries.twelve_Θ_E₄ModP`: `3 Θ E₄ = E₂E₄ - E₆`,
  `12 Θ E₄ = 4E₂E₄ - 4E₆`
* `EisensteinSeries.Θ_E₆ModP`, `EisensteinSeries.twelve_Θ_E₆ModP`: `2 Θ E₆ = E₂E₆ - E₄²`,
  `12 Θ E₆ = 6E₂E₆ - 6E₄²`
-/

@[expose] public noncomputable section

open PowerSeries ModularForm

variable {p : ℕ} [Fact p.Prime]

namespace EisensteinSeries

/-- The reduction of `E₂_int` modulo `p`. This is Serre's `P`. -/
def E₂ModP : (ZMod p)⟦X⟧ := E₂_int.map pLocalInt.toZMod

/-- `E₂ModP` is a mod-`p` modular form of weight `p + 1`, by Serre's congruence. -/
theorem E₂ModP_mem_modPModularForms (hp5 : 5 ≤ p) : E₂ModP ∈ modPModularForms p ((p + 1 : ℕ) : ℤ) :=
  E₂_int_map_toZMod_mem_modPModularForms hp5

/-- **Ramanujan's identity** for `E₂` modulo `p`: `12 Θ E₂ = E₂² - E₄`. -/
theorem Θ_E₂ModP : 12 * Θ (ZMod p) E₂ModP = E₂ModP * E₂ModP - E₄ModP := by
  simpa [E₂ModP, E₄ModP, map_Θ, map_ofNat] using congrArg (map (pLocalInt.toZMod (p := p))) Θ_E₂_int

/-- **Ramanujan's identity** for `E₄` modulo `p`: `3 Θ E₄ = E₂E₄ - E₆`. -/
theorem Θ_E₄ModP : 3 * Θ (ZMod p) E₄ModP = E₂ModP * E₄ModP - E₆ModP := by
  simpa [E₂ModP, E₄ModP, E₆ModP, map_Θ, map_ofNat] using
    congrArg (map (pLocalInt.toZMod (p := p))) Θ_E₄_int

/-- **Ramanujan's identity** for `E₆` modulo `p`: `2 Θ E₆ = E₂E₆ - E₄²`. -/
theorem Θ_E₆ModP : 2 * Θ (ZMod p) E₆ModP = E₂ModP * E₆ModP - E₄ModP * E₄ModP := by
  simpa [E₂ModP, E₄ModP, E₆ModP, map_Θ, map_ofNat] using
    congrArg (PowerSeries.map (pLocalInt.toZMod (p := p))) Θ_E₆_int

/-- `12 Θ E₄ = 4E₂E₄ - 4E₆`, weight-normalized. -/
theorem twelve_Θ_E₄ModP : 12 * Θ (ZMod p) E₄ModP = 4 * (E₂ModP * E₄ModP) - 4 * E₆ModP :=
  calc _ = 4 * (3 * Θ (ZMod p) E₄ModP) := by ring
    _ = _ := by rw [Θ_E₄ModP]; ring

/-- `12 Θ E₆ = 6E₂E₆ - 6E₄²`, weight-normalized. -/
theorem twelve_Θ_E₆ModP :
    12 * Θ (ZMod p) E₆ModP = 6 * (E₂ModP * E₆ModP) - 6 * (E₄ModP * E₄ModP) :=
  calc _ = 6 * (2 * Θ (ZMod p) E₆ModP) := by ring
    _ = _ := by rw [Θ_E₆ModP]; ring

end EisensteinSeries
