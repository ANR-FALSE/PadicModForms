/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ModP.Basic
public import PadicModForms.pLocalInt.Eisenstein

/-!
# The weight `p - 1` Eisenstein series used modulo `p`

This file specializes the integral Eisenstein series to weight `p - 1`. The general integral
construction is in `PadicModForms.pLocalInt.Eisenstein`.
-/

@[expose] public noncomputable section

open PowerSeries ArithmeticFunction sigma ModularForm

variable {p : ℕ} [Fact p.Prime]

namespace EisensteinSeries

namespace ModP

/-- The normalized Eisenstein series of weight `p - 1` over the localization of `ℤ` at `p`. -/
noncomputable abbrev E (hp : 5 ≤ p) : (pLocalInt p)⟦X⟧ :=
  E_int (k := p - 1) (by lia) ((Fact.out : p.Prime).even_sub_one (by lia)) dvd_rfl

/-- The coefficients of `E`. -/
@[simp]
theorem coeff_E (hp : 5 ≤ p) (m : ℕ) : (coeff m (E hp) : pLocalInt p) =
    if m = 0 then 1 else -(2 * (p - 1) / bernoulli (p - 1)) * σ (p - 2) m := by
  rw [E, coeff_E_int, Nat.cast_sub (by lia : 1 ≤ p)]
  congr 2

/-- The scalar extension of `E` to `ℚ` is the rational `q`-expansion of `ERat` of weight
`p - 1`. -/
theorem E_map_eq_rationalQExpansion (hp : 5 ≤ p) :
    (E hp).map (algebraMap _ ℚ) =
      rationalQExpansion (ERat (by lia) ((Fact.out : p.Prime).even_sub_one (by lia))) := by
  simpa [Nat.cast_sub (by lia : 1 ≤ p)] using
    E_int_map (p := p) (k := p - 1) (by lia) ((Fact.out : p.Prime).even_sub_one (by lia)) dvd_rfl

end ModP

end EisensteinSeries
