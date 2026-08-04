/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ModP.Basic
public import PadicModForms.pLocalInt.Eisenstein

/-!
# Eisenstein series modulo `p`

This file specializes the integral Eisenstein series to weight `p - 1`, and reduces `E₄` and
`E₆` modulo `p`. The general integral construction is in `PadicModForms.pLocalInt.Eisenstein`.
-/

@[expose] public noncomputable section

open PowerSeries ArithmeticFunction sigma ModularForm

variable {p : ℕ} [Fact p.Prime]

namespace EisensteinSeries

/-! ### Weight `p - 1` -/

namespace ModP

/-- The normalized Eisenstein series of weight `p - 1` over the localization of `ℤ` at `p`. -/
noncomputable abbrev E (hp : 5 ≤ p) : (pLocalInt p)⟦X⟧ :=
  E_int (k := p - 1) (by lia) ((Fact.out : p.Prime).even_sub_one (by lia))
    (inv_bernoulli_mem_pLocalInt (by lia) ((Fact.out : p.Prime).even_sub_one (by lia)) dvd_rfl)

/-- `E` is a `p`-integral modular form of weight `p - 1`. -/
theorem E_mem_pLocalIntModularForms (hp : 5 ≤ p) :
    E hp ∈ pLocalIntModularForms p (↑(p - 1)) :=
  E_int_mem_pLocalIntModularForms (by lia) ((Fact.out : p.Prime).even_sub_one (by lia))
    (inv_bernoulli_mem_pLocalInt (by lia) ((Fact.out : p.Prime).even_sub_one (by lia)) dvd_rfl)

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
    E_int_map (p := p) (k := p - 1) (by lia) ((Fact.out : p.Prime).even_sub_one (by lia))
      (inv_bernoulli_mem_pLocalInt (by lia) ((Fact.out : p.Prime).even_sub_one (by lia)) dvd_rfl)

end ModP

/-! ### Reduction of `E₄` and `E₆` modulo `p` -/

/-- The reduction of `E₄_int` modulo `p`. -/
def E₄ModP : (ZMod p)⟦X⟧ := E₄_int.map pLocalInt.toZMod

/-- The reduction of `E₆_int` modulo `p`. -/
def E₆ModP : (ZMod p)⟦X⟧ := E₆_int.map pLocalInt.toZMod

/-- `E₄ModP` is a mod-`p` modular form of weight `4`. -/
theorem E₄ModP_mem_modPModularForms : E₄ModP ∈ modPModularForms p 4 :=
  ⟨_, _, E₄_int_map, rfl⟩

/-- `E₆ModP` is a mod-`p` modular form of weight `6`. -/
theorem E₆ModP_mem_modPModularForms : E₆ModP ∈ modPModularForms p 6 :=
  ⟨_, _, E₆_int_map, rfl⟩

end EisensteinSeries
