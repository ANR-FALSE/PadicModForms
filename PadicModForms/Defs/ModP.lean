/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.Defs.Modular
public import PadicModForms.ForMathlib.IntLocalization

/-!
# Modular forms modulo `p`

This file defines modular forms modulo `p`.
-/

@[expose] public section

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- A power series with coefficients in `ℤ/pℤ` is a mod-`p` modular form of weight `k` if it is
the reduction of a power series with coefficients in the localization of `ℤ` at `p` whose base
change to `ℚ` is a modular form of weight `k`. -/
def PowerSeries.isModPModularForm (k : ℤ) (f : (ZMod p)⟦X⟧) : Prop :=
  ∃ g : (pLocalInt p)⟦X⟧, (g.map (algebraMap _ _)).isModularForm k ∧
    g.map pLocalInt.toZMod = f
