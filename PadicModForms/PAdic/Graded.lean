/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.PAdic.Basic

/-!
# Weights of p-adic modular forms

This file relates the classical integral weights in a presentation of a nonzero p-adic modular
form to its limiting p-adic weight.
-/

@[expose] public section

open PowerSeries Filter Topology

variable {p : ℕ} [Fact p.Prime]

theorem w_tendsto {f : ℚ_[p]⟦X⟧} (hf : f ≠ 0) (S : pAdicModularFormStruct f) :
    ∃ (x : X_[p]), Tendsto (fun i ↦ ι (S.w i)) atTop (𝓝 x) := by
  sorry

theorem limit_unique {f : ℚ_[p]⟦X⟧} (hf : f ≠ 0) (S S' : pAdicModularFormStruct f)
    {x x' : X_[p]}
    (hx : Tendsto (fun i ↦ ι (S.w i)) atTop (𝓝 x))
    (hx' : Tendsto (fun i ↦ ι (S'.w i)) atTop (𝓝 x')) : x = x' := by
  sorry

open Classical in
/-- The p-adic weight of a p-adic modular form. -/
noncomputable def w {f : ℚ_[p]⟦X⟧} (hf : f.isPAdicModularForm p) : X_[p] :=
  if hf0 : f = 0 then ι 0 else (w_tendsto hf0 (choice hf)).choose
