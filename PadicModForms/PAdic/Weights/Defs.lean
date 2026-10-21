/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Topology.Algebra.Group.CompactOpen
public import PadicModForms.PAdic.Defs
import PadicModForms.PAdic.Weights.Presentation
import PadicModForms.PAdic.Weights.Topology
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.NormNum.Parity

/-!
# Weights of p-adic modular forms

This file relates the classical integral weights in a presentation of a nonzero p-adic modular
form to its limiting p-adic weight: Serre's **Théorème 2**. The weights `S.w i` of a presentation
`S` are Cauchy for the moduli `(p - 1) p ^ (m - 1)`, by Théorème 1 for the presentation
(`pAdicModularFormStruct.exists_forall_dvd_sub`), hence converge in weight space
(`WeightSpace.exists_tendsto_ι_of_forall_exists_dvd`). Two presentations have eventually
congruent weights (`pAdicModularFormStruct.eventually_dvd_sub`), hence the same limit
(`WeightSpace.eq_of_tendsto_ι_of_forall_eventually_dvd`). The weight `w` of a `p`-adic modular
form is that limit.
-/

@[expose] public section

open PowerSeries Filter Topology

variable {p : ℕ} [Fact p.Prime] {f : ℚ_[p]⟦X⟧}

/-- **Serre's Théorème 2, existence**: the classical weights of a presentation of a nonzero
`p`-adic modular form converge in weight space. -/
theorem w_tendsto (hf : f ≠ 0) (S : pAdicModularFormStruct f) :
    ∃ (x : X_[p]), Tendsto (fun i ↦ ι (S.w i)) atTop (𝓝 x) :=
  WeightSpace.exists_tendsto_ι_of_forall_exists_dvd (S.exists_forall_dvd_sub hf)

/-- **Serre's Théorème 2, uniqueness**: the limit of the classical weights does not depend on
the presentation. -/
theorem limit_unique (hf : f ≠ 0) (S S' : pAdicModularFormStruct f)
    {x x' : X_[p]}
    (hx : Tendsto (fun i ↦ ι (S.w i)) atTop (𝓝 x))
    (hx' : Tendsto (fun i ↦ ι (S'.w i)) atTop (𝓝 x')) : x = x' :=
  WeightSpace.eq_of_tendsto_ι_of_forall_eventually_dvd hx hx' (S.eventually_dvd_sub S' hf)

open Classical in
/-- The p-adic weight of a p-adic modular form. -/
noncomputable def w (hf : f.isPAdicModularForm p) : X_[p] :=
  if hf0 : f = 0 then ι 0 else (w_tendsto hf0 (choice hf)).choose
