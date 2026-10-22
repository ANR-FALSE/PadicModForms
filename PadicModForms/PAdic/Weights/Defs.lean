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

This file relates the classical integral weights in a presentation of a nonzero p-adic modular form
to its limiting p-adic weight: Serre's **Théorème 2**, for `p ≥ 5`. The weights `S.w i` of a
presentation `S` are Cauchy for the moduli `(p - 1) p ^ (m - 1)`, by Théorème 1 for the presentation
(`pAdicModularFormStruct.exists_forall_dvd_sub`), hence converge in weight space
(`WeightSpace.exists_tendsto_ι_of_forall_exists_dvd`). Two presentations have eventually congruent
weights (`pAdicModularFormStruct.eventually_dvd_sub`), hence the same limit
(`WeightSpace.eq_of_tendsto_ι_of_forall_eventually_dvd`). The weight `w` of a `p`-adic modular form
is that limit.

From this file on, the hypothesis `5 ≤ p` is the instance argument `[Fact (5 ≤ p)]`.
-/

open PowerSeries Filter Topology

variable {p : ℕ} [Fact p.Prime] [Fact (5 ≤ p)] {f : ℚ_[p]⟦X⟧}

/-- **Serre's Théorème 2, existence**, for `p ≥ 5`: the classical weights of a presentation of
a nonzero `p`-adic modular form converge in weight space. -/
public theorem w_tendsto (hf : f ≠ 0) (S : pAdicModularFormStruct f) :
    ∃ (x : X_[p]), Tendsto (fun i ↦ ι (S.w i)) atTop (𝓝 x) :=
  WeightSpace.exists_tendsto_ι_of_forall_exists_dvd (S.exists_forall_dvd_sub Fact.out hf)

/-- **Serre's Théorème 2, uniqueness**, for `p ≥ 5`: the limit of the classical weights does not
depend on the presentation. -/
public theorem limit_unique (hf : f ≠ 0) (S S' : pAdicModularFormStruct f)
    {x x' : X_[p]}
    (hx : Tendsto (fun i ↦ ι (S.w i)) atTop (𝓝 x))
    (hx' : Tendsto (fun i ↦ ι (S'.w i)) atTop (𝓝 x')) : x = x' :=
  WeightSpace.eq_of_tendsto_ι_of_forall_eventually_dvd hx hx' (S.eventually_dvd_sub Fact.out S' hf)

open Classical in
/-- The p-adic weight of a p-adic modular form, for `p ≥ 5`. -/
@[expose] public noncomputable def w (f : PAdicModularForms p) : X_[p] :=
  if hf0 : f = 0 then ι 0
  else (w_tendsto (PAdicModularForms.val_eq_zero_iff.not.2 hf0) (choice f.2)).choose

open Classical in
theorem w_def (f : PAdicModularForms p) :
    w f = if hf0 : f = 0 then ι 0
      else (w_tendsto (PAdicModularForms.val_eq_zero_iff.not.2 hf0) (choice f.2)).choose := rfl

/-- The classical weights of the presentation chosen to define `w` converge to `w`. -/
theorem tendsto_ι_w {f : PAdicModularForms p} (hf0 : f ≠ 0) :
    Tendsto (fun i ↦ ι ((Classical.choice f.2).w i)) atTop (𝓝 (w f)) := by
  simpa [w_def, hf0] using (w_tendsto (PAdicModularForms.val_eq_zero_iff.not.2 hf0)
    (Classical.choice f.2)).choose_spec

/-- The weight of a nonzero `p`-adic modular form is the limit of the classical weights of any
of its presentations. -/
public theorem w_eq_of_tendsto {f : PAdicModularForms p} (hf0 : f ≠ 0)
    (S : pAdicModularFormStruct f.1) {x : X_[p]} (hx : Tendsto (fun i ↦ ι (S.w i)) atTop (𝓝 x)) :
    w f = x :=
  limit_unique (PAdicModularForms.val_eq_zero_iff.not.2 hf0) _ S (tendsto_ι_w hf0) hx
