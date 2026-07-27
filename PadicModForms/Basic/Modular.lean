/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Topology.Algebra.Group.CompactOpen

public import PadicModForms.Basic.Rational
public import PadicModForms.WeightSpace.Defs

/-!
# p-adic modular forms

This file defines `p`-adic modular forms as limits of classical modular forms.
-/

@[expose] public section

open UpperHalfPlane PowerSeries ModularFormClass Filter

open scoped MatrixGroups Topology

variable {p : ℕ} [Fact p.Prime]

structure pAdicModularFormStruct (f : ℚ_[p]⟦X⟧) where
  F : ℕ → ℚ⟦X⟧
  w : ℕ → ℤ
  modF : ∀ i, (F i).isModularForm (w i)
  tendsTo : TendstoUniformly (fun i n ↦ (↑(coeff n (F i)) : ℚ_[p])) (coeff · f) atTop

variable (p)

def PowerSeries.isPAdicModularForm (f : ℚ_[p]⟦X⟧) := Nonempty (pAdicModularFormStruct f)

def PAdicModularForms := {f // isPAdicModularForm p f}

theorem powerSeries_isPAdicModularForm_of_qExpansion_eq_map {g : ℚ⟦X⟧}
    (hg : ∃ k : ℤ, g.isModularForm k) : isPAdicModularForm p (g.map (algebraMap _ _)) := by
  rcases hg with ⟨k, f, hg⟩
  refine ⟨⟨fun _ ↦ g, fun _ ↦ k, fun i ↦ ⟨f, hg⟩, fun u hu ↦ ?_⟩⟩
  filter_upwards with i n
  simpa using refl_mem_uniformity hu
