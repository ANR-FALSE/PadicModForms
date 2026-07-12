/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Topology.Algebra.Group.CompactOpen

public import PadicModForms.WeightSpace.Defs

/-!
# p-adic modular forms

This file defines `p`-adic modular forms as limits of classical modular forms.
-/

@[expose] public section

open UpperHalfPlane PowerSeries ModularFormClass Filter

open scoped Topology

variable {p : ℕ} [Fact p.Prime] (n : ℕ)

structure pAdicModularFormStruct (f : ℚ_[p]⟦X⟧) where
  F : ℕ → ℚ⟦X⟧
  w : ℕ → ℤ
  modF : ∀ i, ∃ (g : ModularForm (CongruenceSubgroup.Gamma n) (w i)),
    qExpansion n g = (F i).map (algebraMap ℚ ℂ)
  tendsTo : TendstoUniformly (fun i n ↦ (↑(coeff n (F i)) : ℚ_[p])) (coeff · f) atTop

variable (p)

def PowerSeries.isPAdicModularForm (f : ℚ_[p]⟦X⟧) := Nonempty (pAdicModularFormStruct n f)

def PAdicModularForms (n : ℕ) := {f // isPAdicModularForm p n f}

theorem powerSeries_isPAdicModularForm_of_qExpansion_eq_map {g : ℚ⟦X⟧}
    (hg : ∃ (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma n) k),
      qExpansion n f = g.map (algebraMap ℚ ℂ)) :
    PowerSeries.isPAdicModularForm p n (g.map (algebraMap ℚ ℚ_[p])) := by
  rcases hg with ⟨k, f, hg⟩
  refine ⟨⟨fun _ ↦ g, fun _ ↦ k, fun i ↦ ⟨f, hg⟩, fun u hu ↦ ?_⟩⟩
  filter_upwards with i n
  simpa using refl_mem_uniformity hu
