/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib

/-!
# Topology of the extended integers
-/

@[expose] public section

open Filter Topology

-- should go to Mathlib.Topology.Instances.EInt (new file, analogous to
-- Mathlib.Topology.Instances.ENat)
theorem tendsto_eint_nhds_top_iff {α : Type*} {l : Filter α} {u : α → EInt} :
    Tendsto u l (𝓝 (⊤ : EInt)) ↔ ∀ k : ℤ, ∀ᶠ a in l, (k : EInt) ≤ u a := by
  refine ⟨fun hu k ↦ hu.eventually (Ici_mem_nhds (WithBotTop.coe_ne_top k).lt_top), fun h ↦ ?_⟩
  rw [nhds_top_basis.tendsto_right_iff]
  intro a ha
  induction a using WithBotTop.rec with
  | bot => exact (h 0).mono fun x hx ↦ lt_of_lt_of_le (by simp [bot_lt_iff_ne_bot]) hx
  | coe k => exact (h (k + 1)).mono fun x hx ↦ lt_of_lt_of_le (by simp) hx
  | top => exact (lt_irrefl _ ha).elim
