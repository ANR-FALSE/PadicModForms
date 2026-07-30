/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib

/-!
# The extended integers

Order facts about `EInt = WithBotTop ℤ` and the topology of `EInt`.
-/

@[expose] public section

open Filter Topology

variable {x : EInt}

/-- An element of `EInt` is `≠ ⊥` if it is bounded below by an integer. -/
theorem eint_ne_bot_iff : x ≠ ⊥ ↔ ∃ m : ℤ, m ≤ x := by
  induction x using WithBotTop.rec with
  | bot => simp
  | coe k => exact ⟨fun _ ↦ ⟨k, le_rfl⟩, fun _ ↦ by simp⟩
  | top => exact ⟨fun _ ↦ ⟨0, le_top⟩, fun _ ↦ by simp⟩

theorem eint_ne_bot_of_nonneg (hx : 0 ≤ x) : x ≠ ⊥ := fun h ↦ by simp_all

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
