/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Order.WithBotTop
public import Mathlib.Topology.Instances.Int
public import Mathlib.Topology.Order.WithTop

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

/-- An element of `EInt` that is neither infinite is an integer. -/
theorem exists_intCast_eq (h₁ : x ≠ ⊥) (h₂ : x ≠ ⊤) : ∃ m : ℤ, x = m := by
  induction x using WithBotTop.rec with
  | bot => simp_all
  | coe k => exact ⟨k, rfl⟩
  | top => simp_all

-- should go to Mathlib.Order.WithBotTop, where `WithBotTop.coe` should also be tagged `@[coe]`,
-- allowing this lemma to be `@[norm_cast]` like `WithTop.coe_add` and `WithBot.coe_add`
/-- The inclusion of `ι` into `WithBotTop ι` is additive. -/
theorem WithBotTop.coe_add {ι : Type*} [AddMonoid ι] (a b : ι) :
    ((a + b : ι) : WithBotTop ι) = (a : WithBotTop ι) + b :=
  rfl

/-- Adding a finite element of `EInt` commutes with taking an infimum: translation by an integer
is an order isomorphism of `EInt`. -/
theorem intCast_add_iInf {α : Sort*} (m : ℤ) (g : α → EInt) :
    (m : EInt) + ⨅ n, g n = ⨅ n, ((m : EInt) + g n) := by
  refine le_antisymm (le_iInf fun n ↦ add_le_add le_rfl (iInf_le _ n)) ?_
  suffices (-m : ℤ) + ⨅ n, m + g n ≤ ⨅ n, g n by
    calc _ = m + ((-m : ℤ) + ⨅ n, (m + g n)) := by
          rw [← add_assoc, ← WithBotTop.coe_add]; simp [WithBotTop.coe]
         _ ≤ _ := add_le_add le_rfl this
  refine le_iInf fun n ↦ ?_
  calc _ ≤ (-m : ℤ) + (m + g n) := add_le_add le_rfl (iInf_le _ n)
       _ = g n := by rw [← add_assoc, ← WithBotTop.coe_add]; simp [WithBotTop.coe]


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
