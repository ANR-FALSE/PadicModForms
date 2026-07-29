/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Algebra.DirectSum.Ring

/-!
# Additional lemmas about direct sums

This file contains elementary lemmas about direct sums that are missing from Mathlib.
-/

@[expose] public section

namespace DirectSum

variable {ι : Type*} [DecidableEq ι] {A B : ι → Type*} [∀ i, AddCommMonoid (A i)]
  [∀ i, AddCommMonoid (B i)]

/-- Mapping each summand into the corresponding summand and then adding agrees with the
componentwise map. -/
@[simp]
theorem toAddMonoid_of_comp (f : ∀ i, A i →+ B i) :
    toAddMonoid (fun i ↦ (of B i).comp (f i)) = map f := by
  apply addHom_ext
  intro i x
  simp

end DirectSum
