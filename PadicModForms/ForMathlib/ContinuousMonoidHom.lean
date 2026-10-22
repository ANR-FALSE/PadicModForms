/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Pointwise inverse and quotient of continuous monoid homomorphisms

The group structure on `A →ₜ* E`, for a commutative topological group `E`, is pointwise. Mathlib
records this for the product (`ContinuousMonoidHom.mul_apply`); this file records it for the
inverse and the quotient.
-/

public section

namespace ContinuousMonoidHom

variable {A E : Type*} [Monoid A] [TopologicalSpace A] [CommGroup E] [TopologicalSpace E]
  [IsTopologicalGroup E]

-- should go to Mathlib.Topology.Algebra.ContinuousMonoidHom
@[to_additive (attr := simp)]
theorem inv_apply (f : A →ₜ* E) (a : A) : f⁻¹ a = (f a)⁻¹ := rfl

-- should go to Mathlib.Topology.Algebra.ContinuousMonoidHom
@[to_additive (attr := simp)]
theorem div_apply (f g : A →ₜ* E) (a : A) : (f / g) a = f a / g a := rfl

end ContinuousMonoidHom
