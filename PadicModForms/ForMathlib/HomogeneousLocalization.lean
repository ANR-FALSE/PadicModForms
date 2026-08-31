/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Normality of the degree-zero part of a homogeneous localization

Let `A` be a graded domain and `f` a nonzero homogeneous element.
`HomogeneousLocalization.Away 𝒜 f` is the degree-zero subring of the localization `A[1/f]`. This
file proves that it is a domain and that it is integrally closed in its fraction field whenever
`A` is.

## Main results

* `HomogeneousLocalization.Away.isDomain`: `Away 𝒜 f` is a domain when `A` is and `f ≠ 0`.
* `HomogeneousLocalization.Away.exists_val_eq_of_mul_val_eq`: an element of `A[1/f]` that is a
  quotient of two degree-zero elements has degree zero.
* `HomogeneousLocalization.Away.isIntegrallyClosed`: `Away 𝒜 f` is integrally closed when `A` is.
-/

@[expose] public section

namespace HomogeneousLocalization

variable {ι A σ : Type*} [AddCancelCommMonoid ι] [DecidableEq ι]
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜] {f : A}

-- should go to Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
/-- The degree-zero part of the localization of a domain away from `f ≠ 0` is a domain: `val` is
injective into `Localization.Away f`, which is a domain because `0` is not a power of `f`. -/
theorem Away.isDomain [IsDomain A] (hf : f ≠ 0) : IsDomain (Away 𝒜 f) := by
  sorry

variable {𝒜}

-- should go to Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
/-- An element `x` of `Localization.Away f` satisfying `x * w.val = u.val` with `u` and `w` of
degree zero and `w ≠ 0` is itself of degree zero. Writing `x = F / f ^ N`, clearing denominators
gives an equation in `A` whose right-hand side is homogeneous, and comparing homogeneous
components shows that `F` may be taken homogeneous of degree `N • d`. -/
theorem Away.exists_val_eq_of_mul_val_eq [IsDomain A] {d : ι} (hd : f ∈ 𝒜 d) (hf : f ≠ 0)
    {x : Localization.Away f} {u w : Away 𝒜 f} (hw : w ≠ 0) (h : x * w.val = u.val) :
    ∃ y : Away 𝒜 f, y.val = x := by
  sorry

-- should go to Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
/-- **The degree-zero part of the localization of an integrally closed graded domain away from a
nonzero homogeneous element is integrally closed.** An integral element of the fraction field of
`Away 𝒜 f` lies in `Localization.Away f` because the latter is integrally closed
(`isIntegrallyClosed_of_isLocalization`), and it is a quotient of two degree-zero elements, so
`Away.exists_val_eq_of_mul_val_eq` applies. -/
theorem Away.isIntegrallyClosed [IsDomain A] [IsIntegrallyClosed A] {d : ι} (hd : f ∈ 𝒜 d)
    (hf : f ≠ 0) : IsIntegrallyClosed (Away 𝒜 f) := by
  sorry

end HomogeneousLocalization
