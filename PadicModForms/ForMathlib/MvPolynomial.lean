/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Additional lemmas about multivariable polynomials

Two unrelated additions to Mathlib.

`MvPolynomial.basisRestrictSupport R s` is the canonical `R`-basis, indexed by `s`, of the
submodule of polynomials supported on a set `s` of exponent vectors. It is defined through its
`repr`, so we record the value of the basis itself: the member indexed by `d` is the monomial
`X ^ d`.

We also show that a weighted homogeneous polynomial lifts, along a surjective map of coefficient
rings, to a weighted homogeneous polynomial of the same weight.
-/

@[expose] public section

namespace MvPolynomial

/-! ### The monomial basis of `restrictSupport` -/

variable {σ R : Type*} [CommSemiring R] (s : Set (σ →₀ ℕ)) (d : s)

/-- The coordinates of `basisRestrictSupport R s` are the coefficients. -/
@[simp]
theorem basisRestrictSupport_repr_apply (x : restrictSupport R s) (i : s) :
    (basisRestrictSupport R s).repr x i = coeff (i : σ →₀ ℕ) (x : MvPolynomial σ R) :=
  rfl

/-- The member of `basisRestrictSupport R s` indexed by `d : s` is the monomial `X ^ d`. -/
theorem basisRestrictSupport_apply : basisRestrictSupport R s d =
    ⟨monomial (d : σ →₀ ℕ) 1, (monomial_mem_restrictSupport R).2 (.inl d.2)⟩ := by
  classical
  rw [Module.Basis.apply_eq_iff]
  ext i
  simp [Finsupp.single_apply, ← Subtype.coe_inj]

@[simp]
theorem basisRestrictSupport_apply_coe :
    (basisRestrictSupport R s d : MvPolynomial σ R) = monomial (d : σ →₀ ℕ) 1 := by
  rw [basisRestrictSupport_apply]

/-! ### Lifting a weighted homogeneous polynomial -/

variable {S M : Type*} [CommSemiring S] [AddCommMonoid M]

/-- Reducing coefficients commutes with taking a weighted homogeneous component. -/
theorem map_weightedHomogeneousComponent (f : R →+* S) (w : σ → M) (n : M) (P : MvPolynomial σ R) :
    (weightedHomogeneousComponent w n P).map f = weightedHomogeneousComponent w n (P.map f) := by
  classical
  ext d
  simp [coeff_weightedHomogeneousComponent, coeff_map, apply_ite f]

/-- A weighted homogeneous polynomial lifts to a weighted homogeneous polynomial. -/
theorem exists_map_eq_of_isWeightedHomogeneous {f : R →+* S} (hf : Function.Surjective f)
    {w : σ → M} {n : M} {P : MvPolynomial σ S} (hP : IsWeightedHomogeneous w P n) :
    ∃ Q : MvPolynomial σ R, IsWeightedHomogeneous w Q n ∧ Q.map f = P := by
  obtain ⟨Q, rfl⟩ := map_surjective f hf P
  refine ⟨_, weightedHomogeneousComponent_isWeightedHomogeneous n Q, ?_⟩
  rw [map_weightedHomogeneousComponent, hP.weightedHomogeneousComponent_same]

end MvPolynomial
