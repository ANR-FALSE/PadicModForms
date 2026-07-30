/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The monomial basis of `MvPolynomial.restrictSupport`

`MvPolynomial.basisRestrictSupport R s` is the canonical `R`-basis, indexed by `s`, of the
submodule of polynomials supported on a set `s` of exponent vectors. It is defined through its
`repr`, so this file records the value of the basis itself: the member indexed by `d` is the
monomial `X ^ d`.
-/

@[expose] public section

namespace MvPolynomial

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

end MvPolynomial
