/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Basic
public import PadicModForms.ForMathlib.WeightedHomogeneous
import PadicModForms.ForMathlib.Finsupp

/-!
# Additional lemmas about multivariable polynomials

Several additions to Mathlib.

`MvPolynomial.basisRestrictSupport R s` is the canonical `R`-basis, indexed by `s`, of the
submodule of polynomials supported on a set `s` of exponent vectors. It is defined through its
`repr`, so we record the value of the basis itself: the member indexed by `d` is the monomial
`X ^ d`.

We also show that a weighted homogeneous polynomial lifts, along a surjective map of coefficient
rings, to a weighted homogeneous polynomial of the same weight, and that a weighted homogeneous
polynomial does not involve the variables whose weight exceeds its own. Finally, a sum of two
distinct monomials with nonzero coefficients is not a monomial, and over a field such a binomial
is irreducible when its exponents are positive and coprime.
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

/-! ### Partial derivatives in a variable that is too heavy -/

/-- A polynomial that is weighted homogeneous of weight `n` does not involve a variable of weight
larger than `n`, so its partial derivative in that variable vanishes. -/
theorem IsWeightedHomogeneous.pderiv_eq_zero {w : σ → ℕ} {n : ℕ} {i : σ} {P : MvPolynomial σ R}
    (hP : IsWeightedHomogeneous w P n) (hn : n < w i) : pderiv i P = 0 := by
  refine pderiv_eq_zero_of_notMem_vars fun hi ↦ absurd hn (not_lt.2 ?_)
  obtain ⟨d, hd, hdi⟩ := (mem_vars_iff_mem_support i).1 hi
  exact hP (mem_support_iff.1 hd) ▸ Finsupp.le_weight_of_ne_zero' w (Finsupp.mem_support_iff.1 hdi)

/-! ### Binomials -/

/-- A sum of two monomials in `Fin 2` variables with distinct exponent vectors and nonzero
coefficients is not a monomial. -/
theorem not_exists_eq_monomial_add_monomial {m n : ℕ} {a b : R}
    (hmn : (Finsupp.single (0 : Fin 2) m) ≠ Finsupp.single 1 n) (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ ∃ d r, monomial (Finsupp.single (0 : Fin 2) m) a + monomial (Finsupp.single 1 n) b =
      monomial d r := fun h ↦ by
  set P := monomial (Finsupp.single (0 : Fin 2) m) a + monomial (Finsupp.single 1 n) b
  obtain ⟨d, r, h⟩ := h
  have h0 : coeff (Finsupp.single 0 m) P = a := by simp [P, coeff_monomial, hmn.symm]
  have h1 : coeff (Finsupp.single 1 n) P = b := by simp [P, coeff_monomial, hmn]
  rcases eq_or_ne d (Finsupp.single 0 m) with rfl | H
  · exact hmn (by simp_all)
  · simp_all

/-- Over a field, a binomial in `Fin 2` variables with nonzero coefficients and positive coprime
exponents is irreducible. -/
theorem irreducible_add_monomial_of_coprime {K : Type*} [Field K] {m n : ℕ} {a b : K}
    (hm : 0 < m) (hn : 0 < n) (hc : m.Coprime n) (ha : a ≠ 0) (hb : b ≠ 0) :
    Irreducible (monomial (Finsupp.single (0 : Fin 2) m) a +
      monomial (Finsupp.single 1 n) b) := by
  let w : Fin 2 → ℕ := ![n, m]
  refine IsWeightedHomogeneous.irreducible_of_unique_lower_weight (w := w) (n := m * n)
    (IsWeightedHomogeneous.add ?_ ?_) (fun i ↦ ?_) (fun k _ hk d e hd he ↦ ?_)
    (not_exists_eq_monomial_add_monomial (fun h ↦ ?_) ha hb)
  · apply isWeightedHomogeneous_monomial
    simp [w, Finsupp.weight_eq_sum, Fin.sum_univ_two, mul_comm]
  · apply isWeightedHomogeneous_monomial
    simp [w, Finsupp.weight_eq_sum, Fin.sum_univ_two, mul_comm]
  · fin_cases i <;> simp [w, hm.ne', hn.ne']
  · exact Finsupp.eq_of_weight_eq_of_lt_lcm hn hm
      (by rwa [Nat.Coprime.lcm_eq_mul (hc.symm), mul_comm]) hd he
  · exact hm.ne' (by simpa using Finsupp.ext_iff.1 h 0)

end MvPolynomial
