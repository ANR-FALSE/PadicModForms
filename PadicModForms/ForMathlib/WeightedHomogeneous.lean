/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Degree.Monomial
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted homogeneous polynomials

A polynomial which is weighted homogeneous of weighted degree `0` is a constant, and, over a
domain, every nonzero factor of a nonzero weighted homogeneous multivariate polynomial is itself
weighted homogeneous.

## Main results

* `MvPolynomial.IsWeightedHomogeneous.exists_eq_monomial_of_unique_weight`: a weighted homogeneous
  polynomial is a monomial when its weighted-degree fiber has at most one element.
* `MvPolynomial.IsWeightedHomogeneous.eq_C_coeff_zero`: a polynomial which is weighted homogeneous
  of weighted degree `0`, for a weight function taking no zero value, is a constant; over a field
  it is a unit as soon as it is nonzero (`MvPolynomial.IsWeightedHomogeneous.isUnit_of_ne_zero`).
* `MvPolynomial.IsWeightedHomogeneous.mul_factors`: if a product of two nonzero polynomials is
  weighted homogeneous, both factors are, and their weights add up.
* `MvPolynomial.IsWeightedHomogeneous.irreducible_factor`: every irreducible factor of a nonzero
  weighted homogeneous polynomial is weighted homogeneous.
-/

@[expose] public noncomputable section

open Finsupp Finset

namespace MvPolynomial

-- everything in this file should go to Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

variable {σ R : Type*}

/-- A weighted homogeneous polynomial is a monomial if at most one exponent vector has its
weighted degree. This includes the case in which no exponent vector has that degree: then the
polynomial is zero. -/
theorem IsWeightedHomogeneous.exists_eq_monomial_of_unique_weight [CommSemiring R]
    {M : Type*} [AddCommMonoid M] {w : σ → M} {φ : MvPolynomial σ R} {n : M}
    (hφ : IsWeightedHomogeneous w φ n)
    (hunique : ∀ d e : σ →₀ ℕ, weight w d = n → weight w e = n → d = e) :
    ∃ d r, φ = monomial d r := by
  by_cases hex : ∃ d : σ →₀ ℕ, weight w d = n
  · obtain ⟨d, hd⟩ := hex
    exact ⟨d, coeff d φ, hφ.eq_monomial_of_unique_weight fun e he ↦ hunique e d he hd⟩
  · exact ⟨0, 0, by simpa using hφ.eq_zero_of_no_monomials fun d hd ↦ hex ⟨d, hd⟩⟩

/-- A polynomial which is weighted homogeneous of weighted degree `0`, for a weight function taking
no zero value, is a constant. -/
theorem IsWeightedHomogeneous.eq_C_coeff_zero [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [PartialOrder M] [CanonicallyOrderedAdd M] [IsAddTorsionFree M] {w : σ → M}
    {φ : MvPolynomial σ R} (hw : ∀ i, w i ≠ 0) (hφ : IsWeightedHomogeneous w φ 0) :
    φ = C (coeff 0 φ) :=
  hφ.weightedHomogeneousComponent_same.symm.trans (weightedHomogeneousComponent_zero φ hw)

/-- Over a field, a nonzero polynomial which is weighted homogeneous of weighted degree `0`, for a
weight function taking no zero value, is a unit. -/
theorem IsWeightedHomogeneous.isUnit_of_ne_zero {K : Type*} [Field K] {M : Type*} [AddCommMonoid M]
    [PartialOrder M] [CanonicallyOrderedAdd M] [IsAddTorsionFree M] {w : σ → M}
    {φ : MvPolynomial σ K} (hw : ∀ i, w i ≠ 0) (hφ : IsWeightedHomogeneous w φ 0) (hφ0 : φ ≠ 0) :
    IsUnit φ := by
  refine hφ.eq_C_coeff_zero hw ▸ (isUnit_iff_ne_zero.mpr fun h ↦ hφ0 ?_).map C
  rw [hφ.eq_C_coeff_zero hw, h, map_zero]

variable [CommRing R] (w : σ → ℕ) (d : σ →₀ ℕ) (r : R) (P : MvPolynomial σ R) {n : ℕ}

/-- Record the weight grading in an auxiliary polynomial variable, while retaining each original
monomial as a coefficient. A monomial of weight `n` is sent to that monomial times `X ^ n`. -/
private def toWeightPolynomial : MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  eval₂Hom (Polynomial.C.comp C) fun i ↦ Polynomial.C (X i) * Polynomial.X ^ w i

private theorem toWeightPolynomial_monomial : toWeightPolynomial w (monomial d r) =
    Polynomial.monomial (weight w d) (monomial d r) := by
  rw [toWeightPolynomial, eval₂Hom_monomial, monomial_eq, ← Polynomial.C_mul_X_pow_eq_monomial,
    map_mul]
  simp only [prod, weight_apply, sum, map_prod, map_pow, mul_pow, prod_mul_distrib, ← pow_mul,
    prod_pow_eq_pow_sum, RingHom.comp_apply, smul_eq_mul, mul_comm]
  ring

private theorem eval_one_toWeightPolynomial : Polynomial.eval 1 (toWeightPolynomial w P) = P := by
  induction P using induction_on' with
  | monomial d r => simp [toWeightPolynomial_monomial]
  | add p q hp hq => simp [hp, hq]

/-- The coefficients of the auxiliary polynomial are the weighted homogeneous components. -/
private theorem coeff_toWeightPolynomial (n : ℕ) :
    (toWeightPolynomial w P).coeff n = weightedHomogeneousComponent w n P := by
  induction P using induction_on' with
  | monomial d r =>
    rw [toWeightPolynomial_monomial, Polynomial.coeff_monomial]
    split_ifs with h
    · exact (isWeightedHomogeneous_monomial w d r h).weightedHomogeneousComponent_same.symm
    · exact ((isWeightedHomogeneous_monomial w d r rfl).weightedHomogeneousComponent_ne n
        (symm h)).symm
  | add p q hp hq => simp [hp, hq]

variable {P}

private theorem toWeightPolynomial_ne_zero (hP : P ≠ 0) : toWeightPolynomial w P ≠ 0 := fun h ↦
  hP <| by rw [← eval_one_toWeightPolynomial w P, h, Polynomial.eval_zero]

variable {w}

/-- A polynomial is weighted homogeneous of weight `n` exactly when its image is the monomial of
degree `n`. -/
private theorem toWeightPolynomial_eq_monomial_iff :
    toWeightPolynomial w P = Polynomial.monomial n P ↔ IsWeightedHomogeneous w P n := by
  refine ⟨fun h ↦ ?_, fun hP ↦ Polynomial.ext fun k ↦ ?_⟩
  · have hn : weightedHomogeneousComponent w n P = P := by
      simpa [coeff_toWeightPolynomial] using congrArg (Polynomial.coeff · n) h
    exact hn ▸ weightedHomogeneousComponent_isWeightedHomogeneous ..
  · rw [coeff_toWeightPolynomial, Polynomial.coeff_monomial]
    split_ifs with hk
    · exact hk ▸ hP.weightedHomogeneousComponent_same
    · exact hP.weightedHomogeneousComponent_ne k (symm hk)

open Polynomial

/-- If the degree and the trailing degree of the auxiliary polynomial agree then `P` is weighted
homogeneous, of that common weight. -/
private theorem isWeightedHomogeneous_natDegree
    (h : (toWeightPolynomial w P).natTrailingDegree = (toWeightPolynomial w P).natDegree) :
    IsWeightedHomogeneous w P (toWeightPolynomial w P).natDegree := by
  have hcard : (toWeightPolynomial w P).support.card ≤ 1 := Finset.card_le_one.2 fun a ha b hb ↦ by
    grind [natTrailingDegree_le_of_mem_supp b hb, le_natDegree_of_mem_supp b hb,
      natTrailingDegree_le_of_mem_supp a ha, le_natDegree_of_mem_supp a ha]
  rw [← toWeightPolynomial_eq_monomial_iff]
  convert (monomial_natDegree_leadingCoeff_eq_self hcard).symm
  simpa [eval_one_toWeightPolynomial] using (congrArg (Polynomial.eval 1)
    (monomial_natDegree_leadingCoeff_eq_self hcard)).symm

namespace IsWeightedHomogeneous

variable [IsDomain R] {Q : MvPolynomial σ R}

/-- If a product of two nonzero multivariate polynomials over a domain is weighted homogeneous,
then both factors are weighted homogeneous, and their weights add to the weight of the product. -/
theorem mul_factors (hPQ : IsWeightedHomogeneous w (P * Q) n) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ m k, IsWeightedHomogeneous w P m ∧ IsWeightedHomogeneous w Q k ∧ m + k = n := by
  classical
  have hTP := toWeightPolynomial_ne_zero w hP
  have hTQ := toWeightPolynomial_ne_zero w hQ
  have hprod : toWeightPolynomial w P * toWeightPolynomial w Q = Polynomial.monomial n (P * Q) := by
    rw [← map_mul, toWeightPolynomial_eq_monomial_iff.2 hPQ]
  have hdegree : (toWeightPolynomial w P).natDegree + (toWeightPolynomial w Q).natDegree = n := by
    simp [← natDegree_mul hTP hTQ, hprod, natDegree_monomial, mul_ne_zero hP hQ]
  have htrailing : (toWeightPolynomial w P).natTrailingDegree +
      (toWeightPolynomial w Q).natTrailingDegree = n := by
    rw [← natTrailingDegree_mul hTP hTQ, hprod, natTrailingDegree_monomial (mul_ne_zero hP hQ)]
  exact ⟨_, _, isWeightedHomogeneous_natDegree (by grind [natTrailingDegree_le_natDegree]),
    isWeightedHomogeneous_natDegree (by grind [natTrailingDegree_le_natDegree]), hdegree⟩

/-- Every irreducible factor of a nonzero weighted homogeneous multivariate polynomial over a
domain is weighted homogeneous. -/
theorem irreducible_factor (hP : IsWeightedHomogeneous w P n) (hP0 : P ≠ 0) (hQ : Irreducible Q)
    (hQP : Q ∣ P) : ∃ m, IsWeightedHomogeneous w Q m := by
  obtain ⟨S, rfl⟩ := hQP
  obtain ⟨m, _, hQhom, _, _⟩ := hP.mul_factors hQ.ne_zero (right_ne_zero_of_mul hP0)
  exact ⟨m, hQhom⟩

end IsWeightedHomogeneous

end MvPolynomial
