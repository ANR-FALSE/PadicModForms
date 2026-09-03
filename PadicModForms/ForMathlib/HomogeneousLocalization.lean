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

* `DirectSum.mem_of_mul_mem_of_right_mem`: in a graded domain, a factor of a homogeneous element
  whose cofactor is a nonzero homogeneous element is itself homogeneous.
* `HomogeneousLocalization.Away.isDomain`: `Away 𝒜 f` is a domain when `A` is and `f ≠ 0`.
* `HomogeneousLocalization.Away.exists_val_eq_of_mul_val_eq`: an element of `A[1/f]` that is a
  quotient of two degree-zero elements has degree zero.
* `HomogeneousLocalization.Away.isIntegrallyClosed`: `Away 𝒜 f` is integrally closed when `A` is.
-/

@[expose] public section

section

variable {ι A σ : Type*} [AddRightCancelMonoid ι] [DecidableEq ι]
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

-- should go to Mathlib.RingTheory.GradedAlgebra.Basic
/-- In a graded domain, if `a * b` is homogeneous of degree `i + j` and `b ≠ 0` is homogeneous of
degree `j`, then `a` is homogeneous of degree `i`: the degree-`(i + j)` component of `a * b` is
`aᵢ * b`, so `(a - aᵢ) * b = 0`. -/
theorem DirectSum.mem_of_mul_mem_of_right_mem [IsDomain A] {i j : ι} {a b : A} (hb : b ∈ 𝒜 j)
    (hb0 : b ≠ 0) (h : a * b ∈ 𝒜 (i + j)) : a ∈ 𝒜 i := by
  have key : (decompose 𝒜 a i : A) * b = a * b := by
    rw [← coe_decompose_mul_add_of_right_mem 𝒜 hb, decompose_of_mem_same 𝒜 h]
  have : (a - decompose 𝒜 a i) * b = 0 := by rw [sub_mul, key, sub_self]
  obtain h0 | h0 := mul_eq_zero.mp this
  · exact sub_eq_zero.mp h0 ▸ SetLike.coe_mem _
  · exact absurd h0 hb0

end

namespace HomogeneousLocalization

variable {ι A σ : Type*} [AddCancelCommMonoid ι] [DecidableEq ι]
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜] {f : A}

-- should go to Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
/-- The degree-zero part of the localization of a domain away from `f ≠ 0` is a domain: `val` is
injective into `Localization.Away f`, which is a domain because `0` is not a power of `f`. -/
theorem Away.isDomain [IsDomain A] (hf : f ≠ 0) : IsDomain (Away 𝒜 f) :=
  haveI : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain (Localization.Away f) hf
  Function.Injective.isDomain (algebraMap (Away 𝒜 f) (Localization.Away f)) (val_injective _)

variable {𝒜}

-- should go to Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
/-- An element `x` of `Localization.Away f` satisfying `x * w.val = u.val` with `u` and `w` of
degree zero and `w ≠ 0` is itself of degree zero. Writing `x = F / f ^ N`, clearing denominators
gives an equation in `A` whose right-hand side is homogeneous, and comparing homogeneous
components shows that `F` may be taken homogeneous of degree `N • d`. -/
theorem Away.exists_val_eq_of_mul_val_eq [IsDomain A] {d : ι} (hd : f ∈ 𝒜 d) (hf : f ≠ 0)
    {x : Localization.Away f} {u w : Away 𝒜 f} (hw : w ≠ 0) (h : x * w.val = u.val) :
    ∃ y : Away 𝒜 f, y.val = x := by
  obtain ⟨F, ⟨_, N, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hd u
  obtain ⟨m, b, hb, rfl⟩ := Away.mk_surjective 𝒜 hd w
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hw (by ext; simp [Localization.mk_zero])
  have key : F * (b * f ^ n) = a * f ^ (N + m) := by
    apply IsLocalization.injective (Localization.Away f)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
    simp only [Away.val_mk, Localization.mk_eq_mk', ← IsLocalization.mk'_mul,
      IsLocalization.mk'_eq_iff_eq, Submonoid.coe_mul] at h
    convert h using 2 <;> ring
  have hF : F ∈ 𝒜 (N • d) := by
    refine DirectSum.mem_of_mul_mem_of_right_mem 𝒜 (j := (m + n) • d)
      (add_smul m n d ▸ SetLike.mul_mem_graded hb (SetLike.pow_mem_graded n hd))
      (mul_ne_zero hb0 (pow_ne_zero _ hf)) ?_
    rw [key, show N • d + (m + n) • d = n • d + (N + m) • d by simp only [add_smul]; abel]
    exact SetLike.mul_mem_graded ha (SetLike.pow_mem_graded _ hd)
  exact ⟨Away.mk 𝒜 hd N F hF, by simp [Localization.mk_eq_mk']⟩

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
