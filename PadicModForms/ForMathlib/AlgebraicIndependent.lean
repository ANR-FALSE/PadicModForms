/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Linear independence and descent of coefficients

This file proves that the monomials in an algebraically independent family are linearly
independent. It also proves that coefficients of a finite linearly independent family descend
along an injective homomorphism from a division ring to a semiring, provided that extension of
scalars preserves linear independence, and specializes this result to power series over fields.
-/

@[expose] public section

variable {ι : Type u}

open Function MvPolynomial LinearMap Set Fintype

open scoped PowerSeries

section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {x : ι → A}

/-- The monomials in an algebraically independent family are linearly independent. -/
theorem AlgebraicIndependent.linearIndependent_monomials (hx : AlgebraicIndependent R x) :
    LinearIndependent R (fun d : ι →₀ ℕ ↦ d.prod fun i n ↦ x i ^ n) := by
  have hli : LinearIndependent R (fun d ↦ aeval x (monomial d 1 : MvPolynomial ι R)) :=
    (basisMonomials ι R).linearIndependent.map' (aeval x).toLinearMap (ker_eq_bot_of_injective hx)
  simpa [aeval_monomial] using hli

end

namespace PowerSeries

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {κ : Type*}

/-- A linearly independent family of power series remains linearly independent after extending
the coefficient field. -/
theorem linearIndependent_map (v : κ → K⟦X⟧) (hv : LinearIndependent K v) :
    LinearIndependent L (fun i ↦ (v i).map (algebraMap K L)) := by
  let b := Module.Basis.ofVectorSpace K L
  have H z r j : (b.repr (z * algebraMap K L r)) j = (b.repr z) j * r := by
    rw [← Module.Basis.coord_apply, mul_comm, ← Algebra.smul_def, map_smul]
    simp [Module.Basis.coord_apply, mul_comm]
  refine linearIndependent_iff'.2 (fun s g hg i hi ↦ b.repr.injective (Finsupp.ext fun j ↦ ?_))
  have hrel : ∑ k ∈ s, (b.repr (g k)) j • v k = 0 := ext fun n ↦ by
    simpa [Algebra.smul_def, Module.Basis.coord_apply, H, mul_comm] using
      congrArg (b.coord j) (congrArg (PowerSeries.coeff n) hg)
  simpa [Module.Basis.coord_apply] using linearIndependent_iff'.mp hv s _ hrel i hi

end PowerSeries
