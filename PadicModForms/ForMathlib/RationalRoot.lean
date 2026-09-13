/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The integral root theorem in divisibility form

If `R` is a monic polynomial over a unique factorization domain `A` and `(u, w : A)` with `w ≠ 0`
satisfy `(R.scaleRoots w).eval u = 0`, that is, if `u / w` is a root of `R` in the fraction field,
then `w ∣ u`. This is `Polynomial.isInteger_of_is_root_of_monic` with the root written as a
fraction, which avoids mentioning the fraction field.
-/

@[expose] public section

namespace Polynomial

variable {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

-- should go to Mathlib.RingTheory.Polynomial.RationalRoot
/-- **Integral root theorem**, divisibility form: if `u / w` is a root of a monic polynomial `R`
over a unique factorization domain, then `w ∣ u`. -/
theorem Monic.dvd_of_eval_scaleRoots_eq_zero {R : A[X]} (hR : R.Monic) {u w : A} (hw : w ≠ 0)
    (h : (R.scaleRoots w).eval u = 0) : w ∣ u := by
  have hw' : algebraMap A (FractionRing A) w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A _)).2 hw
  have hroot : aeval (algebraMap A (FractionRing A) u / algebraMap A (FractionRing A) w) R = 0 := by
    have := scaleRoots_eval₂_mul (p := R) (algebraMap A (FractionRing A))
      (algebraMap A (FractionRing A) u / algebraMap A (FractionRing A) w) w
    rw [mul_div_cancel₀ _ hw', eval₂_at_apply, h, map_zero] at this
    rw [aeval_def]
    exact (mul_eq_zero.1 this.symm).resolve_left (pow_ne_zero _ hw')
  obtain ⟨v, hv⟩ := isInteger_of_is_root_of_monic hR hroot
  refine ⟨v, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, hv, mul_div_cancel₀ _ hw']

end Polynomial
