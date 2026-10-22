/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Additional lemmas about power series

This file contains elementary lemmas about power series that are missing from Mathlib.
-/

public section

namespace PowerSeries

variable {R : Type*} [Semiring R]

-- should go to Mathlib.RingTheory.PowerSeries.Basic
/-- A power series with vanishing constant coefficient is `X` times its shift. This is the
special case of `PowerSeries.eq_shift_mul_X_add_const` where the constant term drops out. -/
theorem eq_shift_mul_X {f : R⟦X⟧} (hf : constantCoeff f = 0) :
    f = (mk fun n ↦ coeff (n + 1) f) * X := by
  simpa [hf] using eq_shift_mul_X_add_const f

-- should go to Mathlib.RingTheory.PowerSeries.Basic
/-- A power series all of whose coefficients are divisible by `a` is `a` times a power series,
namely the one obtained by dividing each coefficient by `a`. -/
theorem exists_smul_eq_of_forall_dvd_coeff {a : R} {f : R⟦X⟧} (hf : ∀ n, a ∣ coeff n f) :
    ∃ g : R⟦X⟧, a • g = f := by
  choose c hc using hf
  exact ⟨mk c, ext fun n ↦ by simp [hc n]⟩

-- should go to Mathlib.RingTheory.PowerSeries.Basic
/-- Over a semiring without zero divisors, scalar multiplication of a power series by a nonzero
scalar is injective. -/
instance [NoZeroDivisors R] : NoZeroSMulDivisors R R⟦X⟧ where
  eq_zero_or_eq_zero_of_smul_eq_zero {a f} h := or_iff_not_imp_left.2 fun ha ↦ ext fun n ↦ by
    rw [map_zero]
    exact (mul_eq_zero.1 (by simpa using congr(coeff n $h))).resolve_left ha

-- should go to Mathlib.RingTheory.PowerSeries.Basic
/-- Two power series with the same image under a ring map whose kernel consists of multiples of
`a` differ by `a` times a power series. -/
theorem exists_smul_eq_sub_of_map_eq {A S : Type*} [Ring A] [Ring S] {φ : A →+* S} {a : A}
    (hker : ∀ x, φ x = 0 → a ∣ x) {f g : A⟦X⟧} (h : f.map φ = g.map φ) :
    ∃ k : A⟦X⟧, a • k = f - g :=
  exists_smul_eq_of_forall_dvd_coeff fun n ↦
    hker _ (by rw [← coeff_map, map_sub, h, sub_self, map_zero])

end PowerSeries
