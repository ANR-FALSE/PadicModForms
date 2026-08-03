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

@[expose] public section

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

end PowerSeries
