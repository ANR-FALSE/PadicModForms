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

end PowerSeries
