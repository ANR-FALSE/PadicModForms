/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Reduction of Eisenstein series

This file records the q-expansion coefficients of normalized Eisenstein series.
-/

@[expose] public section

open UpperHalfPlane PowerSeries ArithmeticFunction sigma

namespace EisensteinSeries

variable {k : ℕ} (hk : 3 ≤ k)

theorem qExpansion_coeff (n : ℕ) (hk2 : Even k) : coeff n (qExpansion 1 (ModularForm.E hk)) =
    if n = 0 then 1 else -(2 * k / (bernoulli k) : ℂ) * (σ (k - 1)) n := by
  simpa using EisensteinSeries.E_qExpansion_coeff hk hk2 n

end EisensteinSeries
