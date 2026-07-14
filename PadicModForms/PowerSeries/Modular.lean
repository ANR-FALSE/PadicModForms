/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.Defs.Modular
public import PadicModForms.PowerSeries.PAdic

/-!
# Modular power series

This file proves boundedness results for the coefficients of rational modular power series.
-/

@[expose] public section

namespace PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- The `p`-adic valuations of the coefficients of a rational modular form are bounded below. -/
theorem isModularForm_v_ne_bot {k : ℤ} {f : ℚ⟦X⟧} (hf : f.isModularForm k) :
    Padic.v (f.map (algebraMap ℚ ℚ_[p])) ≠ ⊥ := by
  sorry

end PowerSeries
