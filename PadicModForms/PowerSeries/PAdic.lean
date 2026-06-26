/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

import PadicModForms.PowerSeries.Topology
public import Mathlib

/-!
# Valuation on p-adic power series

-/

@[expose] public section

variable {p : ℕ} [Fact p.Prime]

open scoped PowerSeriesUniformConvergence

open PowerSeries Padic

namespace PowerSeries.Padic

/-- The additive `p`-adic valuation of the `n`-th coefficient of a power series, viewed in the
extended integers `[-∞, ∞]`. -/
noncomputable abbrev coeffPadicValuation (n : ℕ) (f : ℚ_[p]⟦X⟧) : EInt :=
  Padic.addValuation (coeff n f)

/-- The valuation on `ℚ_[p]⟦X⟧`: for `f = ∑ aₙ Xⁿ` we set `v(f) = infₙ v_p(aₙ)`. -/
noncomputable def v (f : ℚ_[p]⟦X⟧) : EInt :=
  ⨅ n, coeffPadicValuation n f

theorem v_def (f : ℚ_[p]⟦X⟧) : v f = ⨅ n, (addValuation (coeff n f) : EInt) :=
  rfl

theorem v_le_coeffPadicValuation (f : ℚ_[p]⟦X⟧) (n : ℕ) : v f ≤ coeffPadicValuation n f :=
  iInf_le ..

theorem le_v_iff {m : EInt} {f : ℚ_[p]⟦X⟧} : m ≤ v f ↔ ∀ n : ℕ, m ≤ coeffPadicValuation n f := by
  rw [v, le_iInf_iff]

end PowerSeries.Padic
