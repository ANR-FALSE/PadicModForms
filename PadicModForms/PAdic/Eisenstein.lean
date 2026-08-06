/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.Bernoulli
public import PadicModForms.PAdic.Basic
public import PadicModForms.Rational.Eisenstein

/-!
# p-adic Eisenstein series

This file defines the Eisenstein series `E₂`, `E₄` and `E₆` as power series over `ℚ_[p]`, and
proves their basic coefficient and modularity results. Serre writes these `P`, `Q` and `R`.
-/

@[expose] public noncomputable section

open UpperHalfPlane PowerSeries ArithmeticFunction sigma ModularForm

variable {p : ℕ} [Fact p.Prime]

namespace EisensteinSeries

/-! ### The series `E₂PAdic`, `E₄PAdic` and `E₆PAdic` -/

/-- `E₂`, regarded as a power series over `ℚ_[p]`. This is Serre's `P`. -/
abbrev E₂PAdic : ℚ_[p]⟦X⟧ := E₂Rat.map (algebraMap ℚ ℚ_[p])

/-- `E₄`, regarded as a power series over `ℚ_[p]`. This is Serre's `Q`. -/
abbrev E₄PAdic : ℚ_[p]⟦X⟧ := (rationalQExpansion E₄Rat).map (algebraMap ℚ ℚ_[p])

/-- `E₆`, regarded as a power series over `ℚ_[p]`. This is Serre's `R`. -/
abbrev E₆PAdic : ℚ_[p]⟦X⟧ := (rationalQExpansion E₆Rat).map (algebraMap ℚ ℚ_[p])

@[simp]
theorem coeff_E₂PAdic (n : ℕ) :
    coeff n E₂PAdic = if n = 0 then 1 else (-24 : ℚ_[p]) * σ 1 n := by
  by_cases hn : n = 0 <;> simp [hn]

@[simp]
theorem coeff_E₄PAdic (n : ℕ) :
    coeff n E₄PAdic = if n = 0 then 1 else (240 : ℚ_[p]) * σ 3 n := by
  by_cases hn : n = 0 <;> simp [hn, coeff_E₄Rat]

@[simp]
theorem coeff_E₆PAdic (n : ℕ) :
    coeff n E₆PAdic = if n = 0 then 1 else -(504 : ℚ_[p]) * σ 5 n := by
  by_cases hn : n = 0 <;> simp [hn, coeff_E₆Rat]

variable {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (p)

/-! ### `p`-adic modularity -/

include hk hk2 in
/-- A rational Eisenstein series becomes a p-adic modular form after extending scalars. -/
theorem ERat_map_isPAdicModularForm :
    isPAdicModularForm p ((rationalQExpansion (ERat hk hk2)).map (algebraMap ℚ ℚ_[p])) :=
  rationalQExpansion_isPAdicModularForm (ERat hk hk2)

include hk hk2 in
/-- A rational `G`-series becomes a p-adic modular form after extending scalars. -/
theorem GRat_map_isPAdicModularForm :
    isPAdicModularForm p ((rationalQExpansion (GRat hk hk2)).map (algebraMap ℚ ℚ_[p])) :=
  rationalQExpansion_isPAdicModularForm (GRat hk hk2)

theorem E₄PAdic_isPAdicModularForm : isPAdicModularForm p E₄PAdic := by
  simpa [E₄PAdic] using ERat_map_isPAdicModularForm p (k := 4) (by norm_num) ⟨2, rfl⟩

theorem E₆PAdic_isPAdicModularForm : isPAdicModularForm p E₆PAdic := by
  simpa [E₆PAdic] using ERat_map_isPAdicModularForm p (k := 6) (by norm_num) ⟨3, rfl⟩

end EisensteinSeries
