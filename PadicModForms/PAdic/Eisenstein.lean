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

This file defines Serre's series `P`, `Q`, and `R` as power series over `ℚ_[p]` and proves their
basic coefficient and modularity results.
-/

@[expose] public noncomputable section

open UpperHalfPlane PowerSeries ArithmeticFunction sigma ModularForm

variable {p : ℕ} [Fact p.Prime]

namespace EisensteinSeries

/-! ### The series `P`, `Q` and `R` -/

/-- `P = E₂`, regarded as a power series over `ℚ_[p]`. -/
abbrev P : ℚ_[p]⟦X⟧ := E₂Rat.map (algebraMap ℚ ℚ_[p])

/-- `Q = E₄`, regarded as a power series over `ℚ_[p]`. -/
abbrev Q : ℚ_[p]⟦X⟧ := (rationalQExpansion E₄Rat).map (algebraMap ℚ ℚ_[p])

/-- `R = E₆`, regarded as a power series over `ℚ_[p]`. -/
abbrev R : ℚ_[p]⟦X⟧ := (rationalQExpansion E₆Rat).map (algebraMap ℚ ℚ_[p])

@[simp] theorem coeff_P (n : ℕ) : coeff n P = if n = 0 then 1 else (-24 : ℚ_[p]) * σ 1 n := by
  by_cases hn : n = 0 <;> simp [hn]

@[simp] theorem coeff_Q (n : ℕ) : coeff n Q = if n = 0 then 1 else (240 : ℚ_[p]) * σ 3 n := by
  by_cases hn : n = 0 <;> simp [hn, coeff_E₄Rat]

@[simp] theorem coeff_R (n : ℕ) : coeff n R = if n = 0 then 1 else -(504 : ℚ_[p]) * σ 5 n := by
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

theorem Q_isPAdicModularForm : isPAdicModularForm p Q := by
  simpa [Q] using ERat_map_isPAdicModularForm p (k := 4) (by norm_num) ⟨2, rfl⟩

theorem R_isPAdicModularForm : isPAdicModularForm p R := by
  simpa [R] using ERat_map_isPAdicModularForm p (k := 6) (by norm_num) ⟨3, rfl⟩

end EisensteinSeries
