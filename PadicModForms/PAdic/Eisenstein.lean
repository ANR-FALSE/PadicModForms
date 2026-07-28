/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.Bernoulli
public import PadicModForms.PAdic.Basic
public import PadicModForms.Rational.Basic

/-!
# p-adic Eisenstein series

This file defines Serre's series `P`, `Q`, and `R` as power series over `ℚ_[p]` and proves their
basic coefficient and modularity results.
-/

@[expose] public noncomputable section

open UpperHalfPlane PowerSeries ArithmeticFunction sigma ModularForm

variable {p : ℕ} [Fact p.Prime]

namespace EisensteinSeries

/-- `P = E₂`, regarded as a power series over `ℚ_[p]`. -/
noncomputable def P : ℚ_[p]⟦X⟧ := (E_rat 2).map (algebraMap ℚ ℚ_[p])

/-- `Q = E₄`, regarded as a power series over `ℚ_[p]`. -/
noncomputable def Q : ℚ_[p]⟦X⟧ := (E_rat 4).map (algebraMap ℚ ℚ_[p])

/-- `R = E₆`, regarded as a power series over `ℚ_[p]`. -/
noncomputable def R : ℚ_[p]⟦X⟧ := (E_rat 6).map (algebraMap ℚ ℚ_[p])

@[simp] theorem coeff_P (n : ℕ) :
    coeff n P = if n = 0 then 1 else (-24 : ℚ_[p]) * σ 1 n := by
  by_cases hn : n = 0
  · simp [P, hn]
  · simp [P, hn, bernoulli_two]
    norm_num

@[simp] theorem coeff_Q (n : ℕ) :
    coeff n Q = if n = 0 then 1 else (240 : ℚ_[p]) * σ 3 n := by
  by_cases hn : n = 0
  · simp [Q, hn]
  · simp [Q, hn, bernoulli_four]
    ring

@[simp] theorem coeff_R (n : ℕ) :
    coeff n R = if n = 0 then 1 else -(504 : ℚ_[p]) * σ 5 n := by
  by_cases hn : n = 0
  · simp [R, hn]
  · simp [R, hn, bernoulli_six]
    norm_num

variable {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k)
variable (p)

include hk hk2 in
/-- A rational Eisenstein series becomes a p-adic modular form after extending scalars. -/
theorem E_rat_map_isPAdicModularForm :
    isPAdicModularForm p ((E_rat k).map (algebraMap ℚ ℚ_[p])) :=
  powerSeries_isPAdicModularForm_of_qExpansion_eq_map p ⟨k, E_rat_isModularForm hk hk2⟩

include hk hk2 in
/-- A rational `G`-series becomes a p-adic modular form after extending scalars. -/
theorem G_rat_map_isPAdicModularForm :
    isPAdicModularForm p ((G_rat k).map (algebraMap ℚ ℚ_[p])) :=
  powerSeries_isPAdicModularForm_of_qExpansion_eq_map p ⟨k, G_rat_isModularForm hk hk2⟩

theorem Q_isPAdicModularForm : isPAdicModularForm p Q := by
  simpa [Q] using E_rat_map_isPAdicModularForm p (k := 4) (by norm_num) ⟨2, rfl⟩

theorem R_isPAdicModularForm : isPAdicModularForm p R := by
  simpa [R] using E_rat_map_isPAdicModularForm p (k := 6) (by norm_num) ⟨3, rfl⟩

end EisensteinSeries
