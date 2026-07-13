/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import PadicModForms.Defs.Modular
import PadicModForms.ForMathlib.Bernoulli

/-!
# Eisenstein series

This file defines Serre's series `P`, `Q`, and `R` as power series over `Q_p`.
-/

@[expose] public section

open UpperHalfPlane PowerSeries ArithmeticFunction sigma

variable {p : ℕ} [Fact p.Prime] (n : ℕ)

namespace EisensteinSeries

/-- Serre's series `P = E_2 = 1 - 24 * sum_{n >= 1} sigma_1(n) q^n`, regarded as
a power series over `Q_p`. -/
noncomputable def P : ℚ_[p]⟦X⟧ := mk fun n ↦ if n = 0 then 1 else -24 * σ 1 n

/-- Serre's series `Q = E_4 = 1 + 240 * sum_{n >= 1} sigma_3(n) q^n`, regarded as
a power series over `Q_p`. -/
noncomputable def Q : ℚ_[p]⟦X⟧ := mk fun n ↦ if n = 0 then 1 else 240 * σ 3 n

/-- The rational `q`-expansion of Serre's series `Q = E_4`. -/
noncomputable def Q_rat : ℚ⟦X⟧ := mk fun n ↦ if n = 0 then 1 else 240 * σ 3 n

/-- Serre's series `R = E_6 = 1 - 504 * sum_{n >= 1} sigma_5(n) q^n`, regarded as
a power series over `Q_p`. -/
noncomputable def R : ℚ_[p]⟦X⟧ := mk fun n ↦ if n = 0 then 1 else -504 * σ 5 n

/-- The rational `q`-expansion of Serre's series `R = E_6`. -/
noncomputable def R_rat : ℚ⟦X⟧ := mk fun n ↦ if n = 0 then 1 else -504 * σ 5 n

@[simp] theorem coeff_P : coeff n P = if n = 0 then 1 else (-24 : ℚ_[p]) * σ 1 n :=
  coeff_mk ..

@[simp] theorem coeff_Q : coeff n Q = if n = 0 then 1 else (240 : ℚ_[p]) * σ 3 n :=
  coeff_mk ..

@[simp] theorem coeff_R : coeff n R = if n = 0 then 1 else -(504 : ℚ_[p]) * σ 5 n :=
  coeff_mk ..

@[simp] theorem coeff_Q_rat : coeff n Q_rat = if n = 0 then 1 else (240 : ℚ) * σ 3 n :=
  coeff_mk ..

@[simp] theorem coeff_R_rat : coeff n R_rat = if n = 0 then 1 else -(504 : ℚ) * σ 5 n :=
  coeff_mk ..

@[simp] theorem map_Q_rat : Q_rat.map (algebraMap ℚ ℚ_[p]) = Q := by
  ext n
  by_cases hn : n = 0 <;> simp [Q_rat, Q, hn]

@[simp] theorem map_R_rat : R_rat.map (algebraMap ℚ ℚ_[p]) = R := by
  ext n
  by_cases hn : n = 0 <;> simp [R_rat, R, hn]

theorem qExpansion_E_four_eq_Q_rat_map :
    qExpansion 1 ModularForm.E₄ = Q_rat.map (algebraMap ℚ ℂ) := by
  ext n
  rw [PowerSeries.coeff_map, EisensteinSeries.E_qExpansion_coeff (by norm_num) ⟨2, rfl⟩ n]
  by_cases hn : n = 0
  · simp [Q_rat, hn]
  · simp [Q_rat, hn, bernoulli_four]
    ring

theorem qExpansion_E_six_eq_R_rat_map :
    qExpansion 1 ModularForm.E₆ = R_rat.map (algebraMap ℚ ℂ) := by
  ext n
  rw [PowerSeries.coeff_map]
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num) ⟨3, rfl⟩ n]
  by_cases hn : n = 0
  · simp [R_rat, hn]
  · simp [R_rat, hn, bernoulli_six]
    ring

theorem Q_isPAdicModularForm : PowerSeries.isPAdicModularForm p Q := by
  rw [← map_Q_rat]
  exact powerSeries_isPAdicModularForm_of_qExpansion_eq_map p (g := Q_rat) <|
    ⟨4, ModularForm.E₄, by simpa using qExpansion_E_four_eq_Q_rat_map⟩

theorem R_isPAdicModularForm : PowerSeries.isPAdicModularForm p R := by
  rw [← map_R_rat]
  exact powerSeries_isPAdicModularForm_of_qExpansion_eq_map p (g := R_rat) <|
    ⟨6, ModularForm.E₆, by simpa using qExpansion_E_six_eq_R_rat_map⟩

end EisensteinSeries
