/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Values of Bernoulli numbers

Explicit values of `bernoulli'` and `bernoulli` beyond the ones computed in mathlib.
-/

@[expose] public section

open Finset

variable {k : ℕ}

theorem bernoulli_ne_zero_of_even (hk : 3 ≤ k) (hk2 : Even k) : bernoulli k ≠ 0 :=
    fun h ↦ by
  rcases hk2 with ⟨m, rfl⟩
  refine riemannZeta_ne_zero_of_one_lt_re (s := 2 * m) (by norm_cast; omega) ?_
  rw [← two_mul] at h
  simpa [h] using riemannZeta_two_mul_nat (k := m) (by omega)

-- should go to Mathlib.NumberTheory.Bernoulli
@[simp]
theorem bernoulli'_five : bernoulli' 5 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by decide)

-- should go to Mathlib.NumberTheory.Bernoulli
@[simp]
theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have h₂ : Nat.choose 6 2 = 15 := by decide
  have h₃ : Nat.choose 6 3 = 20 := by decide
  have h₄ : Nat.choose 6 4 = 15 := by decide
  rw [bernoulli'_def]
  norm_num [sum_range_succ, sum_range_zero, h₂, h₃, h₄]

-- should go to Mathlib.NumberTheory.Bernoulli
@[simp]
theorem bernoulli_four : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

-- should go to Mathlib.NumberTheory.Bernoulli
@[simp]
theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]
