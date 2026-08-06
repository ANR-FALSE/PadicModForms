/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Weights in two variables

## Main results

* `Finsupp.weight_fin_two`: the weight of `d : Fin 2 →₀ ℕ` for a weight function on `Fin 2`.
* `Finsupp.eq_of_weight_eq_of_lt_lcm`: below `Nat.lcm u v`, an exponent vector in two variables of
  weights `u` and `v` is determined by its weight. Two representations of the same weight differ
  by a nonzero common multiple of `u` and `v`, which is at least `Nat.lcm u v`.
-/

@[expose] public section

namespace Finsupp

-- should go to Mathlib.Data.Finsupp.Weight

variable {u v : ℕ}

theorem weight_fin_two (w : Fin 2 → ℕ) (d : Fin 2 →₀ ℕ) : weight w d = d 0 * w 0 + d 1 * w 1 := by
  simp [weight_eq_sum, Fin.sum_univ_two, mul_comm]

private theorem eq_of_mul_add_mul_eq_aux {a b a' b' : ℕ} (hu : 0 < u) (hv : 0 < v) (hle : a ≤ a')
    (h : a * u + b * v = a' * u + b' * v) (hlt : a * u + b * v < Nat.lcm u v) :
    a = a' ∧ b = b' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [add_mul] at h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le
    (Nat.le_of_mul_le_mul_right (show b' * v ≤ b * v by omega) hv)
  rw [add_mul] at h hlt
  have hmk : m * v = k * u := by omega
  have hmv : m * v = 0 := Nat.eq_zero_of_dvd_of_lt
    (Nat.lcm_dvd ⟨k, by rw [hmk, mul_comm]⟩ ⟨m, mul_comm m v⟩) (by omega)
  have hk : k = 0 := by rcases Nat.mul_eq_zero.1 (show k * u = 0 by omega) with h | h <;> omega
  have hm : m = 0 := by rcases Nat.mul_eq_zero.1 hmv with h | h <;> omega
  grind

/-- Below `Nat.lcm u v`, an exponent vector in two variables of weights `u` and `v` is determined
by its weight. -/
theorem eq_of_weight_eq_of_lt_lcm (hu : 0 < u) (hv : 0 < v) {n : ℕ} (hn : n < Nat.lcm u v)
    {d e : Fin 2 →₀ ℕ} (hd : weight ![u, v] d = n) (he : weight ![u, v] e = n) : d = e := by
  rw [weight_fin_two] at hd he
  have key : d 0 = e 0 ∧ d 1 = e 1 := by
    rcases le_total (d 0) (e 0) with hle | hle
    · exact eq_of_mul_add_mul_eq_aux hu hv hle (hd.trans he.symm) (by simp_all)
    · grind [eq_of_mul_add_mul_eq_aux hu hv hle (he.trans hd.symm) (by simp_all)]
  exact Finsupp.ext fun i ↦ by fin_cases i <;> grind

end Finsupp
