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

public section

namespace Finsupp

-- should go to Mathlib.Data.Finsupp.Weight

variable {u v : ℕ}

theorem weight_fin_two (w : Fin 2 → ℕ) (d : Fin 2 →₀ ℕ) : weight w d = d 0 * w 0 + d 1 * w 1 := by
  simp [weight_eq_sum, Fin.sum_univ_two, mul_comm]

private theorem eq_of_mul_add_mul_eq_aux {a b a' b' : ℕ} (hu : 0 < u) (hv : 0 < v) (hle : a ≤ a')
    (h : a * u + b * v = a' * u + b' * v) (hlt : a * u + b * v < Nat.lcm u v) :
    a = a' ∧ b = b' := by
  have hk : (a' - a) * u = (b - b') * v := by rw [Nat.sub_mul, Nat.sub_mul]; lia
  have h0 : (a' - a) * u = 0 := Nat.eq_zero_of_dvd_of_lt
    (Nat.lcm_dvd ⟨_, mul_comm _ u⟩ ⟨_, hk.trans (mul_comm _ v)⟩) (by rw [Nat.sub_mul]; lia)
  rcases Nat.mul_eq_zero.1 h0 with ha | rfl
  · have ha' : a' = a := by lia
    subst ha'
    exact ⟨rfl, Nat.mul_right_cancel hv (by lia)⟩
  · lia

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
