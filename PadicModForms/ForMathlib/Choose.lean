/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Casts of binomial coefficients in weight three

## Main results

* `Nat.cast_descFactorial_three`: `n.descFactorial 3 = n (n - 1) (n - 2)`.
* `Nat.cast_choose_three`: `n.choose 3 = n (n - 1) (n - 2) / 6`.
-/

@[expose] public section

namespace Nat

-- should go to Mathlib.Data.Nat.Factorial.Cast, next to `Nat.cast_descFactorial_two`
/-- Convenience lemma. The `a - 1` and `a - 2` are not using truncated subtraction, as opposed to
the definition of `Nat.descFactorial` as a natural. -/
theorem cast_descFactorial_three {S : Type*} [CommRing S] (a : ℕ) :
    (a.descFactorial 3 : S) = a * (a - 1) * (a - 2) := by
  match a with
  | 0 => simp
  | 1 => simp
  | (n + 2) =>
    rw [show (n + 2).descFactorial 3 = n * ((n + 1) * (n + 2)) by simp [descFactorial]]
    grind

-- should go to Mathlib.Data.Nat.Choose.Cast, next to `Nat.cast_choose_two`
/-- The binomial coefficient `a.choose 3` in a field of characteristic zero. -/
theorem cast_choose_three {K : Type*} [Field K] [CharZero K] (a : ℕ) :
    (a.choose 3 : K) = a * (a - 1) * (a - 2) / 6 := by
  rw [eq_div_iff_mul_eq (by norm_num : (6 : K) ≠ 0), ← cast_descFactorial_three,
    descFactorial_eq_factorial_mul_choose, cast_mul, show 3! = 6 by decide]
  ring

end Nat
