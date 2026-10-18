/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic

/-!
# Primes dividing products of two prime powers

A prime `p` divides `m ^ a * n ^ b` only if it divides `m` or `n`. In particular a prime `p ≥ 5`
divides no number of the form `2 ^ a * 3 ^ b`. This is the only arithmetic input behind the
invertibility of `12`, `24` and `1728` modulo `p` and in the localization of `ℤ` at `p`.
-/

@[expose] public section

namespace Nat.Prime

variable {p m n : ℕ}

-- should go to Mathlib.Data.Nat.Prime.Basic
/-- A prime dividing neither `m` nor `n` divides no product `m ^ a * n ^ b`. -/
theorem not_dvd_pow_mul_pow (hp : p.Prime) (hm : ¬p ∣ m) (hn : ¬p ∣ n) (a b : ℕ) :
    ¬p ∣ m ^ a * n ^ b := by
  rw [hp.dvd_mul]
  rintro (h | h) <;> grind [hp.dvd_of_dvd_pow]

-- should go to Mathlib.Data.Nat.Prime.Basic
/-- A prime `p ≥ 5` divides no number of the form `2 ^ a * 3 ^ b`. -/
theorem not_dvd_two_pow_mul_three_pow (hp : p.Prime) (h5 : 5 ≤ p) (a b : ℕ) :
    ¬p ∣ 2 ^ a * 3 ^ b :=
  hp.not_dvd_pow_mul_pow (fun h ↦ by grind [Nat.le_of_dvd (by decide) h])
    (fun h ↦ by grind [Nat.le_of_dvd (by decide) h]) a b

end Nat.Prime
