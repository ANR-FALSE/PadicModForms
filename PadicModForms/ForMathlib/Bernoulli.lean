/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.Bernoulli
public import PadicModForms.ForMathlib.IntLocalization
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

/-- If `k` is positive and even, and `p - 1 ∣ k`, then the denominator of `Bₖ⁻¹` is
not divisible by `p`. -/
theorem not_dvd_den_inv_bernoulli {p : ℕ} (hk : 0 < k) (hk2 : Even k) (hp : p.Prime)
    (hpk : p - 1 ∣ k) : ¬ p ∣ (bernoulli k)⁻¹.den := by
  rcases hk2 with ⟨m, rfl⟩
  rw [← two_mul] at hk hpk ⊢
  by_cases hB0 : bernoulli (2 * m) = 0
  · simp [hB0, hp.ne_one]
  rw [Rat.den_inv_of_ne_zero hB0]
  intro hpnum
  have hBcop : (bernoulli (2 * m)).den.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr fun hpden ↦
      (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpnum hpden)
        (bernoulli (2 * m)).reduced).symm
  let S := (range (2 * m + 2)).filter fun q ↦ q.Prime ∧ (q - 1) ∣ 2 * m
  have hpS : p ∈ S := by
    simp only [S, mem_filter, mem_range]
    refine ⟨?_, hp, hpk⟩
    have hp_le : p - 1 ≤ 2 * m := Nat.le_of_dvd (by omega) hpk
    omega
  have hrest : (∑ q ∈ S.erase p, (1 : ℚ) / q).den.Coprime p := by
    refine Nat.Coprime.of_dvd_left (Rat.den_sum_dvd_prod_den _ _) ?_
    refine Nat.Coprime.prod_left fun q hq ↦ ?_
    have hq_prime : q.Prime := (mem_filter.mp (mem_of_mem_erase hq)).2.1
    rw [show ((1 : ℚ) / q).den = q by simp [hq_prime.ne_zero]]
    exact (Nat.coprime_primes hq_prime hp).mpr (mem_erase.mp hq).1
  have hVS := Bernoulli.vonStaudt_clausen m
  change bernoulli (2 * m) + ∑ q ∈ S, (1 : ℚ) / q ∈ Set.range Int.cast at hVS
  obtain ⟨z, hz⟩ := hVS
  have hz_cop : ((z : ℚ).den).Coprime p := by simp
  have hzB_cop : ((z : ℚ) - bernoulli (2 * m)).den.Coprime p :=
    Nat.Coprime.of_dvd_left (Rat.sub_den_dvd _ _) (hz_cop.mul_left hBcop)
  have hpterm_cop : ((1 : ℚ) / p).den.Coprime p := by
    rw [← add_sum_erase _ _ hpS] at hz
    rw [show (1 : ℚ) / p = (z : ℚ) - bernoulli (2 * m) -
        ∑ q ∈ S.erase p, (1 : ℚ) / q by linarith [hz]]
    exact Nat.Coprime.of_dvd_left (Rat.sub_den_dvd _ _) (hzB_cop.mul_left hrest)
  exact (hp.coprime_iff_not_dvd.mp hpterm_cop.symm) (by simp [hp.ne_zero])

/-- If `p` is prime, `k ≥ 3` is even, and `p - 1 ∣ k`, then `Bₖ⁻¹` is `p`-integral. -/
theorem inv_bernoulli_mem_pLocalInt {p : ℕ} [hp : Fact p.Prime] (hk : 3 ≤ k) (hk2 : Even k)
    (hpk : p - 1 ∣ k) : (bernoulli k)⁻¹ ∈ pLocalInt p :=
  (mem_pLocalInt_iff p).2 <| not_dvd_den_inv_bernoulli (by omega) hk2 hp.out hpk

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
