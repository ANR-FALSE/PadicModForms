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

open Finset Ideal

variable {k : ℕ}

theorem bernoulli_ne_zero_of_even (hk : 3 ≤ k) (hk2 : Even k) : bernoulli k ≠ 0 :=
    fun h ↦ by
  rcases hk2 with ⟨m, rfl⟩
  refine riemannZeta_ne_zero_of_one_lt_re (s := 2 * m) (by norm_cast; lia) ?_
  rw [← two_mul] at h
  simpa [h] using riemannZeta_two_mul_nat (k := m) (by lia)

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
    have hp_le : p - 1 ≤ 2 * m := Nat.le_of_dvd (by lia) hpk
    lia
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

/-- If `k` is positive and even, and `p - 1 ∣ k`, then `p` divides the denominator of
`Bₖ`. -/
theorem dvd_den_bernoulli {p : ℕ} (hk : 0 < k) (hk2 : Even k) (hp : p.Prime)
    (hpk : p - 1 ∣ k) : p ∣ (bernoulli k).den := by
  rcases hk2 with ⟨m, rfl⟩
  rw [← two_mul] at hk hpk ⊢
  by_contra hpden
  have hBcop : (bernoulli (2 * m)).den.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr hpden).symm
  let S := (range (2 * m + 2)).filter fun q ↦ q.Prime ∧ (q - 1) ∣ 2 * m
  have hpS : p ∈ S := by
    simp only [S, mem_filter, mem_range]
    refine ⟨?_, hp, hpk⟩
    have hp_le : p - 1 ≤ 2 * m := Nat.le_of_dvd (by lia) hpk
    lia
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
  (mem_pLocalInt_iff p).2 <| not_dvd_den_inv_bernoulli (by lia) hk2 hp.out hpk

/-- If `p - 1 ∣ k`, then `p` divides `Bₖ⁻¹` in the localization of `ℤ` at `p`. -/
theorem p_dvd_inv_bernoulli {p : ℕ} [Fact p.Prime] (hk : 3 ≤ k) (hk2 : Even k)
    (hpk : p - 1 ∣ k) : (p : pLocalInt p) ∣ ⟨_, inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩ := by
  let q := (bernoulli k)⁻¹
  have hpnum : (p : ℤ) ∣ q.num := by
    rw [Rat.num_inv]
    exact dvd_mul_of_dvd_right (by exact_mod_cast (dvd_den_bernoulli (by lia) hk2 Fact.out hpk)) _
  have hqden : ¬ p ∣ q.den := by
    simpa [q] using not_dvd_den_inv_bernoulli (by lia) hk2 Fact.out hpk
  let qden : (span {(p : ℤ)}).primeCompl := ⟨q.den, fun h ↦ hqden <| by
    exact_mod_cast mem_span_singleton.mp h⟩
  have hq : (⟨q, by simpa [q] using inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩) =
      IsLocalization.mk' (pLocalInt p) q.num qden := by
    simpa [IsLocalization.eq_mk'_iff_mul_eq] using Subtype.ext (Rat.mul_den_eq_num q)
  obtain ⟨z, hz⟩ := hpnum
  refine ⟨IsLocalization.mk' (pLocalInt p) z qden, ?_⟩
  rw [show (⟨_, inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩ : pLocalInt p) =
    ⟨q, by simpa [q] using inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩ by rfl, hq, hz,
    ← IsLocalization.mul_mk'_eq_mk'_of_mul]
  norm_num

/-- If `p` is prime, `k ≥ 3` is even, and `p - 1 ∣ k`, then `Bₖ⁻¹` reduces to zero
modulo `p`. -/
theorem toZMod_inv_bernoulli_eq_zero {p : ℕ} [Fact p.Prime] (hk : 3 ≤ k) (hk2 : Even k)
    (hpk : p - 1 ∣ k) :
    pLocalInt.toZMod ⟨(bernoulli k)⁻¹, inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩ = 0 := by
  let q := (bernoulli k)⁻¹
  have hpnum : (p : ℤ) ∣ q.num := by
    rw [Rat.num_inv]
    exact dvd_mul_of_dvd_right (by exact_mod_cast (dvd_den_bernoulli (by lia) hk2 Fact.out hpk)) _
  have hqden : ¬ p ∣ q.den := by
    simpa [q] using not_dvd_den_inv_bernoulli (by lia) hk2 Fact.out hpk
  let qden : (span {(p : ℤ)}).primeCompl := ⟨q.den, fun h ↦ hqden <| by
    exact_mod_cast mem_span_singleton.mp h⟩
  have hq : (⟨q, by simpa [q] using inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩) =
      IsLocalization.mk' (pLocalInt p) q.num qden := by
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    exact Subtype.ext (Rat.mul_den_eq_num q)
  rw [show (⟨(bernoulli k)⁻¹, inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩ : pLocalInt p) =
      ⟨q, by simpa [q] using inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩ by rfl, hq]
  change IsLocalization.lift _ (IsLocalization.mk' (pLocalInt p) q.num qden) = 0
  rw [IsLocalization.lift_mk'_spec]
  simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd q.num p).2 hpnum

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
