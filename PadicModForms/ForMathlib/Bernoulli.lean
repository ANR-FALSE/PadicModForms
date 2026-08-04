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
import PadicModForms.ForMathlib.Choose

/-!
# Values and `p`-adic properties of Bernoulli numbers

Explicit values of `bernoulli'` and `bernoulli` beyond the ones computed in mathlib, together with
the consequences of von Staudt–Clausen describing the behaviour of `Bₖ` at a prime `p`, and the
instance `k = p + 1` of Kummer's congruence.

## Main results

* `bernoulli_mem_pLocalInt`: if `p - 1 ∤ k` then `Bₖ` is `p`-integral.
* `bernoulli_add_inv_mem_pLocalInt`: if `p - 1 ∣ k` then `Bₖ + 1/p` is `p`-integral; equivalently
  `p Bₖ ≡ -1` modulo `p`.
* `inv_bernoulli_mem_pLocalInt`, `toZMod_inv_bernoulli_eq_zero`: if `p - 1 ∣ k` then `Bₖ⁻¹` is
  `p`-integral and reduces to `0` modulo `p`.
* `exists_bernoulli_p_add_one`, `toZMod_bernoulli_p_add_one_mul_twelve`: Kummer's congruence
  `B_{p+1}/(p+1) ≡ B₂/2` modulo `p`, in the form `12 B_{p+1} ≡ 1`.
* `toZMod_inv_bernoulli_p_add_one`: the form used for Eisenstein series, `B_{p+1}⁻¹ ≡ 12`.
-/

@[expose] public section

open Finset Ideal Nat

variable {k : ℕ}

/-! ### Nonvanishing and denominators -/

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
    (hp.coprime_iff_not_dvd.mpr fun hpden ↦ (not_coprime_of_dvd_of_dvd hp.one_lt hpnum hpden)
        (bernoulli (2 * m)).reduced).symm
  let S := (range (2 * m + 2)).filter fun q ↦ q.Prime ∧ (q - 1) ∣ 2 * m
  have hpS : p ∈ S := by
    simp only [S, mem_filter, mem_range]
    refine ⟨?_, hp, hpk⟩
    have hp_le : p - 1 ≤ 2 * m := le_of_dvd (by lia) hpk
    lia
  have hrest : (∑ q ∈ S.erase p, (1 : ℚ) / q).den.Coprime p := by
    refine (Coprime.prod_left fun q hq ↦ ?_).of_dvd_left (Rat.den_sum_dvd_prod_den _ _)
    have hq_prime : q.Prime := (mem_filter.mp (mem_of_mem_erase hq)).2.1
    rw [show ((1 : ℚ) / q).den = q by simp [hq_prime.ne_zero]]
    exact (coprime_primes hq_prime hp).mpr (mem_erase.mp hq).1
  have hVS := Bernoulli.vonStaudt_clausen m
  change bernoulli (2 * m) + ∑ q ∈ S, (1 : ℚ) / q ∈ Set.range Int.cast at hVS
  obtain ⟨z, hz⟩ := hVS
  have hz_cop : ((z : ℚ).den).Coprime p := by simp
  have hzB_cop : ((z : ℚ) - bernoulli (2 * m)).den.Coprime p :=
    (hz_cop.mul_left hBcop).of_dvd_left (Rat.sub_den_dvd _ _)
  have hpterm_cop : ((1 : ℚ) / p).den.Coprime p := by
    rw [← add_sum_erase _ _ hpS] at hz
    rw [show (1 : ℚ) / p = (z : ℚ) - bernoulli (2 * m) -
        ∑ q ∈ S.erase p, (1 : ℚ) / q by linarith [hz]]
    exact Coprime.of_dvd_left (Rat.sub_den_dvd _ _) (hzB_cop.mul_left hrest)
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
    have hp_le : p - 1 ≤ 2 * m := le_of_dvd (by lia) hpk
    lia
  have hrest : (∑ q ∈ S.erase p, (1 : ℚ) / q).den.Coprime p := by
    refine (Coprime.prod_left fun q hq ↦ ?_).of_dvd_left (Rat.den_sum_dvd_prod_den _ _)
    have hq_prime : q.Prime := (mem_filter.mp (mem_of_mem_erase hq)).2.1
    rw [show ((1 : ℚ) / q).den = q by simp [hq_prime.ne_zero]]
    exact (coprime_primes hq_prime hp).mpr (mem_erase.mp hq).1
  have hVS := Bernoulli.vonStaudt_clausen m
  change bernoulli (2 * m) + ∑ q ∈ S, (1 : ℚ) / q ∈ Set.range Int.cast at hVS
  obtain ⟨z, hz⟩ := hVS
  have hz_cop : ((z : ℚ).den).Coprime p := by simp
  have hzB_cop : ((z : ℚ) - bernoulli (2 * m)).den.Coprime p :=
    Coprime.of_dvd_left (Rat.sub_den_dvd _ _) (hz_cop.mul_left hBcop)
  have hpterm_cop : ((1 : ℚ) / p).den.Coprime p := by
    rw [← add_sum_erase _ _ hpS] at hz
    rw [show (1 : ℚ) / p = (z : ℚ) - bernoulli (2 * m) -
        ∑ q ∈ S.erase p, (1 : ℚ) / q by linarith [hz]]
    exact Coprime.of_dvd_left (Rat.sub_den_dvd _ _) (hzB_cop.mul_left hrest)
  exact (hp.coprime_iff_not_dvd.mp hpterm_cop.symm) (by simp [hp.ne_zero])

/-! ### Integrality of `Bₖ⁻¹` at `p` -/

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

/-! ### Small values -/

-- should go to Mathlib.NumberTheory.Bernoulli
@[simp]
theorem bernoulli'_five : bernoulli' 5 = 0 :=
  bernoulli'_eq_zero_of_odd (by decide) (by decide)

-- should go to Mathlib.NumberTheory.Bernoulli
@[simp]
theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have h₂ : choose 6 2 = 15 := by decide
  have h₃ : choose 6 3 = 20 := by decide
  have h₄ : choose 6 4 = 15 := by decide
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

/-! ### von Staudt–Clausen: `p`-integrality of `Bₖ` -/

section Kummer

variable {p : ℕ} [hp : Fact p.Prime]

/-- If `p - 1` does not divide `k`, then `Bₖ` is `p`-integral. -/
theorem bernoulli_mem_pLocalInt (hpk : ¬ (p - 1) ∣ k) : bernoulli k ∈ pLocalInt p := by
  rcases even_or_odd k with hk2 | hk2
  · obtain ⟨m, rfl⟩ := hk2
    rw [← two_mul] at hpk ⊢
    obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen m
    rw [show bernoulli (2 * m) = (z : ℚ) -
      ∑ q ∈ range (2 * m + 2) with q.Prime ∧ (q - 1) ∣ 2 * m, (1 : ℚ) / q by grind]
    refine sub_mem (intCast_mem _ _) (sum_mem fun q hq ↦ ?_)
    simp only [mem_filter, mem_range] at hq
    have hqp : q ≠ p := by rintro rfl; exact hpk hq.2.2
    rw [mem_pLocalInt_iff, show ((1 : ℚ) / q).den = q from by simp [hq.2.1.ne_zero]]
    exact fun h ↦ hqp ((prime_dvd_prime_iff_eq hp.out hq.2.1).mp h).symm
  · rcases eq_or_ne k 1 with rfl | hk1
    · rw [bernoulli_one, mem_pLocalInt_iff, show ((-1 / 2 : ℚ)).den = 2 from by norm_num]
      exact fun h ↦ hpk (by simp [(prime_dvd_prime_iff_eq hp.out prime_two).mp h])
    · rw [bernoulli_eq_zero_of_odd hk2 (by rcases hk2 with ⟨j, rfl⟩; lia)]
      exact zero_mem _

/-- Von Staudt–Clausen at `p`: if `p - 1 ∣ k` with `k` positive and even, then `Bₖ + 1/p` is
`p`-integral. -/
theorem bernoulli_add_inv_mem_pLocalInt (hk : 0 < k) (hk2 : Even k) (hpk : (p - 1) ∣ k) :
    bernoulli k + (p : ℚ)⁻¹ ∈ pLocalInt p := by
  obtain ⟨m, rfl⟩ := hk2
  rw [← two_mul] at hk hpk ⊢
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen m
  have hpS : p ∈ (range (2 * m + 2)).filter (fun q ↦ q.Prime ∧ (q - 1) ∣ 2 * m) := by
    simpa using ⟨by grind [le_of_dvd hk hpk], hp.out, hpk⟩
  rw [← Finset.add_sum_erase _ _ hpS] at hz
  have hB : bernoulli (2 * m) + (p : ℚ)⁻¹ = z - ∑ q ∈ ((range (2 * m + 2)).filter
    (fun q ↦ q.Prime ∧ (q - 1) ∣ 2 * m)).erase p, (1 : ℚ) / q := by rw [hz]; ring
  rw [hB]
  refine sub_mem (intCast_mem _ _) (sum_mem fun q hq ↦ ?_)
  have hqprime : q.Prime := by simpa using (mem_filter.mp (mem_of_mem_erase hq)).2.1
  rw [mem_pLocalInt_iff, show ((1 : ℚ) / q).den = q by simp [hqprime.ne_zero]]
  exact fun h ↦ ((mem_erase.mp hq).1) ((prime_dvd_prime_iff_eq hp.out hqprime).mp h).symm

/-! ### Kummer's congruence in weight `p + 1` -/

/-- Kummer's congruence `B_{p+1}/(p+1) ≡ B₂/2` modulo `p`, in the explicit form
`12 B_{p+1} - 1 ∈ p ℤ₍ₚ₎`. -/
theorem exists_bernoulli_p_add_one (hp5 : 5 ≤ p) :
    ∃ w ∈ pLocalInt p, 12 * bernoulli (p + 1) - 1 = p * w := by
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 5 := ⟨p - 5, by lia⟩
  have hc1 : (r + 7).choose (r + 6) = r + 7 := by grind
  have hc2 : (r + 7).choose (r + 5) = (r + 7).choose 2 := by
    rw [show r + 5 = (r + 7) - 2 by lia, choose_symm (by lia)]
  have hc3 : (r + 7).choose (r + 4) = (r + 7).choose 3 := by
    rw [show r + 4 = (r + 7) - 3 by lia, choose_symm (by lia)]
  have hb5 := bernoulli_eq_zero_of_odd (hp.1.odd_of_ne_two (by lia)) (by lia)
  have hv2 : ((r + 7).choose 2) = (r + 7) * ((r : ℚ) + 6) / 2 := by grind [cast_choose_two]
  have hv3 : (((r + 7).choose 3) : ℚ) = (r + 7) * (r + 6) * (r + 5) / 6 := by
    grind [cast_choose_three]
  have key := sum_bernoulli (r + 7)
  rw [if_neg (by lia), sum_range_succ, sum_range_succ, sum_range_succ, range_eq_Ico,
    ← sum_Ico_consecutive _ (zero_le 3) (by lia : 3 ≤ r + 4), ← range_eq_Ico] at key
  simp only [sum_range_succ, sum_range_zero, choose_zero_right, choose_one_right, bernoulli_zero,
    bernoulli_one, bernoulli_two, hc1, hc2, hc3, hb5, hv2, hv3] at key
  push_cast at key
  obtain ⟨T, hTmem, hT⟩ := exists_sum_natCast_mul_eq_mul (s := Ico 3 (r + 4)) (b := bernoulli)
    (c := ((r + 7).choose ·)) (fun _ _ ↦ hp.out.dvd_choose (by grind) (by grind) (by grind))
    (fun _ _ ↦ bernoulli_mem_pLocalInt (by simpa using not_dvd_of_pos_of_lt (by grind) (by grind)))
  obtain ⟨j, hj⟩ := hp.out.odd_of_ne_two (by lia : r + 5 ≠ 2)
  obtain ⟨v, hvmem, hv⟩ : ∃ v ∈ pLocalInt _, (r + 5) * bernoulli (r + 4) + 1 = (r + 5) * v :=
      ⟨bernoulli (r + 4) + (↑(r + 5) : ℚ)⁻¹, bernoulli_add_inv_mem_pLocalInt (by lia)
        ⟨j, by lia⟩ (by simp), (by grind)⟩
  have h7 : ((↑(r + 7) : ℚ))⁻¹ ∈ pLocalInt (r + 5) := inv_natCast_mem_pLocalInt (by lia)
    fun h ↦ by grind [le_of_dvd (by lia) (dvd_sub h (dvd_refl _))]
  rw [hT] at key
  refine ⟨(↑(r + 7) : ℚ)⁻¹ * ((↑(r + 13)) - 12 * T - 2 * ↑(r + 7) * ↑(r + 6) * v), ?_, ?_⟩
  · exact mul_mem h7 (by apply_rules [sub_mem, mul_mem, natCast_mem])
  · grind [show ((r : ℚ) + 7) ≠ 0 by positivity]

/-- For `p ≥ 5`, `B_{p+1}` is `p`-integral. -/
theorem bernoulli_p_add_one_mem_pLocalInt (hp5 : 5 ≤ p) : bernoulli (p + 1) ∈ pLocalInt p := by
  obtain ⟨w, hwmem, hw⟩ := exists_bernoulli_p_add_one hp5
  suffices (12 : ℚ)⁻¹ ∈ pLocalInt p  by
    rw [show bernoulli (p + 1) = (12 : ℚ)⁻¹ * (1 + p * w) by grind]
    exact mul_mem this (add_mem (one_mem _) (mul_mem (natCast_mem _ _) hwmem))
  refine inv_natCast_mem_pLocalInt (by norm_num) fun (h : p ∣ 4 * 3) ↦ ?_
  rcases (Nat.Prime.dvd_mul hp.out).mp h with h' | h' <;>
  exact absurd (le_of_dvd (by norm_num) h') (by lia)

/-- Kummer's congruence in weight `p + 1`: `12 B_{p+1} ≡ 1` modulo `p`. -/
theorem toZMod_bernoulli_p_add_one_mul_twelve (hp5 : 5 ≤ p) :
    pLocalInt.toZMod ⟨bernoulli (p + 1), bernoulli_p_add_one_mem_pLocalInt hp5⟩ * 12 = 1 := by
  obtain ⟨w, hwmem, hw⟩ := exists_bernoulli_p_add_one hp5
  suffices (12 : pLocalInt p) * ⟨_, bernoulli_p_add_one_mem_pLocalInt hp5⟩ - 1 = p * ⟨w, hwmem⟩ by
    have h := congrArg pLocalInt.toZMod this
    simp only [map_sub, map_mul, map_ofNat, map_natCast, ZMod.natCast_self] at h
    grind
  exact Subtype.ext hw

/-- For `p ≥ 5`, `B_{p+1}⁻¹` is `p`-integral. -/
theorem inv_bernoulli_p_add_one_mem_pLocalInt (hp5 : 5 ≤ p) :
    (bernoulli (p + 1))⁻¹ ∈ pLocalInt p :=
  inv_mem_pLocalInt (bernoulli_p_add_one_mem_pLocalInt hp5) fun h ↦
    by grind [toZMod_bernoulli_p_add_one_mul_twelve hp5]

/-- Kummer's congruence in weight `p + 1`, in the form used for the Eisenstein series:
`B_{p+1}⁻¹ ≡ 12` modulo `p`. -/
theorem toZMod_inv_bernoulli_p_add_one (hp5 : 5 ≤ p) :
    pLocalInt.toZMod ⟨(bernoulli (p + 1))⁻¹, inv_bernoulli_p_add_one_mem_pLocalInt hp5⟩ = 12 := by
  obtain ⟨j, hj⟩ := hp.out.odd_of_ne_two (by lia)
  suffices bernoulli (p + 1) ≠ 0 by
    have h12 := toZMod_bernoulli_p_add_one_mul_twelve hp5
    refine mul_left_cancel₀ (a := pLocalInt.toZMod ⟨_, bernoulli_p_add_one_mem_pLocalInt hp5⟩) ?_ ?_
    · exact fun h ↦ zero_ne_one (by rwa [h, zero_mul] at h12)
    rw [← map_mul, show (⟨_, bernoulli_p_add_one_mem_pLocalInt hp5⟩ *
      ⟨_, inv_bernoulli_p_add_one_mem_pLocalInt hp5⟩ : pLocalInt p) = 1 from
        Subtype.ext (by push_cast; field_simp), map_one]
    grind
  exact bernoulli_ne_zero_of_even (by lia) ⟨(p + 1) / 2, by lia⟩


end Kummer
