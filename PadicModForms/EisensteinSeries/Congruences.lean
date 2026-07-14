/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.EisensteinSeries.Basic
import PadicModForms.ForMathlib.Bernoulli

/-!
# Congruences for Eisenstein series

This file proves congruences between normalized Eisenstein series and `1` modulo powers of `p`.
-/

@[expose] public section

open PowerSeries ArithmeticFunction sigma

variable {p k m : ℕ} [Hp : Fact p.Prime]

namespace EisensteinSeries

open ModP

/-- If `p - 1 ∣ k`, then the normalized Eisenstein series of weight `k` is congruent to `1`
modulo `p`. -/
theorem E_int_mod_p (hk : 3 ≤ k) (hk2 : Even k) (hpk : p - 1 ∣ k) :
    (E_int hk hk2 hpk).map pLocalInt.toZMod = 1 := by
  let B_i : pLocalInt p := ⟨_, inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩
  have hB_inv : pLocalInt.toZMod B_i = 0 := toZMod_inv_bernoulli_eq_zero hk hk2 hpk
  ext n
  by_cases hn : n = 0
  · simp [hn, coeff_E_int_zero hk hk2 hpk]
  have hcoeff : coeff n (E_int hk hk2 hpk) = -(2 * k) * B_i * σ (k - 1) n := by
    simpa [B_i] using coeff_E_int_of_ne_zero hk hk2 hpk hn
  simp [hn, hcoeff, map_mul, map_mul, map_neg, hB_inv]

/-- If `(p - 1) * p ^ (m - 1) ∣ k`, then `E_k` is congruent to `1` modulo `p ^ m`. -/
theorem E_int_mod_p_pow_of_dvd (hm : 1 ≤ m) (hk : 3 ≤ k) (hk2 : Even k)
  (hkm : (p - 1) * p ^ (m - 1) ∣ k) :
    (E_int hk hk2 ((dvd_mul_right _ _).trans hkm)).map (pLocalInt.toZModPow m) = 1 := by
  let hpk : p - 1 ∣ k := (dvd_mul_right _ _).trans hkm
  let B_i : pLocalInt p := ⟨_, inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩
  have hB : (p : pLocalInt p) ∣ B_i := by simpa [B_i] using p_dvd_inv_bernoulli hk hk2 hpk
  have hpnk : p ^ (m - 1) ∣ k := (dvd_mul_left _ _).trans hkm
  have hkpow : (p : pLocalInt p) ^ (m - 1) ∣ (k : pLocalInt p) := by
    obtain ⟨c, hc⟩ := hpnk
    exact ⟨(c : pLocalInt p), Subtype.ext (by norm_num [hc])⟩
  have hscalar : (p : pLocalInt p) ^ m ∣ (2 * k : pLocalInt p) * B_i := by
    obtain ⟨a, ha⟩ := hkpow
    obtain ⟨b, hb⟩ := hB
    refine ⟨2 * a * b, ?_⟩
    rw [ha, hb, ← pow_sub_one_mul (by omega : m ≠ 0) (p : pLocalInt p)]
    ring
  have hscalar_map : pLocalInt.toZModPow m ((2 * k : pLocalInt p) * B_i) = 0 :=
    pLocalInt.toZModPow_eq_zero_of_dvd hscalar
  ext n
  by_cases hn : n = 0
  · simp [hn, coeff_E_int_zero hk hk2 hpk]
  have hcoeff : coeff n (E_int hk hk2 hpk) = -(2 * k) * B_i * σ (k - 1) n := by
    simpa [B_i] using coeff_E_int_of_ne_zero hk hk2 hpk hn
  simp [hn, hcoeff, map_mul, map_neg, hscalar_map]

/-- If `2 ^ (m - 2) ∣ k`, then `E_k` is congruent to `1` modulo `2 ^ m`. -/
theorem E_int_mod_two_pow_of_dvd (hm : 2 ≤ m) (hk : 3 ≤ k) (hk2 : Even k) (hkm : 2 ^ (m - 2) ∣ k) :
    (E_int (p := 2) hk hk2 (by simp)).map (pLocalInt.toZModPow m) = 1 := by
  let hpk : 2 - 1 ∣ k := by simp
  let B_i : pLocalInt 2 := ⟨_, inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩
  have hB : (2 : pLocalInt 2) ∣ B_i := by simpa [B_i] using p_dvd_inv_bernoulli hk hk2 hpk
  have hkpow : (2 : pLocalInt 2) ^ (m - 2) ∣ (k : pLocalInt 2) := by
    obtain ⟨c, hc⟩ := hkm
    refine ⟨(c : pLocalInt 2), Subtype.ext (by norm_num [hc])⟩
  have hscalar :
      (2 : pLocalInt 2) ^ m ∣ (2 * k : pLocalInt 2) * B_i := by
    obtain ⟨a, ha⟩ := hkpow
    obtain ⟨b, hb⟩ := hB
    refine ⟨a * b, ?_⟩
    calc _ = 2 ^ (m - 2 + 2) * a * b := by grind
      _ = _ := by grind
  have hscalar_map : pLocalInt.toZModPow m ((2 * k : pLocalInt 2) * B_i) = 0 :=
    pLocalInt.toZModPow_eq_zero_of_dvd hscalar
  ext n
  by_cases hn : n = 0
  · simp [hn, coeff_E_int_zero hk hk2 hpk]
  have hcoeff : coeff n (E_int hk hk2 hpk) = -(2 * k) * B_i * σ (k - 1) n := by
    simpa [B_i] using coeff_E_int_of_ne_zero hk hk2 hpk hn
  simp [hn, hcoeff, map_mul, map_neg, hscalar_map]

/-- The normalized Eisenstein series of weight `p - 1` is congruent to `1` modulo `p`. -/
theorem E_p_sub_one_mod_p (hp : 5 ≤ p) : (E hp).map pLocalInt.toZMod = 1 := by
  exact E_int_mod_p (by lia) (Hp.out.even_sub_one (by lia)) dvd_rfl

end EisensteinSeries
