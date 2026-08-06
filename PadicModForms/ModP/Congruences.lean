/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ModP.Eisenstein

/-!
# Congruences for Eisenstein series

This file proves congruences between normalized Eisenstein series and `1` modulo powers of `p`,
and Serre's congruence `E₂ ≡ E_{p+1}` modulo `p`.

## Main results

* `E_int_mod_p`, `E_int_mod_p_pow_of_dvd`, `E_int_mod_two_pow_of_dvd`: `Eₖ ≡ 1` modulo `pᵐ` when
  `(p - 1) pᵐ⁻¹ ∣ k`, and its variant at `p = 2`.
* `E_p_sub_one_mod_p`: the case `k = p - 1`, which is what the Hasse invariant is built from.
* `E₂_int_map_toZMod`: **Serre's congruence** `E₂ ≡ E_{p+1}` modulo `p`.
* `E₂_int_map_toZMod_mem_modPModularForms`: consequently the reduction of `E₂` is a mod-`p`
  modular form of weight `p + 1`, although `E₂` itself is not modular.
-/

@[expose] public section

open PowerSeries ArithmeticFunction sigma

variable {p k m : ℕ} [Hp : Fact p.Prime]

namespace EisensteinSeries

open ModP

/-- If `p - 1 ∣ k`, then the normalized Eisenstein series of weight `k` is congruent to `1`
modulo `p`. -/
theorem E_int_mod_p (hk : 3 ≤ k) (hk2 : Even k) (hpk : p - 1 ∣ k) :
    (E_int hk hk2 (inv_bernoulli_mem_pLocalInt hk hk2 hpk)).map pLocalInt.toZMod = 1 := by
  let B_i : pLocalInt p := ⟨_, inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩
  have hB_inv : pLocalInt.toZMod B_i = 0 := toZMod_inv_bernoulli_eq_zero hk hk2 hpk
  ext n
  by_cases hn : n = 0
  · simp [hn, coeff_E_int_zero hk hk2 (inv_bernoulli_mem_pLocalInt hk hk2 hpk)]
  have hcoeff : coeff n (E_int hk hk2 (inv_bernoulli_mem_pLocalInt hk hk2 hpk)) =
      -(2 * k) * B_i * σ (k - 1) n := by
    simpa [B_i] using coeff_E_int_of_ne_zero hk hk2 (inv_bernoulli_mem_pLocalInt hk hk2 hpk) hn
  simp [hn, hcoeff, map_mul, map_mul, map_neg, hB_inv]

/-- If `(p - 1) * p ^ (m - 1) ∣ k`, then `E_k` is congruent to `1` modulo `p ^ m`. -/
theorem E_int_mod_p_pow_of_dvd (hm : 1 ≤ m) (hk : 3 ≤ k) (hk2 : Even k)
  (hkm : (p - 1) * p ^ (m - 1) ∣ k) :
    (E_int hk hk2 (inv_bernoulli_mem_pLocalInt hk hk2 ((dvd_mul_right _ _).trans hkm))).map
      (pLocalInt.toZModPow m) = 1 := by
  let hpk : p - 1 ∣ k := (dvd_mul_right _ _).trans hkm
  let B_i : pLocalInt p := ⟨_, inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩
  have hB : (p : pLocalInt p) ∣ B_i := by simpa [B_i] using p_dvd_inv_bernoulli hk hk2 hpk
  have hpnk : p ^ (m - 1) ∣ k := (dvd_mul_left _ _).trans hkm
  have hkpow : (p : pLocalInt p) ^ (m - 1) ∣ k := by
    obtain ⟨c, hc⟩ := hpnk
    exact ⟨c, Subtype.ext (by norm_num [hc])⟩
  have hscalar : (p : pLocalInt p) ^ m ∣ 2 * k * B_i := by
    obtain ⟨a, ha⟩ := hkpow
    obtain ⟨b, hb⟩ := hB
    exact ⟨2 * a * b, by rw [ha, hb, ← pow_sub_one_mul (by lia : m ≠ 0) _]; ring⟩
  have hscalar_map : pLocalInt.toZModPow m ((2 * k : pLocalInt p) * B_i) = 0 :=
    pLocalInt.toZModPow_eq_zero_of_dvd hscalar
  ext n
  by_cases hn : n = 0
  · simp [hn, coeff_E_int_zero hk hk2 (inv_bernoulli_mem_pLocalInt hk hk2 hpk)]
  have hcoeff : coeff n (E_int hk hk2 (inv_bernoulli_mem_pLocalInt hk hk2 hpk)) =
      -(2 * k) * B_i * σ (k - 1) n := by
    simpa [B_i] using coeff_E_int_of_ne_zero hk hk2 (inv_bernoulli_mem_pLocalInt hk hk2 hpk) hn
  simp [hn, hcoeff, map_mul, map_neg, hscalar_map]

/-- If `2 ^ (m - 2) ∣ k`, then `E_k` is congruent to `1` modulo `2 ^ m`. -/
theorem E_int_mod_two_pow_of_dvd (hm : 2 ≤ m) (hk : 3 ≤ k) (hk2 : Even k) (hkm : 2 ^ (m - 2) ∣ k) :
    (E_int (p := 2) hk hk2 (inv_bernoulli_mem_pLocalInt hk hk2 (by simp))).map
      (pLocalInt.toZModPow m) = 1 := by
  let hpk : 2 - 1 ∣ k := by simp
  let B_i : pLocalInt 2 := ⟨_, inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩
  have hB : 2 ∣ B_i := by simpa [B_i] using p_dvd_inv_bernoulli hk hk2 hpk
  have hkpow : 2 ^ (m - 2) ∣ (k : pLocalInt 2) := by
    obtain ⟨c, hc⟩ := hkm
    exact ⟨c, Subtype.ext (by norm_num [hc])⟩
  have hscalar : 2 ^ m ∣ 2 * k * B_i := by
    obtain ⟨a, ha⟩ := hkpow
    obtain ⟨b, hb⟩ := hB
    refine ⟨a * b, ?_⟩
    calc _ = 2 ^ (m - 2 + 2) * a * b := by rw [ha, hb]; ring
      _ = _ := by rw [show m - 2 + 2 = m by lia]; ring
  have hscalar_map : pLocalInt.toZModPow m ((2 * k : pLocalInt 2) * B_i) = 0 :=
    pLocalInt.toZModPow_eq_zero_of_dvd hscalar
  ext n
  by_cases hn : n = 0
  · simp [hn, coeff_E_int_zero hk hk2 (inv_bernoulli_mem_pLocalInt hk hk2 hpk)]
  have hcoeff : coeff n (E_int hk hk2 (inv_bernoulli_mem_pLocalInt hk hk2 hpk)) =
      -(2 * k) * B_i * σ (k - 1) n := by
    simpa [B_i] using coeff_E_int_of_ne_zero hk hk2 (inv_bernoulli_mem_pLocalInt hk hk2 hpk) hn
  simp [hn, hcoeff, map_mul, map_neg, hscalar_map]

/-- The normalized Eisenstein series of weight `p - 1` is congruent to `1` modulo `p`. -/
theorem E_p_sub_one_mod_p (hp : 5 ≤ p) : (E hp).map pLocalInt.toZMod = 1 :=
  E_int_mod_p (by lia) (Hp.out.even_sub_one (by lia)) (by rfl)

/-! ### Serre's congruence `E₂ ≡ E_{p+1}` modulo `p` -/

section E₂

variable (hp5 : 5 ≤ p)

include hp5

/-- Weight `p + 1` is even, since `p` is an odd prime. -/
theorem even_p_add_one : Even (p + 1) :=
  (Hp.out.odd_of_ne_two (by lia)).add_one

/-- The normalized Eisenstein series of weight `p + 1` over the localization of `ℤ` at `p`. -/
noncomputable def E_p_add_one : (pLocalInt p)⟦X⟧ :=
  E_int (k := p + 1) (by lia) (even_p_add_one hp5) (inv_bernoulli_p_add_one_mem_pLocalInt hp5)

/-- `E_{p+1}` is a `p`-integral modular form of weight `p + 1`. -/
theorem E_p_add_one_mem_pLocalIntModularForms : E_p_add_one hp5 ∈ pLocalIntModularForms p (p + 1) :=
  E_int_mem_pLocalIntModularForms ..

omit hp5

/-- The nonconstant coefficients of `E₂_int`. -/
theorem coeff_E₂_int_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    coeff n (E₂_int (p := p)) = -24 * (σ 1 n : pLocalInt p) :=
  Subtype.ext <| by simp [coeff_E₂_int, hn]

include hp5

/-- **Serre's congruence**: `E₂ ≡ E_{p+1}` modulo `p`. Consequently the reduction of `E₂` is a
mod-`p` modular form of weight `p + 1`, which is what makes `Θ` raise weights by `p + 1`. -/
theorem E₂_int_map_toZMod :
    (E₂_int : (pLocalInt p)⟦X⟧).map pLocalInt.toZMod = (E_p_add_one hp5).map pLocalInt.toZMod := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 : coeff 0 (E₂_int (p := p)) = 1 := Subtype.ext <| by rw [coeff_E₂_int]; norm_num
    rw [coeff_map, coeff_map, E_p_add_one, coeff_E_int_zero, h0]
  · simp only [coeff_map, coeff_E₂_int_of_ne_zero hn, E_p_add_one, coeff_E_int_of_ne_zero _ _ _ hn,
    map_mul, map_neg, map_natCast, map_ofNat, toZMod_inv_bernoulli_p_add_one hp5]
    simp [sigma_apply, show (24 : ZMod p) = 2 * 12 by norm_num]

/-- The reduction of `E₂` modulo `p` is a mod-`p` modular form of weight `p + 1`. -/
theorem E₂_int_map_toZMod_mem_modPModularForms : (E₂_int : (pLocalInt p)⟦X⟧).map pLocalInt.toZMod ∈
      modPModularForms p ((p + 1 : ℕ) : ℤ) := by
  rw [mem_modPModularForms, E₂_int_map_toZMod hp5]
  obtain ⟨F, hF⟩ := E_p_add_one_mem_pLocalIntModularForms hp5
  exact ⟨_, F, hF, rfl⟩

end E₂

end EisensteinSeries
