/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.Bernoulli
public import PadicModForms.ModP.Basic
public import PadicModForms.Rational.Eisenstein

/-!
# Integral and mod-`p` Eisenstein series

This file defines an integral model of `ERat` at `p` and the Eisenstein series of weight `p - 1`
used in the mod-`p` theory.
-/

@[expose] public noncomputable section

open PowerSeries ArithmeticFunction sigma ModularForm

variable {p k : ℕ} [Fact p.Prime]

namespace EisensteinSeries

variable (hk : 3 ≤ k) (hk2 : Even k)

include hk hk2 in
/-- The coefficients of `ERat` are `p`-integral if `p - 1 ∣ k`. -/
theorem coeff_ERat_mem_pLocalInt (hpk : p - 1 ∣ k) (n : ℕ) :
    coeff n (rationalQExpansion (ERat hk hk2)) ∈ pLocalInt p := by
  rw [rationalQExpansion_apply, coeff_ERat _ hk hk2]
  by_cases hn : n = 0
  · simp [hn]
  · have hk_mem : (k : ℚ) ∈ pLocalInt p := by simp
    have htwo_mem : (2 : ℚ) ∈ pLocalInt p := by simp
    have hsigma_mem : (σ (k - 1) n : ℚ) ∈ pLocalInt p := by simp
    grind [div_eq_mul_inv, inv_bernoulli_mem_pLocalInt, mul_mem, neg_mem]

/-- The normalized Eisenstein series `E_k` over the localization of `ℤ` at `p`. -/
noncomputable def E_int (hpk : p - 1 ∣ k) : (pLocalInt p)⟦X⟧ :=
  (rationalQExpansion (ERat hk hk2)).toSubring (pLocalInt p).toSubring
    (coeff_ERat_mem_pLocalInt hk hk2 hpk)

variable (n : ℕ)

@[simp]
theorem coeff_E_int (hpk : p - 1 ∣ k) : (coeff n (E_int hk hk2 hpk) : pLocalInt p) =
      if n = 0 then 1 else -(2 * k / bernoulli k) * σ (k - 1) n := by
  rw [E_int, coeff_toSubring, rationalQExpansion_apply, coeff_ERat]

/-- The constant coefficient of `E_int` is `1`. -/
@[simp]
theorem coeff_E_int_zero (hpk : p - 1 ∣ k) : coeff 0 (E_int hk hk2 hpk) = 1 := by
  exact Subtype.ext <| by simp only [coeff_E_int, reduceIte, OneMemClass.coe_one]

/-- A nonconstant coefficient of `E_int` factors through `Bₖ⁻¹`. -/
theorem coeff_E_int_of_ne_zero (hpk : p - 1 ∣ k) {m : ℕ} (hm : m ≠ 0) :
    coeff m (E_int hk hk2 hpk) =
      -(2 * k) * ⟨_, inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩ * σ (k - 1) m := Subtype.ext <| by
  simp [coeff_E_int, hm, div_eq_mul_inv, show ((2 : pLocalInt p) : ℚ) = 2 from
    map_ofNat (pLocalInt p).subtype 2]

/-- Extending scalars from `pLocalInt p` to `ℚ` sends `E_int` to the rational `q`-expansion of
`ERat`. -/
theorem E_int_map (hpk : p - 1 ∣ k) :
    (E_int hk hk2 hpk).map (algebraMap _ ℚ) = rationalQExpansion (ERat hk hk2) := by
  ext; simp [coeff_E_int, coeff_ERat]

namespace ModP

/-- The normalized Eisenstein series of weight `p - 1` over the localization of `ℤ` at `p`. -/
noncomputable abbrev E (hp : 5 ≤ p) : (pLocalInt p)⟦X⟧ :=
  E_int (k := p - 1) (by lia) ((Fact.out : p.Prime).even_sub_one (by lia)) dvd_rfl

/-- The coefficients of `E`. -/
@[simp]
theorem coeff_E (hp : 5 ≤ p) (m : ℕ) : (coeff m (E hp) : pLocalInt p) =
    if m = 0 then 1 else -(2 * (p - 1) / bernoulli (p - 1)) * σ (p - 2) m := by
  rw [E, coeff_E_int, Nat.cast_sub (by lia : 1 ≤ p)]
  congr 2

/-- The scalar extension of `E` to `ℚ` is the rational `q`-expansion of `ERat` of weight
`p - 1`. -/
theorem E_map_eq_rationalQExpansion (hp : 5 ≤ p) :
    (E hp).map (algebraMap _ ℚ) =
      rationalQExpansion (ERat (by lia) ((Fact.out : p.Prime).even_sub_one (by lia))) := by
  simpa [Nat.cast_sub (by lia : 1 ≤ p)] using
    E_int_map (p := p) (k := p - 1) (by lia) ((Fact.out : p.Prime).even_sub_one (by lia)) dvd_rfl

end ModP

end EisensteinSeries
