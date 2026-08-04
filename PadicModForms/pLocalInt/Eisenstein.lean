/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.Bernoulli
public import PadicModForms.Rational.Eisenstein
public import PadicModForms.pLocalInt.Basic

/-!
# Eisenstein series over the localization of `ℤ` at `p`

This file defines integral models at `p` of rational Eisenstein series. It also provides
canonical integral models of `E₂`, `E₄`, and `E₆`; the latter two are integral modular forms.
-/

@[expose] public noncomputable section

open PowerSeries ArithmeticFunction sigma ModularForm SetLike

variable {p k : ℕ} [Fact p.Prime]

namespace EisensteinSeries

variable (hk : 3 ≤ k) (hk2 : Even k)

/-! ### The Eisenstein series `E_k` in weight `k` -/

include hk hk2 in
/-- The coefficients of `ERat` are `p`-integral as soon as `Bₖ⁻¹` is. -/
theorem coeff_ERat_mem_pLocalInt (hB : (bernoulli k)⁻¹ ∈ pLocalInt p) (n : ℕ) :
    coeff n (rationalQExpansion (ERat hk hk2)) ∈ pLocalInt p := by
  rw [rationalQExpansion_apply, coeff_ERat _ hk hk2]
  by_cases hn : n = 0
  · simp [hn]
  · have hk_mem : (k : ℚ) ∈ pLocalInt p := by simp
    have htwo_mem : (2 : ℚ) ∈ pLocalInt p := by simp
    have hsigma_mem : (σ (k - 1) n : ℚ) ∈ pLocalInt p := by simp
    grind [div_eq_mul_inv, mul_mem, neg_mem]

/-- The normalized Eisenstein series `E_k` over the localization of `ℤ` at `p`. -/
noncomputable def E_int (hB : (bernoulli k)⁻¹ ∈ pLocalInt p) : (pLocalInt p)⟦X⟧ :=
  (rationalQExpansion (ERat hk hk2)).toSubring (pLocalInt p).toSubring
    (coeff_ERat_mem_pLocalInt hk hk2 hB)

variable (n : ℕ)

@[simp]
theorem coeff_E_int (hB : (bernoulli k)⁻¹ ∈ pLocalInt p) :
    (coeff n (E_int hk hk2 hB) : pLocalInt p) =
      if n = 0 then 1 else -(2 * k / bernoulli k) * σ (k - 1) n := by
  rw [E_int, coeff_toSubring, rationalQExpansion_apply, coeff_ERat]

/-- The constant coefficient of `E_int` is `1`. -/
@[simp]
theorem coeff_E_int_zero (hB : (bernoulli k)⁻¹ ∈ pLocalInt p) : coeff 0 (E_int hk hk2 hB) = 1 := by
  exact Subtype.ext <| by simp only [coeff_E_int, reduceIte, OneMemClass.coe_one]

/-- A nonconstant coefficient of `E_int` factors through `Bₖ⁻¹`. -/
theorem coeff_E_int_of_ne_zero (hB : (bernoulli k)⁻¹ ∈ pLocalInt p) {m : ℕ} (hm : m ≠ 0) :
    coeff m (E_int hk hk2 hB) =
      -(2 * k) * ⟨_, hB⟩ * σ (k - 1) m := Subtype.ext <| by
  simp [coeff_E_int, hm, div_eq_mul_inv]

/-- Extending scalars from `pLocalInt p` to `ℚ` sends `E_int` to the rational `q`-expansion of
`ERat`. -/
theorem E_int_map (hB : (bernoulli k)⁻¹ ∈ pLocalInt p) :
    (E_int hk hk2 hB).map (algebraMap _ ℚ) = rationalQExpansion (ERat hk hk2) := by
  ext
  simp [coeff_E_int, coeff_ERat]

/-- `E_int` is a `p`-integral modular form of weight `k`. -/
theorem E_int_mem_pLocalIntModularForms (hB : (bernoulli k)⁻¹ ∈ pLocalInt p) :
    E_int hk hk2 hB ∈ pLocalIntModularForms p k :=
  ⟨ERat hk hk2, E_int_map hk hk2 hB⟩

omit hk hk2

/-! ### `E₂` -/

/-- The coefficients of `E₂Rat` are integral at every prime. -/
theorem coeff_E₂Rat_mem_pLocalInt (n : ℕ) : coeff n E₂Rat ∈ pLocalInt p := by
  rw [coeff_E₂Rat]
  split_ifs
  · exact one_mem ..
  · rw [show (-24 : ℚ) * (σ 1 n : ℚ) = ((-24 * (σ 1 n : ℤ) : ℤ) : ℚ) by push_cast; ring]
    exact intCast_mem _ _

/-- The rational `q`-expansion `E₂Rat`, with coefficients in `pLocalInt p`. -/
noncomputable def E₂_int : (pLocalInt p)⟦X⟧ :=
  E₂Rat.toSubring (pLocalInt p).toSubring coeff_E₂Rat_mem_pLocalInt

@[simp]
theorem coeff_E₂_int (n : ℕ) : ((coeff n E₂_int : pLocalInt p) : ℚ) =
    if n = 0 then 1 else (-24 : ℚ) * σ 1 n := by
  rw [E₂_int, coeff_toSubring, coeff_E₂Rat]

/-- Extending scalars to `ℚ` sends `E₂_int` to `E₂Rat`. -/
theorem E₂_int_map : E₂_int.map (algebraMap (pLocalInt p) ℚ) = E₂Rat := by
  ext; simp

/-! ### `E₄` -/

/-- The coefficients of `E₄Rat` are integral at every prime. -/
theorem coeff_E₄Rat_mem_pLocalInt (n : ℕ) : coeff n (E₄Rat : ℚ⟦X⟧) ∈ pLocalInt p := by
  rw [coeff_E₄Rat]
  split_ifs
  · exact one_mem ..
  · rw [show (240 : ℚ) * (σ 3 n : ℚ) = ((240 * (σ 3 n : ℤ) : ℤ) : ℚ) by push_cast; ring]
    exact intCast_mem _ _

/-- The normalized Eisenstein series `E₄` over `pLocalInt p`. -/
noncomputable def E₄_int : (pLocalInt p)⟦X⟧ :=
  (E₄Rat : ℚ⟦X⟧).toSubring (pLocalInt p).toSubring coeff_E₄Rat_mem_pLocalInt

@[simp]
theorem coeff_E₄_int (n : ℕ) : ((coeff n E₄_int : pLocalInt p) : ℚ) =
    if n = 0 then 1 else (240 : ℚ) * σ 3 n := by
  rw [E₄_int, coeff_toSubring, coeff_E₄Rat]

/-- The constant coefficient of `E₄_int` is `1`. -/
@[simp]
theorem constantCoeff_E₄_int : constantCoeff (E₄_int (p := p)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact Subtype.ext <| by rw [coeff_E₄_int]; norm_num

@[simp]
theorem coeff_zero_E₄_int : coeff 0 (E₄_int (p := p)) = 1 :=
  (coeff_zero_eq_constantCoeff_apply _).trans constantCoeff_E₄_int

/-- The `q`-coefficient of `E₄_int` is `240`. -/
@[simp]
theorem coeff_one_E₄_int : coeff 1 (E₄_int (p := p)) = 240 := Subtype.ext <| by
  rw [coeff_E₄_int]
  norm_num

/-- Extending scalars to `ℚ` sends `E₄_int` to the rational `q`-expansion of `E₄Rat`. -/
theorem E₄_int_map : E₄_int.map (algebraMap (pLocalInt p) ℚ) = rationalQExpansion E₄Rat := by
  ext; simp [rationalQExpansion_apply, coeff_E₄Rat]

/-- `E₄_int` is a `p`-integral modular form of weight `4`. -/
theorem E₄_int_mem_pLocalIntModularForms :  E₄_int ∈ pLocalIntModularForms p 4 :=
  ⟨E₄Rat, E₄_int_map⟩

/-- `E₄_int ^ 3` is a `p`-integral modular form of weight `12`. -/
theorem E₄_int_pow_three_mem : E₄_int ^ 3 ∈ pLocalIntModularForms p 12 := by
  simpa using pow_mem_graded 3 (E₄_int_mem_pLocalIntModularForms (p := p))

/-! ### `E₆` -/

/-- The coefficients of `E₆Rat` are integral at every prime. -/
theorem coeff_E₆Rat_mem_pLocalInt (n : ℕ) : coeff n (E₆Rat : ℚ⟦X⟧) ∈ pLocalInt p := by
  rw [coeff_E₆Rat]
  split_ifs
  · exact one_mem ..
  · rw [show -(504 : ℚ) * (σ 5 n : ℚ) = ((-504 * (σ 5 n : ℤ) : ℤ) : ℚ) by push_cast; ring]
    exact intCast_mem ..

/-- The normalized Eisenstein series `E₆` over `pLocalInt p`. -/
noncomputable def E₆_int : (pLocalInt p)⟦X⟧ :=
  (E₆Rat : ℚ⟦X⟧).toSubring (pLocalInt p).toSubring coeff_E₆Rat_mem_pLocalInt

@[simp]
theorem coeff_E₆_int (n : ℕ) : ((coeff n E₆_int : pLocalInt p) : ℚ) =
    if n = 0 then 1 else -(504 : ℚ) * σ 5 n := by
  rw [E₆_int, coeff_toSubring, coeff_E₆Rat]

/-- The constant coefficient of `E₆_int` is `1`. -/
@[simp]
theorem constantCoeff_E₆_int : constantCoeff (E₆_int (p := p)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact Subtype.ext <| by rw [coeff_E₆_int]; norm_num

@[simp]
theorem coeff_zero_E₆_int : coeff 0 (E₆_int (p := p)) = 1 :=
  (coeff_zero_eq_constantCoeff_apply _).trans constantCoeff_E₆_int

/-- The `q`-coefficient of `E₆_int` is `-504`. -/
@[simp]
theorem coeff_one_E₆_int : coeff 1 (E₆_int (p := p)) = -504 := Subtype.ext <| by
  rw [coeff_E₆_int]
  norm_num

/-- Extending scalars to `ℚ` sends `E₆_int` to the rational `q`-expansion of `E₆Rat`. -/
theorem E₆_int_map :
    E₆_int.map (algebraMap (pLocalInt p) ℚ) = rationalQExpansion E₆Rat := by
  ext; simp [rationalQExpansion_apply, coeff_E₆Rat]

/-- `E₆_int` is a `p`-integral modular form of weight `6`. -/
theorem E₆_int_mem_pLocalIntModularForms : E₆_int ∈ pLocalIntModularForms p 6 :=
  ⟨E₆Rat, E₆_int_map⟩

/-- `E₆_int ^ 2` is a `p`-integral modular form of weight `12`. -/
theorem E₆_int_pow_two_mem : E₆_int ^ 2 ∈ pLocalIntModularForms p 12 := by
  simpa using pow_mem_graded 2 (E₆_int_mem_pLocalIntModularForms (p := p))

/-! ### Monomials in `E₄` and `E₆` -/

/-- The monomial `E₄_int ^ a * E₆_int ^ b` is a `p`-integral modular form of weight `4a + 6b`. -/
theorem E₄_int_pow_mul_E₆_int_pow_mem {a b n : ℕ} (hab : 4 * a + 6 * b = n) :
    E₄_int ^ a * E₆_int ^ b ∈ pLocalIntModularForms p n := by
  simpa [show a * 4 + (b : ℤ) * 6 = n by grind] using mul_mem_graded (pow_mem_graded a
    (E₄_int_mem_pLocalIntModularForms (p := p))) (pow_mem_graded b E₆_int_mem_pLocalIntModularForms)

end EisensteinSeries
