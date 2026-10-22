/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ModP.Filtration
public import PadicModForms.ModP.Differential
import PadicModForms.ModP.Squarefree

/-!
# `Θ` and the filtration

Let `p ≥ 5`, `A = hasseInvPoly hp` and `D = δModP A`, so that `evalE₄E₆ModP D = E₂ModP`, `D` has
weight `p + 1`, and `A` and `D` are relatively prime. For `F` weighted homogeneous of weight `n`
the differential identity `12 Θ (ev F) = n E₂ (ev F) + ev (δ F)` rewrites, using `ev A = 1`, into
the purely polynomial form `12 Θ (ev F) = ev (n D F + A δF)` whose argument is weighted
homogeneous of weight `n + p + 1`.

Consequently `Θ` sends modular forms to modular forms and raises the filtration by at most
`p + 1`, with equality exactly detected by divisibility of `n D F + A δF` by `A`: for a reduced
`F` this happens if and only if `p ∣ n`, because `A` is prime to both `D` and `F`.

Iterating on `E₂ = ev D` of filtration `p + 1` gives the filtration `(j + 1)(p + 1)` for
`Θ^[j] E₂` as long as `j ≤ p - 2`, in particular `p² - 1` for `j = p - 2`; this is the filtration
computation feeding the non-modularity of the divisor-sum series in
`PadicModForms.ModP.ArtinSchreier`.

## Main results

* `ModularForm.twelve_Θ_evalE₄E₆ModP_eq_evalE₄E₆ModP`: the polynomial form of the differential
  identity.
* `ModularForm.exists_isWeightedHomogeneous_Θ_evalE₄E₆ModP`: `Θ` preserves mod-`p` modular forms,
  raising the weight by `p + 1`.
* `ModularForm.modPFiltration_Θ_le`, `ModularForm.modPFiltration_Θ_eq`: the theta filtration
  bound, sharp when `p ∤ fil f`.
* `ModularForm.modPFiltration_iterate_Θ_E₂ModP`: `fil (Θ^[j] E₂) = (j + 1)(p + 1)` for
  `j ≤ p - 2`.
-/

noncomputable section

open EisensteinSeries MvPolynomial
open PowerSeries hiding C X

namespace ModularForm

variable {p n : ℕ} [Fact p.Prime] {F : MvPolynomial (Fin 2) (ZMod p)}

/-- The differential identity in polynomial form: for `F` weighted homogeneous of weight `n`,
`12 Θ (ev F) = ev (n (δA) F + A (δF))`. This eliminates `E₂ModP` from
`twelve_Θ_evalE₄E₆ModP` using `evalE₄E₆ModP_δModP_hasseInvPoly` and
`evalE₄E₆ModP_hasseInvPoly`. -/
public theorem twelve_Θ_evalE₄E₆ModP_eq_evalE₄E₆ModP (hp : 5 ≤ p)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) :
    12 * Θ (evalE₄E₆ModP F) = evalE₄E₆ModP
      ((n : MvPolynomial (Fin 2) (ZMod p)) * δModP (hasseInvPoly hp) * F +
        hasseInvPoly hp * δModP F) := by
  rw [twelve_Θ_evalE₄E₆ModP hF, map_add, map_mul, map_mul, map_mul, map_natCast,
    evalE₄E₆ModP_δModP_hasseInvPoly hp, evalE₄E₆ModP_hasseInvPoly hp, one_mul, mul_assoc]

/-- The polynomial `n (δA) F + A (δF)` of `twelve_Θ_evalE₄E₆ModP_eq_evalE₄E₆ModP` is weighted
homogeneous of weight `n + (p + 1)`: `δA` has weight `p + 1` and `δ` raises the weight by `2`. -/
theorem isWeightedHomogeneous_δModP_hasseInvPoly_mul_add (hp : 5 ≤ p)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) :
    IsWeightedHomogeneous E₄E₆Weights ((n : MvPolynomial (Fin 2) (ZMod p)) *
      δModP (hasseInvPoly hp) * F + hasseInvPoly hp * δModP F) (n + (p + 1)) := by
  refine IsWeightedHomogeneous.add ?_ ?_
  · have := ((isWeightedHomogeneous_C E₄E₆Weights (n : ZMod p)).mul
      (isWeightedHomogeneous_δModP_hasseInvPoly hp)).mul hF
    rwa [map_natCast C, show 0 + (p + 1) + n = n + (p + 1) by lia] at this
  · have := (hasseInvPoly_isWeightedHomogeneous hp).mul (isWeightedHomogeneous_δModP hF)
    rwa [show p - 1 + (n + 2) = n + (p + 1) by lia] at this

/-- `Θ` sends mod-`p` modular forms to mod-`p` modular forms, raising the weight by `p + 1`:
`Θ (ev F)` is the evaluation of `12⁻¹ • (n (δA) F + A (δF))`, which is weighted homogeneous of
weight `n + (p + 1)`. -/
public theorem exists_isWeightedHomogeneous_Θ_evalE₄E₆ModP (hp : 5 ≤ p)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) :
    ∃ G, IsWeightedHomogeneous E₄E₆Weights G (n + (p + 1)) ∧
      evalE₄E₆ModP G = Θ (evalE₄E₆ModP F) := by
  refine ⟨(12⁻¹ : ZMod p) • ((n : MvPolynomial (Fin 2) (ZMod p)) * δModP (hasseInvPoly hp) * F +
    hasseInvPoly hp * δModP F), (weightedHomogeneousSubmodule _ _ _).smul_mem _
      (isWeightedHomogeneous_δModP_hasseInvPoly_mul_add hp hF), ?_⟩
  have h12 : (12 : ZMod p) ≠ 0 := ZMod.ne_zero_of_eq_two_pow_mul_three_pow hp 2 1 (by norm_num)
  rw [map_smul, ← twelve_Θ_evalE₄E₆ModP_eq_evalE₄E₆ModP hp hF, PowerSeries.smul_eq_C_mul,
    ← mul_assoc, ← map_ofNat (PowerSeries.C (R := ZMod p)) 12, ← map_mul, inv_mul_cancel₀ h12,
    map_one, one_mul]

/-- **The theta filtration bound**: `fil (Θ f) ≤ fil f + p + 1`. -/
public theorem modPFiltration_Θ_le (hp : 5 ≤ p) (hF : IsWeightedHomogeneous E₄E₆Weights F n) :
    modPFiltration p (Θ (evalE₄E₆ModP F)) ≤ modPFiltration p (evalE₄E₆ModP F) + (p + 1) := by
  obtain ⟨G, hG, hGF⟩ := exists_isWeightedHomogeneous_modPFiltration hF
  obtain ⟨H, hH, hHG⟩ := exists_isWeightedHomogeneous_Θ_evalE₄E₆ModP hp hG
  exact (hGF ▸ hHG) ▸ modPFiltration_le hH

/-- **The sharp theta filtration formula**: if `p` does not divide `fil f` then
`fil (Θ f) = fil f + p + 1`. For a reduced representative `F` of weight `a = fil f`, if `A`
divided `a (δA) F + A (δF)` it would divide `a (δA) F`, hence `F`, since `a` is invertible and
`A` is relatively prime to `δA`. -/
theorem modPFiltration_Θ_eq (hp : 5 ≤ p) (hF : IsWeightedHomogeneous E₄E₆Weights F n)
    (h0 : evalE₄E₆ModP F ≠ 0) (hpa : ¬p ∣ modPFiltration p (evalE₄E₆ModP F)) :
    modPFiltration p (Θ (evalE₄E₆ModP F)) = modPFiltration p (evalE₄E₆ModP F) + (p + 1) := by
  obtain ⟨G, hG, hGF, hGA⟩ := exists_isWeightedHomogeneous_not_dvd hp hF h0
  have ha : IsUnit (modPFiltration p (evalE₄E₆ModP F) : MvPolynomial (Fin 2) (ZMod p)) := by
    simpa using (isUnit_iff_ne_zero.mpr fun h ↦ hpa ((ZMod.natCast_eq_zero_iff _ _).1 h)).map C
  have key := modPFiltration_eq_of_not_dvd hp
    (isWeightedHomogeneous_δModP_hasseInvPoly_mul_add hp hG) fun h ↦ hGA
      ((ha.isRelPrime_right.mul_right (isRelPrime_hasseInvPoly_δModP hp)).dvd_of_dvd_mul_left
        ((dvd_add_left (dvd_mul_right _ _)).1 h))
  have h12 : (12 : ZMod p) ≠ 0 := ZMod.ne_zero_of_eq_two_pow_mul_three_pow hp 2 1 (by norm_num)
  rwa [← twelve_Θ_evalE₄E₆ModP_eq_evalE₄E₆ModP hp hG, hGF,
    ← map_ofNat (PowerSeries.C (R := ZMod p)) 12, ← PowerSeries.smul_eq_C_mul,
    modPFiltration_smul h12] at key

/-! ### Iterating `Θ` on `E₂` -/

/-- `Θ^[j] E₂ModP` is a mod-`p` modular form of weight `(j + 1)(p + 1)`, by induction on the
representative `δModP (hasseInvPoly hp)` of `E₂ModP` through
`exists_isWeightedHomogeneous_Θ_evalE₄E₆ModP`. -/
public theorem exists_isWeightedHomogeneous_iterate_Θ_E₂ModP (hp : 5 ≤ p) (j : ℕ) :
    ∃ G, IsWeightedHomogeneous E₄E₆Weights G ((j + 1) * (p + 1)) ∧
      evalE₄E₆ModP G = (Θ (R := ZMod p))^[j] E₂ModP := by
  induction j with
  | zero =>
    exact ⟨_, by simpa using isWeightedHomogeneous_δModP_hasseInvPoly hp,
      evalE₄E₆ModP_δModP_hasseInvPoly hp⟩
  | succ j ih =>
    obtain ⟨G, hG, hGE⟩ := ih
    obtain ⟨H, hH, hHG⟩ := exists_isWeightedHomogeneous_Θ_evalE₄E₆ModP hp hG
    exact ⟨H, by grind, by rw [hHG, hGE, Function.iterate_succ_apply']⟩

/-- The filtration of `E₂ = Ẽ_{p+1}` is exactly `p + 1`: its representative
`δModP (hasseInvPoly hp)` is relatively prime to the Hasse invariant, hence reduced. -/
theorem modPFiltration_E₂ModP (hp : 5 ≤ p) : modPFiltration p (E₂ModP (p := p)) = p + 1 := by
  rw [← evalE₄E₆ModP_δModP_hasseInvPoly hp]
  exact modPFiltration_eq_of_not_dvd hp (isWeightedHomogeneous_δModP_hasseInvPoly hp) fun h ↦
    not_isUnit_hasseInvPoly hp (isRelPrime_hasseInvPoly_δModP hp dvd_rfl h)

/-- **The filtration of the iterates of `Θ` on `E₂`**: `fil (Θ^[j] E₂) = (j + 1)(p + 1)` for
`j ≤ p - 2`. In this range `(j + 1)(p + 1) ≡ j + 1 ≢ 0 mod p`, so the sharp theta formula applies
at every step of the induction. -/
public theorem modPFiltration_iterate_Θ_E₂ModP (hp : 5 ≤ p) {j : ℕ} (hj : j ≤ p - 2) :
    modPFiltration p ((Θ (R := ZMod p))^[j] E₂ModP) = (j + 1) * (p + 1) := by
  induction j with
  | zero => simpa using modPFiltration_E₂ModP hp
  | succ j ih =>
    obtain ⟨G, hG, hGE⟩ := exists_isWeightedHomogeneous_iterate_Θ_E₂ModP hp j
    have ih := ih (by lia)
    rw [← hGE] at ih
    rw [Function.iterate_succ_apply', ← hGE]
    rw [modPFiltration_Θ_eq hp hG (fun h ↦ ?_) ?_, ih]
    · ring
    · rw [ih, (Fact.out : p.Prime).dvd_mul]
      rintro (h | h)
      · grind [Nat.le_of_dvd j.succ_pos h]
      · grind [Nat.le_of_dvd one_pos (Nat.dvd_add_self_left.1 h)]
    · rw [h, modPFiltration_zero] at ih
      exact Nat.mul_ne_zero j.succ_ne_zero p.succ_ne_zero ih.symm

end ModularForm
