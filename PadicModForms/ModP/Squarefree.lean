/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.MvPolynomial
public import PadicModForms.ModP.Differential
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Squarefreeness of the Hasse invariant

Let `p ≥ 5`. The Hasse invariant `hasseInvPoly hp` is weighted homogeneous of weight `p - 1` in
`X₀, X₁` over `ZMod p`, and its evaluation under `evalE₄E₆ModP` is `1`. This file proves that it is
relatively prime to its Ramanujan derivative and deduces that it is squarefree.

The proof rules out an irreducible common factor `F` of `hasseInvPoly hp` and of its Ramanujan
derivative, in four steps. To begin with `F` is weighted homogeneous, of some weight `c` with
`1 ≤ c ≤ p - 1` (`exists_isWeightedHomogeneous_of_irreducible_dvd`,
`weight_le_of_dvd_hasseInvPoly`).

1. `F ∣ δ F` (`dvd_δModP_of_dvd_of_dvd_δModP`). Writing `hasseInvPoly hp = F ^ r * G` with
   `F ∤ G`, the Leibniz rule makes the order of vanishing at `F` drop by exactly one at each
   differentiation — the scalars it produces are invertible because `r ≤ p - 1` — so the second
   derivative of `hasseInvPoly hp` vanishes to order `r - 2` at `F`, whereas
   `δModP (δModP (hasseInvPoly hp)) = -X₀ * hasseInvPoly hp` vanishes to order at least `r`.
2. `δ F = 0` (`δModP_eq_zero_of_dvd_of_dvd_δModP`). Otherwise `δ F / F` would be weighted
   homogeneous of weight `2`, since `δ` raises the weight by `2`, and no monomial in variables of
   weights `4` and `6` has weight `2`.
3. `F ∣ X₀³ - X₁²` (`dvd_X_zero_pow_three_sub_X_one_sq`). Eliminating one partial derivative at a
   time between `δ F = 0` and Euler's identity gives `4 (X₀³ - X₁²) ∂₀F = c X₀² F` and
   `6 (X₀³ - X₁²) ∂₁F = -c X₁ F`. If `F` did not divide `X₀³ - X₁²` it would divide both partial
   derivatives, which have smaller weight, so both would vanish and Euler's identity would read
   `c F = 0`.
4. `X₀³ - X₁²` is irreducible, so `F` is associated to it; but `evalE₄E₆ModP F` is a unit, being
   a factor of `evalE₄E₆ModP (hasseInvPoly hp) = 1`, while
   `evalE₄E₆ModP (X₀³ - X₁²) = 1728 Δ` has zero constant coefficient.

## Main results

* `ModularForm.dvd_δModP_of_dvd_of_dvd_δModP`: step 1.
* `ModularForm.δModP_eq_zero_of_dvd_of_dvd_δModP`: steps 1 and 2 combined.
* `ModularForm.dvd_X_zero_pow_three_sub_X_one_sq`: step 3.
* `ModularForm.le_of_pow_dvd_hasseInvPoly`: if `F ^ r` divides the Hasse invariant, with `F`
  irreducible, then `r ≤ p - 1`. In particular `r` is invertible in `ZMod p`.
* `ModularForm.isRelPrime_hasseInvPoly_δModP`: the Hasse invariant is relatively prime to its
  Ramanujan derivative.
* `ModularForm.hasseInvPoly_squarefree`: the Hasse invariant is squarefree.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace ModularForm

variable {p : ℕ} [Fact p.Prime] {F G : MvPolynomial (Fin 2) (ZMod p)} {r k : ℕ}

/-! ### Weights of the factors of the Hasse invariant -/

theorem hasseInvPoly_ne_zero (hp : 5 ≤ p) : hasseInvPoly hp ≠ 0 := fun h ↦ by
  simpa [h] using evalE₄E₆ModP_hasseInvPoly hp

/-- An irreducible factor of the Hasse invariant is weighted homogeneous of positive weight. -/
theorem exists_isWeightedHomogeneous_of_irreducible_dvd (hp : 5 ≤ p) (hF : Irreducible F)
    (hFA : F ∣ hasseInvPoly hp) : ∃ c, 1 ≤ c ∧ IsWeightedHomogeneous E₄E₆Weights F c := by
  obtain ⟨c, hc⟩ := (hasseInvPoly_isWeightedHomogeneous hp).irreducible_factor
    (hasseInvPoly_ne_zero hp) hF hFA
  refine ⟨c, ?_, hc⟩
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · exact absurd (hc.isUnit_of_ne_zero E₄E₆Weights_ne_zero hF.ne_zero) hF.not_isUnit
  · exact hc0

/-- The weight of a weighted homogeneous factor of the Hasse invariant is at most `p - 1`, the
weight of the Hasse invariant itself. -/
theorem weight_le_of_dvd_hasseInvPoly (hp : 5 ≤ p) (hr : IsWeightedHomogeneous E₄E₆Weights F r)
    (hFA : F ∣ hasseInvPoly hp) : r ≤ p - 1 :=
  hr.weight_le_of_dvd (hasseInvPoly_isWeightedHomogeneous hp) (hasseInvPoly_ne_zero hp) hFA

/-- If `F ^ r` divides the Hasse invariant, with `F` irreducible, then `r ≤ p - 1`. -/
theorem le_of_pow_dvd_hasseInvPoly (hp : 5 ≤ p) (hF : Irreducible F)
    (hr : F ^ r ∣ hasseInvPoly hp) : r ≤ p - 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · exact Nat.zero_le _
  obtain ⟨c, hc1, hc⟩ := exists_isWeightedHomogeneous_of_irreducible_dvd hp hF
    ((dvd_pow_self F hr0.ne').trans hr)
  have : r * c ≤ p - 1 := weight_le_of_dvd_hasseInvPoly hp (by simpa using hc.pow r) hr
  grind [Nat.le_mul_of_pos_right r hc1]

/-- A natural number that is positive and smaller than `p` is a unit of `(ZMod p)[X₀, X₁]`. -/
private theorem isUnit_natCast (hk0 : 0 < k) (hkp : k < p) :
    IsUnit (k : MvPolynomial (Fin 2) (ZMod p)) := by
  have : (k : ZMod p) ≠ 0 := fun h ↦
    absurd (Nat.le_of_dvd hk0 ((ZMod.natCast_eq_zero_iff _ _).1 h)) (by lia)
  simpa using (isUnit_iff_ne_zero.mpr this).map C

private theorem isUnit_natCast_of_pow_dvd (hp : 5 ≤ p) (hF : Irreducible F)
  (hr : F ^ r ∣ hasseInvPoly hp) (hk0 : 0 < k) (hkr : k ≤ r) :
    IsUnit (k : MvPolynomial (Fin 2) (ZMod p)) :=
  isUnit_natCast hk0 <| by
    grind [Nat.Prime.two_le (Fact.out (p := p.Prime)), le_of_pow_dvd_hasseInvPoly hp hF hr]

/-! ### Step 1: a common factor divides its own derivative -/

/-- The cofactor left behind when `δ` is applied to `F ^ (n + 1) * G`; see `δModP_pow_succ_mul`. -/
private def leibnizCofactor (F G : MvPolynomial (Fin 2) (ZMod p)) (n : ℕ) :
    MvPolynomial (Fin 2) (ZMod p) := (↑(n + 1)) * (G * δModP F) + F * δModP G

/-- The Leibniz rule at a power: differentiating `F ^ (n + 1) * G` lowers the exponent by one. -/
private theorem δModP_pow_succ_mul (F G : MvPolynomial (Fin 2) (ZMod p)) (n : ℕ) :
    δModP (F ^ (n + 1) * G) = F ^ n * leibnizCofactor F G n := by
  rw [Derivation.leibniz, Derivation.leibniz_pow]
  grind [leibnizCofactor, Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]

/-- The cofactor is again prime to `F`, provided the scalar `n + 1` is invertible. -/
private theorem not_dvd_leibnizCofactor (hprime : Prime F)
  (hu : IsUnit (↑(k + 1) : MvPolynomial (Fin 2) (ZMod p)))
    (hδF : ¬F ∣ δModP F) (hG : ¬F ∣ G) : ¬F ∣ leibnizCofactor F G k := fun h ↦ by
  rcases hprime.dvd_mul.1 (hu.dvd_mul_left.1 ((dvd_add_left (dvd_mul_right F _)).mp h)) with h' | h'
  · exact hG h'
  · exact hδF h'

/-- An irreducible polynomial dividing `hasseInvPoly` and `δ hasseInvPoly` divides `δ` of itself. -/
theorem dvd_δModP_of_dvd_of_dvd_δModP (hp : 5 ≤ p) (hF : Irreducible F) (hFA : F ∣ hasseInvPoly hp)
    (hFB : F ∣ δModP (hasseInvPoly hp)) : F ∣ δModP F := by
  by_contra hFδF
  have hprime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hF
  obtain ⟨G, hG, hFG⟩ := (FiniteMultiplicity.of_prime_left hprime
    (hasseInvPoly_ne_zero hp)).exists_eq_pow_mul_and_not_dvd
  obtain ⟨r, hr⟩ : ∃ r, multiplicity F (hasseInvPoly hp) = r := ⟨_, rfl⟩
  rw [hr] at hG
  have hpow : F ^ r ∣ hasseInvPoly hp := ⟨G, hG⟩
  obtain _ | n := r
  · rw [pow_zero, one_mul] at hG
    exact hFG (hG ▸ hFA)
  have : δModP (hasseInvPoly hp) = F ^ n * leibnizCofactor F G n := by rw [hG, δModP_pow_succ_mul]
  have hFE := not_dvd_leibnizCofactor hprime
    (isUnit_natCast_of_pow_dvd hp hF hpow n.succ_pos (Nat.le_refl _)) hFδF hFG
  obtain _ | m := n
  · rw [pow_zero, one_mul] at this
    exact hFE (this ▸ hFB)
  suffices δModP (δModP (hasseInvPoly hp)) =
      F ^ m * leibnizCofactor F (leibnizCofactor F G (m + 1)) m by
    suffices hδ2' : δModP (δModP (hasseInvPoly hp)) = F ^ m * (-X 0 * F ^ 2 * G) by
      refine not_dvd_leibnizCofactor hprime (isUnit_natCast_of_pow_dvd hp hF hpow
        m.succ_pos (Nat.le_succ (m + 1))) hFδF hFE ?_
      rw [mul_left_cancel₀ (pow_ne_zero m hF.ne_zero) (this.symm.trans hδ2')]
      exact ⟨-X 0 * F * G, by ring⟩
    grind [δModP_sq_hasseInvPoly hp]
  rw [this, δModP_pow_succ_mul]

/-! ### Step 2: the derivative of a common factor vanishes -/

/-- In variables of weights `4` and `6` there is no nonzero weighted homogeneous polynomial of
weight `2`. -/
theorem eq_zero_of_isWeightedHomogeneous_two (hG : IsWeightedHomogeneous E₄E₆Weights G 2) :
    G = 0 :=
  hG.eq_zero_of_no_monomials fun d ↦ by rw [weight_E₄E₆_apply]; omega

/-- An irreducible factor of the Hasse invariant dividing its own derivative is killed by `δ`. -/
theorem δModP_eq_zero_of_dvd_δModP (hp : 5 ≤ p) (hF : Irreducible F) (hFA : F ∣ hasseInvPoly hp)
    (h : F ∣ δModP F) : δModP F = 0 := by
  by_contra hδ0
  obtain ⟨c, _, hc⟩ := exists_isWeightedHomogeneous_of_irreducible_dvd hp hF hFA
  obtain ⟨H, hH⟩ := h
  have hH0 : H ≠ 0 := fun h0 ↦ hδ0 (by grind)
  obtain ⟨m, k, hm, _, _⟩ := (hH ▸ isWeightedHomogeneous_δModP hc).mul_factors hF.ne_zero hH0
  exact hH0 (eq_zero_of_isWeightedHomogeneous_two (by grind [hm.inj_right hF.ne_zero hc]))

/-- **Steps 1 and 2**: an irreducible common factor of the Hasse invariant and of its Ramanujan
derivative is killed by `δ`. -/
theorem δModP_eq_zero_of_dvd_of_dvd_δModP (hp : 5 ≤ p) (hF : Irreducible F)
    (hFA : F ∣ hasseInvPoly hp) (hFB : F ∣ δModP (hasseInvPoly hp)) : δModP F = 0 :=
  δModP_eq_zero_of_dvd_δModP hp hF hFA (dvd_δModP_of_dvd_of_dvd_δModP hp hF hFA hFB)

/-! ### Step 3: a common factor divides `X₀³ - X₁²` -/

/-- Eliminating `∂₁F` between `δ F = 0` and Euler's identity. -/
private theorem four_mul_pderiv_zero (hk : IsWeightedHomogeneous E₄E₆Weights F k)
    (hδ : δModP F = 0) :
    4 * ((X 0 ^ 3 - X 1 ^ 2) * pderiv 0 F) = (k : MvPolynomial (Fin 2) (ZMod p)) * X 0 ^ 2 * F := by
  grind [euler_E₄E₆Weights hk, δModP_apply]

/-- Eliminating `∂₀F` between `δ F = 0` and Euler's identity. -/
private theorem six_mul_pderiv_one (hk : IsWeightedHomogeneous E₄E₆Weights F k) (hδ : δModP F = 0) :
    6 * ((X 0 ^ 3 - X 1 ^ 2) * pderiv 1 F) = -((k : MvPolynomial (Fin 2) (ZMod p)) * X 1 * F) := by
  grind [euler_E₄E₆Weights hk, δModP_apply]

/-- A partial derivative of `F` divisible by `F` vanishes: it has strictly smaller weight. -/
private theorem pderiv_eq_zero_of_dvd {i : Fin 2} (hr : IsWeightedHomogeneous E₄E₆Weights F r)
    (hw : 0 < E₄E₆Weights i) (h : F ∣ pderiv i F) : pderiv i F = 0 := by
  rcases lt_or_ge r (E₄E₆Weights i) with hlt | hle
  · exact hr.pderiv_eq_zero hlt
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
    by_contra h0
    exact absurd (hr.weight_le_of_dvd (hr.pderiv (n' := m) (by lia)) h0 h) (by lia)

/-- **Step 3**: an irreducible factor of the Hasse invariant killed by `δ` divides `X₀³ - X₁²`,
the polynomial whose evaluation is `1728 Δ`. -/
theorem dvd_X_zero_pow_three_sub_X_one_sq (hp : 5 ≤ p) (hF : Irreducible F)
    (hFA : F ∣ hasseInvPoly hp) (hδ : δModP F = 0) :
    F ∣ (X 0 : MvPolynomial (Fin 2) (ZMod p)) ^ 3 - X 1 ^ 2 := by
  by_contra hdvd
  have hprime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hF
  obtain ⟨c, hc1, hc⟩ := exists_isWeightedHomogeneous_of_irreducible_dvd hp hF hFA
  have hu4 : IsUnit (4 : MvPolynomial (Fin 2) (ZMod p)) := by
    simpa using isUnit_natCast (k := 4) (by norm_num) (by lia)
  have hu6 : IsUnit (6 : MvPolynomial (Fin 2) (ZMod p)) := by
    have h2 : IsUnit (2 : MvPolynomial (Fin 2) (ZMod p)) := by
      simpa using isUnit_natCast (k := 2) (by norm_num) (by lia)
    have h3 : IsUnit (3 : MvPolynomial (Fin 2) (ZMod p)) := by
      simpa using isUnit_natCast (k := 3) (by norm_num) (by lia)
    grind [show (6 : MvPolynomial (Fin 2) (ZMod p)) = 2 * 3 by norm_num]
  suffices pderiv 0 F = 0 ∧ pderiv 1 F = 0 by
    exact hF.ne_zero <| ((isUnit_natCast hc1
    (by grind [weight_le_of_dvd_hasseInvPoly hp hc hFA])).mul_right_eq_zero).mp
      (by grind [euler_E₄E₆Weights hc])
  refine ⟨pderiv_eq_zero_of_dvd hc (by simp) ?_,
    pderiv_eq_zero_of_dvd hc (by simp) ?_⟩
  · exact (hprime.dvd_mul.mp (hu4.dvd_mul_left.mp ⟨(c : MvPolynomial (Fin 2) (ZMod p)) * X 0 ^ 2,
      by rw [four_mul_pderiv_zero hc hδ]; ring⟩)).resolve_left hdvd
  · exact (hprime.dvd_mul.mp (hu6.dvd_mul_left.mp ⟨-((c : MvPolynomial (Fin 2) (ZMod p)) * X 1),
      by rw [six_mul_pderiv_one hc hδ]; ring⟩)).resolve_left hdvd

/-! ### Step 4: there is no common factor -/

/-- `X₀³ - X₁²`, whose evaluation is `1728 Δ`, is weighted homogeneous of weight `12`. -/
theorem isWeightedHomogeneous_X_zero_pow_three_sub_X_one_sq : IsWeightedHomogeneous E₄E₆Weights
    ((X 0 : MvPolynomial (Fin 2) (ZMod p)) ^ 3 - X 1 ^ 2) 12 :=
  IsWeightedHomogeneous.sub
    (by simpa using (isWeightedHomogeneous_X (ZMod p) E₄E₆Weights 0).pow 3)
    (by simpa using (isWeightedHomogeneous_X (ZMod p) E₄E₆Weights 1).pow 2)

/-- `X₀³ - X₁²` is irreducible. -/
theorem irreducible_X_zero_pow_three_sub_X_one_sq :
    Irreducible ((X 0 : MvPolynomial (Fin 2) (ZMod p)) ^ 3 - X 1 ^ 2) := by
  simpa [X_pow_eq_monomial, sub_eq_add_neg] using
    irreducible_add_monomial_of_coprime (K := ZMod p) (m := 3) (n := 2) (a := 1) (b := -1)
      (by norm_num) (by norm_num) (by norm_num) one_ne_zero (neg_ne_zero.mpr one_ne_zero)

/-- The evaluation of `X₀³ - X₁²` is `E₄³ - E₆²`, that is `1728 Δ`. -/
theorem evalE₄E₆ModP_X_zero_pow_three_sub_X_one_sq :
    evalE₄E₆ModP ((X 0 : MvPolynomial (Fin 2) (ZMod p)) ^ 3 - X 1 ^ 2) =
      EisensteinSeries.E₄ModP ^ 3 - EisensteinSeries.E₆ModP ^ 2 := by
  rw [map_sub, map_pow, map_pow, evalE₄E₆ModP_X_zero, evalE₄E₆ModP_X_one]

/-- The evaluation of `X₀³ - X₁²` has zero constant coefficient. -/
theorem constantCoeff_evalE₄E₆ModP_X_zero_pow_three_sub_X_one_sq :
    PowerSeries.constantCoeff (evalE₄E₆ModP (p := p) ((X 0) ^ 3 - X 1 ^ 2)) = 0 := by
  have h4 : PowerSeries.constantCoeff (EisensteinSeries.E₄ModP (p := p)) = 1 := by
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h6 : PowerSeries.constantCoeff (EisensteinSeries.E₆ModP (p := p)) = 1 := by
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  grind [evalE₄E₆ModP_X_zero_pow_three_sub_X_one_sq]

/-- **Step 4**: an irreducible factor of the Hasse invariant does not divide its Ramanujan
derivative. -/
theorem not_dvd_δModP_hasseInvPoly (hp : 5 ≤ p) (hF : Irreducible F) (hFA : F ∣ hasseInvPoly hp) :
    ¬F ∣ δModP (hasseInvPoly hp) := fun hFB ↦ by
  obtain ⟨u, hu⟩ := hF.associated_of_dvd irreducible_X_zero_pow_three_sub_X_one_sq
    (dvd_X_zero_pow_three_sub_X_one_sq hp hF hFA (δModP_eq_zero_of_dvd_of_dvd_δModP hp hF hFA hFB))
  obtain ⟨G, hG⟩ := hFA
  have hunit : IsUnit (evalE₄E₆ModP F) := .of_mul_eq_one (evalE₄E₆ModP G) <| by
    rw [← map_mul, ← hG, evalE₄E₆ModP_hasseInvPoly hp]
  have h0 := constantCoeff_evalE₄E₆ModP_X_zero_pow_three_sub_X_one_sq (p := p)
  rw [← hu, map_mul] at h0
  exact ((hunit.mul (u.isUnit.map evalE₄E₆ModP)).map PowerSeries.constantCoeff).ne_zero h0

/-- **The Hasse invariant is relatively prime to its Ramanujan derivative.** -/
theorem isRelPrime_hasseInvPoly_δModP (hp : 5 ≤ p) :
    IsRelPrime (hasseInvPoly hp) (δModP (hasseInvPoly hp)) := fun z hzA hzB ↦ by
  by_contra hz
  have hz0 : z ≠ 0 := fun h ↦ hasseInvPoly_ne_zero hp (zero_dvd_iff.mp (h ▸ hzA))
  obtain ⟨F, hF, hFz⟩ := WfDvdMonoid.exists_irreducible_factor hz hz0
  exact not_dvd_δModP_hasseInvPoly hp hF (hFz.trans hzA) (hFz.trans hzB)

/-- **The Hasse invariant is squarefree.** -/
theorem hasseInvPoly_squarefree (hp : 5 ≤ p) : Squarefree (hasseInvPoly hp) := by
  rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero (hasseInvPoly_ne_zero hp)]
  intro F hF hF_sq
  have hF_hasseInvPoly : F ∣ hasseInvPoly hp := (dvd_mul_right F F).trans hF_sq
  obtain ⟨G, hG⟩ := hF_sq
  suffices F ∣ δModP (hasseInvPoly hp) by
    exact hF.not_isUnit (isRelPrime_hasseInvPoly_δModP hp hF_hasseInvPoly this)
  refine ⟨leibnizCofactor F G 1, ?_⟩
  simpa [hG, pow_two] using δModP_pow_succ_mul F G 1


end ModularForm
