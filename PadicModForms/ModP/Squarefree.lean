/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.WeightedHomogeneous
public import PadicModForms.ModP.Differential

/-!
# Towards the squarefreeness of the Hasse invariant

Let `p ≥ 5`. This file works towards the statement that the Hasse invariant `hasseInvPoly` and its
Ramanujan derivative `δ hasseInvPoly` are relatively prime, from which `hasseInvPoly` is
squarefree.

## Main results

* `ModularForm.dvd_δModP_of_dvd_of_dvd_δModP`: an irreducible common factor `F` of the Hasse
  invariant and of its Ramanujan derivative divides `δ F`.
* `ModularForm.δModP_eq_zero_of_dvd_of_dvd_δModP`: such an `F` in fact satisfies `δ F = 0`.
* `ModularForm.le_of_pow_dvd_hasseInvPoly`: if `F ^ r` divides the Hasse invariant, with `F`
  irreducible, then `r ≤ p - 1`. In particular `r` is invertible in `ZMod p`.
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
  · exfalso
    have hw : ∀ i, E₄E₆Weights i ≠ 0 := fun i ↦ by fin_cases i <;> simp
    refine hF.not_isUnit (hc.eq_C_coeff_zero hw ▸ (isUnit_iff_ne_zero.mpr (fun h ↦ ?_)).map C)
    exact hF.ne_zero <| by rw [hc.eq_C_coeff_zero hw, h, map_zero]
  · exact hc0

/-- If `F ^ r` divides the Hasse invariant, with `F` irreducible, then `r ≤ p - 1`. -/
theorem le_of_pow_dvd_hasseInvPoly (hp : 5 ≤ p) (hF : Irreducible F)
    (hr : F ^ r ∣ hasseInvPoly hp) : r ≤ p - 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · exact Nat.zero_le _
  obtain ⟨G, hG⟩ := hr
  obtain ⟨c, hc1, hc⟩ := exists_isWeightedHomogeneous_of_irreducible_dvd hp hF
    ((dvd_pow_self F hr0.ne').trans ⟨G, hG⟩)
  have hFr0 : F ^ r ≠ 0 := pow_ne_zero _ hF.ne_zero
  have hG0 : G ≠ 0 := fun h ↦ (hasseInvPoly_ne_zero hp) (by rw [hG, h, mul_zero])
  have : IsWeightedHomogeneous E₄E₆Weights (F ^ r * G) (p - 1) := by
    simpa [← hG] using hasseInvPoly_isWeightedHomogeneous hp
  obtain ⟨m, k, hm, _, hmk⟩ := this.mul_factors hFr0 hG0
  grind [Nat.le_mul_of_pos_right r hc1, hm.inj_right hFr0 (by simpa using hc.pow r)]

private theorem isUnit_natCast_of_pow_dvd (hp : 5 ≤ p) (hF : Irreducible F)
  (hr : F ^ r ∣ hasseInvPoly hp) (hk0 : 0 < k) (hkr : k ≤ r) :
    IsUnit (k : MvPolynomial (Fin 2) (ZMod p)) := by
  have hkp : k < p := by
    grind [Nat.Prime.two_le (Fact.out (p := p.Prime)), le_of_pow_dvd_hasseInvPoly hp hF hr]
  have : (k : ZMod p) ≠ 0 := fun h ↦
    absurd (Nat.le_of_dvd hk0 ((ZMod.natCast_eq_zero_iff _ _).1 h)) (by lia)
  simpa using (isUnit_iff_ne_zero.mpr this).map C

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

end ModularForm
