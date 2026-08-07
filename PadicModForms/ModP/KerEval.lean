/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ModP.Squarefree
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import PadicModForms.pLocalInt.Discriminant

/-!
# Towards the kernel of the evaluation at `E₄` and `E₆`

Let `p ≥ 5` and write `A = hasseInvPoly hp`, weighted homogeneous of weight `d = p - 1` with
`evalE₄E₆ModP A = 1`. We prove here that `A - 1` is irreducible.

## Main results

* `ModularForm.exists_irreducible_dvd_hasseInvPoly`: the Hasse invariant has an irreducible factor
`π`, and `π * π` does not divide it.
* `ModularForm.irreducible_X_pow_sub_C_hasseInvPoly`: `T ^ (p - 1) - A` is irreducible.
-/

@[expose] public noncomputable section

open Polynomial

namespace ModularForm

variable {p : ℕ} [Fact p.Prime] {P : MvPolynomial (Fin 2) (ZMod p)} {N : ℕ}

/-! ### An irreducible factor of the Hasse invariant -/

/-- The Hasse invariant, being neither zero nor a unit, has an irreducible factor `π`; since it is
squarefree, `π * π` does not divide it. -/
theorem exists_irreducible_dvd_hasseInvPoly (hp : 5 ≤ p) : ∃ π : MvPolynomial (Fin 2) (ZMod p),
    Irreducible π ∧ π ∣ hasseInvPoly hp ∧ ¬π * π ∣ hasseInvPoly hp := by
  obtain ⟨π, hπ, hπA⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_hasseInvPoly hp) (hasseInvPoly_ne_zero hp)
  exact ⟨π, hπ, hπA, fun h ↦ hπ.not_isUnit (hasseInvPoly_squarefree hp π h)⟩

/-! ### Eisenstein's criterion for `T ^ (p - 1) - A` -/

/-- `T ^ (p - 1) - A` is Eisenstein at an irreducible factor `π` of the Hasse invariant `A`: it is
monic, its intermediate coefficients vanish, and its constant coefficient `-A` is divisible by `π`
but not by `π ^ 2`. -/
theorem isEisensteinAt_X_pow_sub_C_hasseInvPoly (hp : 5 ≤ p) (hP : Irreducible P)
    (hPA : P ∣ hasseInvPoly hp) (hP2 : ¬P * P ∣ hasseInvPoly hp) :
    (X ^ (p - 1) - C (hasseInvPoly hp)).IsEisensteinAt (Ideal.span {P}) where
  leading := by
    rw [(monic_X_pow_sub_C _ (by lia)).leadingCoeff, Ideal.mem_span_singleton]
    exact fun h ↦ hP.not_isUnit (isUnit_of_dvd_one h)
  mem {n} hn := by
    rw [natDegree_X_pow_sub_C] at hn
    rw [coeff_sub, coeff_X_pow, if_neg (by lia), coeff_C, Ideal.mem_span_singleton]
    split_ifs <;> simp_all
  notMem := by
    rw [coeff_sub, coeff_X_pow, if_neg (by lia), coeff_C_zero, zero_sub,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact fun h ↦ hP2 (by rwa [← dvd_neg, ← pow_two])

/-- **Eisenstein's criterion**: `T ^ (p - 1) - A` is irreducible in `(ZMod p)[X₀, X₁][T]`. -/
theorem irreducible_X_pow_sub_C_hasseInvPoly (hp : 5 ≤ p) (hP : Irreducible P)
    (hPA : P ∣ hasseInvPoly hp) (hπ2 : ¬P * P ∣ hasseInvPoly hp) :
    Irreducible (X ^ (p - 1) - C (hasseInvPoly hp)) :=
  (isEisensteinAt_X_pow_sub_C_hasseInvPoly hp hP hPA hπ2).irreducible
    ((Ideal.span_singleton_prime hP.ne_zero).2
      (UniqueFactorizationMonoid.irreducible_iff_prime.1 hP))
    (monic_X_pow_sub_C _ (by lia)).isPrimitive  (by rw [natDegree_X_pow_sub_C]; lia)

/-! ### Irreducibility of `A - 1` -/

open MvPolynomial hiding C X coeff monomial

/-- A weighted homogenization of positive degree, of a polynomial with nonzero constant
coefficient, is not a unit: its coefficient in that degree is the constant coefficient. -/
private theorem not_isUnit_weightedHomogenize (hN : 0 < N) (hP : constantCoeff P ≠ 0) :
    ¬IsUnit (weightedHomogenize E₄E₆Weights N P) := fun hunit ↦ by
  have hcoeff : (weightedHomogenize E₄E₆Weights N P).coeff N ≠ 0 := by
    simpa [constantCoeff_eq] using hP
  grind [natDegree_eq_zero_of_isUnit, le_natDegree_of_ne_zero hcoeff]

/-- A factor of the Hasse invariant minus one is nonzero in weight `0`, and its maximal weight is
positive unless it is a unit. -/
private theorem natDegree_toWeightPolynomial_pos (hP0 : P ≠ 0) (hPu : ¬IsUnit P) :
    0 < (toWeightPolynomial E₄E₆Weights P).natDegree := by
  rcases Nat.eq_zero_or_pos (toWeightPolynomial E₄E₆Weights P).natDegree with h | h
  · refine absurd ((h ▸ isWeightedHomogeneous_natDegree ?_).isUnit_of_ne_zero
      E₄E₆Weights_ne_zero hP0) hPu
    grind [natTrailingDegree_le_natDegree (toWeightPolynomial E₄E₆Weights P)]
  · exact h

/-- **The Hasse invariant minus one is irreducible.** A factorization `A - 1 = F * G` homogenizes,
in the maximal weights `r` and `s` of `F` and `G`, to a factorization of `A - T ^ (p - 1)`; both
homogenizations have positive degree because `F` and `G` have nonzero constant coefficients, and
this contradicts the irreducibility of `T ^ (p - 1) - A`. -/
theorem irreducible_hasseInvPoly_sub_one (hp : 5 ≤ p) : Irreducible (hasseInvPoly hp - 1) := by
  obtain ⟨P, hP, hPA, hP2⟩ := exists_irreducible_dvd_hasseInvPoly hp
  have hAhom := hasseInvPoly_isWeightedHomogeneous hp
  have hTP : toWeightPolynomial E₄E₆Weights (hasseInvPoly hp - 1) =
      monomial (p - 1) (hasseInvPoly hp) - 1 := by simp [toWeightPolynomial_eq_monomial_iff.2 hAhom]
  have hdeg : (toWeightPolynomial E₄E₆Weights (hasseInvPoly hp - 1)).natDegree = p - 1 := by
    grind [natDegree_sub_eq_left_of_natDegree_lt, natDegree_monomial_eq _ (hasseInvPoly_ne_zero hp),
      natDegree_monomial_eq _ (hasseInvPoly_ne_zero hp), natDegree_one]
  have hA1 : hasseInvPoly hp - 1 ≠ 0 := by grind
  refine ⟨fun hunit ↦ ?_, fun F G hFG ↦ ?_⟩
  · grind [natDegree_eq_zero_of_isUnit (hunit.map (toWeightPolynomial E₄E₆Weights))]
  by_contra! hcon
  set r := (toWeightPolynomial E₄E₆Weights F).natDegree with hr
  set s := (toWeightPolynomial E₄E₆Weights G).natDegree with hs
  suffices X ^ (p - 1) - C (hasseInvPoly hp) =
      (-weightedHomogenize E₄E₆Weights r F) * weightedHomogenize E₄E₆Weights s G by
    have hconst : constantCoeff F * constantCoeff G = -1 := by rw [← map_mul, ← hFG, map_sub,
      map_one, constantCoeff_eq, hAhom.coeff_eq_zero 0 (by grind), zero_sub]
    rcases (irreducible_X_pow_sub_C_hasseInvPoly hp hP hPA hP2).isUnit_or_isUnit this with h | h
    · exact not_isUnit_weightedHomogenize (natDegree_toWeightPolynomial_pos (by grind) hcon.1)
        (fun h0 ↦ by simp [h0] at hconst) ((IsUnit.neg_iff _).mp h)
    · exact not_isUnit_weightedHomogenize (natDegree_toWeightPolynomial_pos (by grind) hcon.2)
        (fun h0 ↦ by simp [h0] at hconst) h
  suffices weightedHomogenize E₄E₆Weights r F * weightedHomogenize E₄E₆Weights s G =
      C (hasseInvPoly hp) - X ^ (p - 1) by
    grind
  have hrs : r + s = p - 1 := by rw [hr, hs, ← natDegree_mul (toWeightPolynomial_ne_zero _
    (by grind)) (toWeightPolynomial_ne_zero _ (by grind)), ← map_mul, ← hFG, hdeg]
  rw [← weightedHomogenize_mul le_rfl le_rfl, hrs, ← hFG, map_sub,
    weightedHomogenize_of_isWeightedHomogeneous hAhom le_rfl, weightedHomogenize_one,
    Nat.sub_self, pow_zero, mul_one]

/-! ### The coefficient of `q` in the evaluation of `X₀³ - X₁²` -/

/-- The coefficient of `q` in `evalE₄E₆ModP (X₀³ - X₁²) = E₄³ - E₆² = 1728 Δ` is `1728`, which is
nonzero modulo `p` because `p ≥ 5`. -/
theorem coeff_one_evalE₄E₆ModP_X_zero_pow_three_sub_X_one_sq (hp : 5 ≤ p) :
    PowerSeries.coeff 1 (evalE₄E₆ModP
      ((MvPolynomial.X 0) ^ 3 - MvPolynomial.X 1 ^ 2)) = (1728 : ZMod p) := by
  suffices EisensteinSeries.E₄ModP ^ 3 - EisensteinSeries.E₆ModP ^ 2 =
      PowerSeries.map (pLocalInt.toZMod (p := p))
        (EisensteinSeries.E₄_int ^ 3 - EisensteinSeries.E₆_int ^ 2) by
    simp [evalE₄E₆ModP_X_zero_pow_three_sub_X_one_sq, this, ← smul_discriminant_int hp,
    coeff_discriminant_int_one hp, smul_eq_mul, map_ofNat]
  simp [EisensteinSeries.E₄ModP, EisensteinSeries.E₆ModP]

end ModularForm
