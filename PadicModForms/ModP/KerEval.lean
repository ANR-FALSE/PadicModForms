/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ModP.Squarefree
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

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

variable {p : ℕ} [Fact p.Prime] {π : MvPolynomial (Fin 2) (ZMod p)}

/-! ### An irreducible factor of the Hasse invariant -/

/-- The Hasse invariant, being neither zero nor a unit, has an irreducible factor `π`; since it is
squarefree, `π * π` does not divide it. -/
theorem exists_irreducible_dvd_hasseInvPoly (hp : 5 ≤ p) :
    ∃ π : MvPolynomial (Fin 2) (ZMod p),
      Irreducible π ∧ π ∣ hasseInvPoly hp ∧ ¬π * π ∣ hasseInvPoly hp := by
  obtain ⟨π, hπ, hπA⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_hasseInvPoly hp) (hasseInvPoly_ne_zero hp)
  exact ⟨π, hπ, hπA, fun h ↦ hπ.not_isUnit (hasseInvPoly_squarefree hp π h)⟩

/-! ### Eisenstein's criterion for `T ^ (p - 1) - A` -/

/-- `T ^ (p - 1) - A` is Eisenstein at an irreducible factor `π` of the Hasse invariant `A`: it is
monic, its intermediate coefficients vanish, and its constant coefficient `-A` is divisible by `π`
but not by `π ^ 2`. -/
theorem isEisensteinAt_X_pow_sub_C_hasseInvPoly (hp : 5 ≤ p) (hπ : Irreducible π)
    (hπA : π ∣ hasseInvPoly hp) (hπ2 : ¬π * π ∣ hasseInvPoly hp) :
    (X ^ (p - 1) - C (hasseInvPoly hp)).IsEisensteinAt (Ideal.span {π}) where
  leading := by
    rw [(monic_X_pow_sub_C _ (by lia)).leadingCoeff, Ideal.mem_span_singleton]
    exact fun h ↦ hπ.not_isUnit (isUnit_of_dvd_one h)
  mem {n} hn := by
    rw [natDegree_X_pow_sub_C] at hn
    rw [coeff_sub, coeff_X_pow, if_neg (by lia), coeff_C, Ideal.mem_span_singleton]
    split_ifs <;> simp_all
  notMem := by
    rw [coeff_sub, coeff_X_pow, if_neg (by lia), coeff_C_zero, zero_sub,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact fun h ↦ hπ2 (by rwa [← dvd_neg, ← pow_two])

/-- **Eisenstein's criterion**: `T ^ (p - 1) - A` is irreducible in `(ZMod p)[X₀, X₁][T]`. -/
theorem irreducible_X_pow_sub_C_hasseInvPoly (hp : 5 ≤ p) (hπ : Irreducible π)
    (hπA : π ∣ hasseInvPoly hp) (hπ2 : ¬π * π ∣ hasseInvPoly hp) :
    Irreducible ((X : Polynomial (MvPolynomial (Fin 2) (ZMod p))) ^ (p - 1) -
      C (hasseInvPoly hp)) :=
  (isEisensteinAt_X_pow_sub_C_hasseInvPoly hp hπ hπA hπ2).irreducible
    ((Ideal.span_singleton_prime hπ.ne_zero).2
      (UniqueFactorizationMonoid.irreducible_iff_prime.1 hπ))
    (monic_X_pow_sub_C _ (by lia)).isPrimitive  (by rw [natDegree_X_pow_sub_C]; lia)

end ModularForm
