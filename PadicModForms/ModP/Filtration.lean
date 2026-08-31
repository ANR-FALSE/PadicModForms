/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ModP.Weights

/-!
# The filtration of mod-`p` modular forms

Let `p ≥ 5` and write `A = hasseInvPoly hp`, weighted homogeneous of weight `p - 1` with
`evalE₄E₆ModP A = 1`. The *filtration* of a mod-`p` modular form `f` is the least weight of a
weighted homogeneous polynomial in `E₄`, `E₆` evaluating to `f`.

Everything here reduces to divisibility by `A`. The starting point is that a weighted homogeneous
polynomial lying in the ideal `(A - 1)` vanishes, because multiplication by `A - 1` mixes distinct
weights; combined with Swinnerton-Dyer's kernel theorem this pins down all homogeneous
representatives of a given form (`eq_hasseInvPoly_pow_mul_of_evalE₄E₆ModP_eq`), and shows that a
representative computes the filtration exactly when it is not divisible by `A`
(`modPFiltration_eq_of_not_dvd`). Squarefreeness of `A` then gives the behaviour of the filtration
under Frobenius.

## Main definitions

* `ModularForm.modPFiltration`: the filtration, as a `Nat.sInf`.

## Main results

* `ModularForm.eq_zero_of_isWeightedHomogeneous_of_hasseInvPoly_sub_one_dvd`: homogeneous
  elements of `(A - 1)` vanish.
* `ModularForm.eq_hasseInvPoly_pow_mul_of_evalE₄E₆ModP_eq`: homogeneous representatives of the
  same form differ by a power of `A`.
* `ModularForm.modPFiltration_eq_of_not_dvd`, `ModularForm.exists_isWeightedHomogeneous_not_dvd`:
  the reduced representative criterion.
* `ModularForm.modPFiltration_add_of_lt`: forms of unequal filtrations do not cancel.
* `ModularForm.modPFiltration_pow_prime`: `fil (f ^ p) = p * fil f`.
-/

@[expose] public noncomputable section

open MvPolynomial
open PowerSeries hiding C X

namespace ModularForm

variable {p n n' : ℕ} [Fact p.Prime] {F G : MvPolynomial (Fin 2) (ZMod p)}

/-! ### Homogeneous elements and the ideal `(A - 1)` -/

/-- A weighted homogeneous polynomial divisible by `hasseInvPoly hp - 1` vanishes: writing
`F = (A - 1) * G` and comparing the weighted homogeneous components of least weight in `G` forces
every component of `G` to vanish. -/
theorem eq_zero_of_isWeightedHomogeneous_of_hasseInvPoly_sub_one_dvd (hp : 5 ≤ p)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) (hdvd : hasseInvPoly hp - 1 ∣ F) : F = 0 := by
  sorry

/-- Two weighted homogeneous polynomials with the same evaluation at `E₄` and `E₆` modulo `p` and
weights differing by `t * (p - 1)` differ exactly by the factor `hasseInvPoly hp ^ t`: their
difference, after padding by the Hasse invariant, is homogeneous and lies in the kernel of the
evaluation. -/
theorem eq_hasseInvPoly_pow_mul_of_evalE₄E₆ModP_eq (hp : 5 ≤ p) {t : ℕ}
    (hF : IsWeightedHomogeneous E₄E₆Weights F (n + t * (p - 1)))
    (hG : IsWeightedHomogeneous E₄E₆Weights G n)
    (h : evalE₄E₆ModP F = evalE₄E₆ModP G) : F = hasseInvPoly hp ^ t * G := by
  sorry

/-- A weighted homogeneous polynomial not divisible by the Hasse invariant has nonzero evaluation:
its evaluation vanishing would put it in `(A - 1)`, hence make it zero. -/
theorem evalE₄E₆ModP_ne_zero_of_not_dvd (hp : 5 ≤ p)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) (hA : ¬hasseInvPoly hp ∣ F) :
    evalE₄E₆ModP F ≠ 0 := by
  sorry

/-! ### The filtration -/

/-- The filtration of a mod-`p` modular form: the least weight of a weighted homogeneous
polynomial in `E₄`, `E₆` evaluating to it. By the `Nat.sInf` convention it takes the junk value
`0` on power series that are not modular forms of any single weight, and the value `0` on `0`. -/
def modPFiltration (p : ℕ) [Fact p.Prime] (f : (ZMod p)⟦X⟧) : ℕ :=
  sInf {n | ∃ F, IsWeightedHomogeneous E₄E₆Weights F n ∧ evalE₄E₆ModP F = f}

theorem modPFiltration_le (hF : IsWeightedHomogeneous E₄E₆Weights F n) :
    modPFiltration p (evalE₄E₆ModP F) ≤ n := by
  sorry

/-- A mod-`p` modular form has a homogeneous representative of weight its filtration. -/
theorem exists_isWeightedHomogeneous_modPFiltration (hF : IsWeightedHomogeneous E₄E₆Weights F n) :
    ∃ G, IsWeightedHomogeneous E₄E₆Weights G (modPFiltration p (evalE₄E₆ModP F)) ∧
      evalE₄E₆ModP G = evalE₄E₆ModP F := by
  sorry

/-- The filtration is invariant under multiplication by a nonzero scalar. -/
theorem modPFiltration_smul {f : (ZMod p)⟦X⟧} {c : ZMod p} (hc : c ≠ 0) :
    modPFiltration p (c • f) = modPFiltration p f := by
  sorry

/-- A modular form of filtration `0` is constant, the weights of `E₄` and `E₆` being positive. -/
theorem exists_C_of_modPFiltration_eq_zero (hF : IsWeightedHomogeneous E₄E₆Weights F n)
    (h : modPFiltration p (evalE₄E₆ModP F) = 0) : ∃ c, evalE₄E₆ModP F = PowerSeries.C c := by
  sorry

/-! ### Reduced representatives -/

/-- **The reduced representative criterion**: a weighted homogeneous representative not divisible
by the Hasse invariant computes the filtration. A representative of smaller weight would, by the
`m = 1` congruence theorem and `eq_hasseInvPoly_pow_mul_of_evalE₄E₆ModP_eq`, exhibit `F` as a
multiple of `hasseInvPoly hp`. -/
theorem modPFiltration_eq_of_not_dvd (hp : 5 ≤ p)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) (hA : ¬hasseInvPoly hp ∣ F) :
    modPFiltration p (evalE₄E₆ModP F) = n := by
  sorry

/-- Every nonzero mod-`p` modular form has a *reduced* representative: weighted homogeneous of
weight the filtration and not divisible by the Hasse invariant. -/
theorem exists_isWeightedHomogeneous_not_dvd (hp : 5 ≤ p)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) (h0 : evalE₄E₆ModP F ≠ 0) :
    ∃ G, IsWeightedHomogeneous E₄E₆Weights G (modPFiltration p (evalE₄E₆ModP F)) ∧
      evalE₄E₆ModP G = evalE₄E₆ModP F ∧ ¬hasseInvPoly hp ∣ G := by
  sorry

/-- The filtration of a nonzero form is congruent to the weight of any homogeneous representative
modulo `p - 1`. -/
theorem natCast_modPFiltration_eq (hp : 5 ≤ p) (hF : IsWeightedHomogeneous E₄E₆Weights F n)
    (h0 : evalE₄E₆ModP F ≠ 0) :
    (modPFiltration p (evalE₄E₆ModP F) : ZMod (p - 1)) = (n : ZMod (p - 1)) := by
  sorry

/-! ### Sums and Frobenius -/

/-- **Forms of unequal filtrations do not cancel**: for two nonzero forms of the same degree
modulo `p - 1`, if `fil u < fil v` then `fil (u + v) = fil v`. At the weight `fil v`, a
representative of `u + v` is the sum of a multiple of the Hasse invariant and a reduced
polynomial. -/
theorem modPFiltration_add_of_lt (hp : 5 ≤ p)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) (hG : IsWeightedHomogeneous E₄E₆Weights G n')
    (hF0 : evalE₄E₆ModP F ≠ 0) (hG0 : evalE₄E₆ModP G ≠ 0)
    (hnn' : (n : ZMod (p - 1)) = (n' : ZMod (p - 1)))
    (hlt : modPFiltration p (evalE₄E₆ModP F) < modPFiltration p (evalE₄E₆ModP G)) :
    modPFiltration p (evalE₄E₆ModP F + evalE₄E₆ModP G) =
      modPFiltration p (evalE₄E₆ModP G) := by
  sorry

/-- **The filtration is multiplied by `p` under Frobenius**: since the Hasse invariant is
squarefree, `A ∣ G ^ p` implies `A ∣ G` (`Squarefree.dvd_pow_iff_dvd`), so the `p`-th power of a
reduced representative stays reduced. -/
theorem modPFiltration_pow_prime (hp : 5 ≤ p) (hF : IsWeightedHomogeneous E₄E₆Weights F n)
    (h0 : evalE₄E₆ModP F ≠ 0) :
    modPFiltration p (evalE₄E₆ModP F ^ p) = p * modPFiltration p (evalE₄E₆ModP F) := by
  sorry

end ModularForm
