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

/-- A weighted homogeneous polynomial divisible by `hasseInvPoly hp - 1` vanishes: its evaluation
is `0`, and evaluation is injective in each fixed weight (`eq_of_evalE₄E₆ModP_eq`). -/
theorem eq_zero_of_isWeightedHomogeneous_of_hasseInvPoly_sub_one_dvd (hp : 5 ≤ p)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) (hdvd : hasseInvPoly hp - 1 ∣ F) : F = 0 := by
  obtain ⟨G, rfl⟩ := hdvd
  exact eq_of_evalE₄E₆ModP_eq hp hF (isWeightedHomogeneous_zero ..)
    (by simp [evalE₄E₆ModP_hasseInvPoly hp])

/-- Two weighted homogeneous polynomials with the same evaluation at `E₄` and `E₆` modulo `p` and
weights differing by `t * (p - 1)` differ exactly by the factor `hasseInvPoly hp ^ t`: multiplying
the lighter one by `hasseInvPoly hp ^ t` gives a polynomial of the same weight and the same
evaluation as the heavier one, and evaluation is injective in a fixed weight. -/
theorem eq_hasseInvPoly_pow_mul_of_evalE₄E₆ModP_eq (hp : 5 ≤ p) {t : ℕ}
    (hF : IsWeightedHomogeneous E₄E₆Weights F (n + t * (p - 1)))
    (hG : IsWeightedHomogeneous E₄E₆Weights G n)
    (h : evalE₄E₆ModP F = evalE₄E₆ModP G) : F = hasseInvPoly hp ^ t * G :=
  eq_of_evalE₄E₆ModP_eq hp hF (isWeightedHomogeneous_hasseInvPoly_pow_mul hp hG t)
    (by rw [h, evalE₄E₆ModP_hasseInvPoly_pow_mul])

/-- A nonzero weighted homogeneous polynomial has nonzero evaluation, evaluation being injective in
a fixed weight; in particular this holds when it is not divisible by the Hasse invariant. -/
theorem evalE₄E₆ModP_ne_zero_of_not_dvd (hp : 5 ≤ p)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) (hA : ¬hasseInvPoly hp ∣ F) :
    evalE₄E₆ModP F ≠ 0 := fun h ↦
  hA (eq_of_evalE₄E₆ModP_eq hp hF (isWeightedHomogeneous_zero ..) (by rw [h, map_zero]) ▸
    dvd_zero _)

/-! ### The filtration -/

/-- The filtration of a mod-`p` modular form: the least weight of a weighted homogeneous
polynomial in `E₄`, `E₆` evaluating to it. By the `Nat.sInf` convention it takes the junk value
`0` on power series that are not modular forms of any single weight, and the value `0` on `0`. -/
def modPFiltration (p : ℕ) [Fact p.Prime] (f : (ZMod p)⟦X⟧) : ℕ :=
  sInf {n | ∃ F, IsWeightedHomogeneous E₄E₆Weights F n ∧ evalE₄E₆ModP F = f}

/-- The filtration is the infimum of the weights of the weighted homogeneous representatives. -/
theorem modPFiltration_def (p : ℕ) [Fact p.Prime] (f : (ZMod p)⟦X⟧) : modPFiltration p f =
    sInf {n | ∃ F, IsWeightedHomogeneous E₄E₆Weights F n ∧ evalE₄E₆ModP F = f} := rfl

@[simp]
theorem modPFiltration_zero : modPFiltration p (0 : (ZMod p)⟦X⟧) = 0 :=
  Nat.sInf_eq_zero.2 (Or.inl ⟨0, isWeightedHomogeneous_zero .., map_zero _⟩)

theorem modPFiltration_le (hF : IsWeightedHomogeneous E₄E₆Weights F n) :
    modPFiltration p (evalE₄E₆ModP F) ≤ n :=
  Nat.sInf_le ⟨F, hF, rfl⟩

/-- A mod-`p` modular form has a homogeneous representative of weight its filtration. -/
theorem exists_isWeightedHomogeneous_modPFiltration (hF : IsWeightedHomogeneous E₄E₆Weights F n) :
    ∃ G, IsWeightedHomogeneous E₄E₆Weights G (modPFiltration p (evalE₄E₆ModP F)) ∧
      evalE₄E₆ModP G = evalE₄E₆ModP F :=
  Nat.sInf_mem (s := {m | ∃ G, IsWeightedHomogeneous E₄E₆Weights G m ∧
    evalE₄E₆ModP G = evalE₄E₆ModP F}) ⟨n, F, hF, rfl⟩

/-- The filtration is invariant under multiplication by a nonzero scalar. -/
theorem modPFiltration_smul {f : (ZMod p)⟦X⟧} {c : ZMod p} (hc : c ≠ 0) :
    modPFiltration p (c • f) = modPFiltration p f := by
  rw [modPFiltration_def, modPFiltration_def]
  congr 1
  ext m
  constructor
  · rintro ⟨F, hF, hFf⟩
    exact ⟨c⁻¹ • F, (weightedHomogeneousSubmodule _ _ _).smul_mem _ hF,
      by rw [map_smul, hFf, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  · rintro ⟨F, hF, hFf⟩
    exact ⟨c • F, (weightedHomogeneousSubmodule _ _ _).smul_mem _ hF, by rw [map_smul, hFf]⟩

/-- A modular form of filtration `0` is constant, the weights of `E₄` and `E₆` being positive. -/
theorem exists_C_of_modPFiltration_eq_zero (hF : IsWeightedHomogeneous E₄E₆Weights F n)
    (h : modPFiltration p (evalE₄E₆ModP F) = 0) : ∃ c, evalE₄E₆ModP F = PowerSeries.C c := by
  obtain ⟨G, hG, hGF⟩ := exists_isWeightedHomogeneous_modPFiltration hF
  rw [h] at hG
  refine ⟨G.coeff 0, ?_⟩
  rw [← hGF]
  conv_lhs => rw [hG.eq_C_coeff_zero E₄E₆Weights_ne_zero]
  simp [evalE₄E₆ModP, PowerSeries.C_eq_algebraMap]

/-! ### Reduced representatives -/

/-- **The reduced representative criterion**: a weighted homogeneous representative not divisible
by the Hasse invariant computes the filtration. A representative of smaller weight would, by the
`m = 1` congruence theorem and `eq_hasseInvPoly_pow_mul_of_evalE₄E₆ModP_eq`, exhibit `F` as a
multiple of `hasseInvPoly hp`. -/
theorem modPFiltration_eq_of_not_dvd (hp : 5 ≤ p)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) (hA : ¬hasseInvPoly hp ∣ F) :
    modPFiltration p (evalE₄E₆ModP F) = n := by
  obtain ⟨G, hG, hGF⟩ := exists_isWeightedHomogeneous_modPFiltration hF
  have hle := modPFiltration_le hF
  obtain ⟨t, ht⟩ : p - 1 ∣ n - modPFiltration p (evalE₄E₆ModP F) :=
    (ZMod.natCast_eq_zero_iff _ _).1 <| by
      rw [Nat.cast_sub hle, natCast_eq_of_evalE₄E₆ModP_eq hp hF hG hGF.symm
        (evalE₄E₆ModP_ne_zero_of_not_dvd hp hF hA), sub_self]
  rcases t with _ | t
  · lia
  · have hn : n = modPFiltration p (evalE₄E₆ModP F) + (t + 1) * (p - 1) := by rw [mul_comm]; lia
    exact absurd (eq_hasseInvPoly_pow_mul_of_evalE₄E₆ModP_eq hp (hn ▸ hF) hG hGF.symm ▸
      dvd_mul_of_dvd_left (dvd_pow_self _ t.succ_ne_zero) G) hA

/-- Every nonzero mod-`p` modular form has a *reduced* representative: weighted homogeneous of
weight the filtration and not divisible by the Hasse invariant. Dividing a representative of
minimal weight by the Hasse invariant would produce one of smaller weight. -/
theorem exists_isWeightedHomogeneous_not_dvd (hp : 5 ≤ p)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) (h0 : evalE₄E₆ModP F ≠ 0) :
    ∃ G, IsWeightedHomogeneous E₄E₆Weights G (modPFiltration p (evalE₄E₆ModP F)) ∧
      evalE₄E₆ModP G = evalE₄E₆ModP F ∧ ¬hasseInvPoly hp ∣ G := by
  obtain ⟨G, hG, hGF⟩ := exists_isWeightedHomogeneous_modPFiltration hF
  refine ⟨G, hG, hGF, fun ⟨H, hH⟩ ↦ ?_⟩
  have hHF : evalE₄E₆ModP H = evalE₄E₆ModP F := by
    rw [← hGF, hH, map_mul, evalE₄E₆ModP_hasseInvPoly hp, one_mul]
  have hH0 : H ≠ 0 := fun h ↦ h0 (by rw [← hHF, h, map_zero])
  obtain ⟨m, k, hm, hk, hmk⟩ := (hH ▸ hG).mul_factors (hasseInvPoly_ne_zero hp) hH0
  have hle := modPFiltration_le hk
  rw [hHF] at hle
  grind [hm.inj_right (hasseInvPoly_ne_zero hp) (hasseInvPoly_isWeightedHomogeneous hp)]

/-- The filtration of a nonzero form is congruent to the weight of any homogeneous representative
modulo `p - 1`. -/
theorem natCast_modPFiltration_eq (hp : 5 ≤ p) (hF : IsWeightedHomogeneous E₄E₆Weights F n)
    (h0 : evalE₄E₆ModP F ≠ 0) :
    (modPFiltration p (evalE₄E₆ModP F) : ZMod (p - 1)) = (n : ZMod (p - 1)) := by
  obtain ⟨G, hG, hGF⟩ := exists_isWeightedHomogeneous_modPFiltration hF
  exact natCast_eq_of_evalE₄E₆ModP_eq hp hG hF hGF (by rwa [hGF])

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
  obtain ⟨U, hU, hUF⟩ := exists_isWeightedHomogeneous_modPFiltration hF
  obtain ⟨V, hV, hVG, hVA⟩ := exists_isWeightedHomogeneous_not_dvd hp hG hG0
  obtain ⟨t, ht⟩ : p - 1 ∣ modPFiltration p (evalE₄E₆ModP G) - modPFiltration p (evalE₄E₆ModP F) :=
    (ZMod.natCast_eq_zero_iff _ _).1 <| by
      rw [Nat.cast_sub hlt.le, natCast_modPFiltration_eq hp hF hF0,
        natCast_modPFiltration_eq hp hG hG0, hnn', sub_self]
  have ht0 : t ≠ 0 := by
    intro rfl
    rw [mul_zero] at ht
    lia
  have hW : IsWeightedHomogeneous E₄E₆Weights (hasseInvPoly hp ^ t * U + V)
      (modPFiltration p (evalE₄E₆ModP G)) := by
    refine IsWeightedHomogeneous.add ?_ hV
    have := isWeightedHomogeneous_hasseInvPoly_pow_mul hp hU t
    rwa [show modPFiltration p (evalE₄E₆ModP F) + t * (p - 1) =
      modPFiltration p (evalE₄E₆ModP G) by rw [mul_comm]; lia] at this
  have hWA : ¬hasseInvPoly hp ∣ hasseInvPoly hp ^ t * U + V := fun h ↦
    hVA ((dvd_add_right (dvd_mul_of_dvd_left (dvd_pow_self _ ht0) _)).1 h)
  have key := modPFiltration_eq_of_not_dvd hp hW hWA
  rwa [map_add, evalE₄E₆ModP_hasseInvPoly_pow_mul, hUF, hVG] at key

/-- **The filtration is multiplied by `p` under Frobenius**: since the Hasse invariant is
squarefree, `A ∣ G ^ p` implies `A ∣ G` (`Squarefree.dvd_pow_iff_dvd`), so the `p`-th power of a
reduced representative stays reduced. -/
theorem modPFiltration_pow_prime (hp : 5 ≤ p) (hF : IsWeightedHomogeneous E₄E₆Weights F n)
    (h0 : evalE₄E₆ModP F ≠ 0) :
    modPFiltration p (evalE₄E₆ModP F ^ p) = p * modPFiltration p (evalE₄E₆ModP F) := by
  obtain ⟨U, hU, hUF, hUA⟩ := exists_isWeightedHomogeneous_not_dvd hp hF h0
  have key := modPFiltration_eq_of_not_dvd hp (hU.pow p) fun h ↦
    hUA (((hasseInvPoly_squarefree hp).dvd_pow_iff_dvd (Fact.out : p.Prime).ne_zero).1 h)
  rwa [map_pow, hUF, smul_eq_mul] at key

end ModularForm
