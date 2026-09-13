/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

import PadicModForms.ForMathlib.RationalRoot
public import PadicModForms.ModP.Graded
import PadicModForms.ForMathlib.WeightedHomogeneous
import PadicModForms.ModP.Hasse

/-!
# The degree-zero mod-`p` modular forms and their normality

Let `p ≥ 5`. The algebra of mod-`p` modular forms of all weights is graded by `ZMod (p - 1)`,
because multiplication by the Hasse invariant `A = hasseInvPoly hp` identifies the weights `k` and
`k + (p - 1)`. This file defines its degree-zero part `modPWeightZeroForms p`, Serre's `𝓜⁰`: the
evaluations at `E₄`, `E₆` of polynomials supported in weights divisible by `p - 1`.

The structural fact needed for Serre's congruence theorem is the normality of `𝓜⁰`, in the form
`ModularForm.mem_modPWeightZeroForms_of_isIntegral`: a power series `f` with `w * f = u`, for
degree-zero forms `u` and `w ≠ 0`, which is integral over the degree-zero forms, is itself a
degree-zero form.

Serre deduces this from the smoothness of the modular curve. We instead reduce it to the integral
root theorem in `(ZMod p)[X₀, X₁]`, which is a unique factorization domain. Choose weighted
homogeneous representatives `U` of `u` and `W` of `w`, and representatives of the coefficients of a
monic equation of degree `d` for `f` over `𝓜⁰`. Multiplying each of them by a power of the Hasse
invariant `A` raises weights without changing evaluations, so one may arrange that all the terms of
the induced equation carry the same weight `d * a`. That equation evaluates to `w ^ d * P(f) = 0`,
hence holds in `(ZMod p)[X₀, X₁]`, evaluation being injective in a fixed weight. It says exactly
that `U / W` is a root of a monic polynomial, so `W ∣ U`, and the quotient is a weighted homogeneous
representative of `f` whose weight is divisible by `p - 1`.

This replaces the route through the degree-zero part of the localization `(ZMod p)[X₀, X₁][A⁻¹]`,
which needs the normality of a homogeneous localization and the fraction field of `𝓜⁰`; neither is
used here.

## Main definitions

* `modPWeightZeroForms`: the degree-zero mod-`p` modular forms, as a subalgebra of `(ZMod p)⟦X⟧`.

## Main results

* `ModularForm.exists_isWeightedHomogeneous_of_mem_modPWeightZeroForms`: a degree-zero form is
  the evaluation of a single homogeneous polynomial of weight divisible by `p - 1`.
* `ModularForm.mem_modPWeightZeroForms_of_isIntegral`: normality of `𝓜⁰`.
-/

@[expose] public noncomputable section

open MvPolynomial
open PowerSeries hiding C X

variable {p n : ℕ} [Fact p.Prime] {F : MvPolynomial (Fin 2) (ZMod p)} {f : (ZMod p)⟦X⟧}

/-- The mod-`p` modular forms of degree zero: evaluations at `E₄`, `E₆` of polynomials that are
weighted homogeneous of degree `0` for the grading by `ZMod (p - 1)`, that is, supported in
weights divisible by `p - 1`. This is Serre's `𝓜⁰`. -/
def modPWeightZeroForms (p : ℕ) [Fact p.Prime] : Subalgebra (ZMod p) (ZMod p)⟦X⟧ where
  carrier := {f | ∃ F, IsWeightedHomogeneous (ModularForm.E₄E₆WeightsModPSubOne p) F 0 ∧
    ModularForm.evalE₄E₆ModP F = f}
  mul_mem' := fun ⟨F, hF, hFf⟩ ⟨G, hG, hGg⟩ ↦
    ⟨F * G, by simpa using hF.mul hG, by rw [map_mul, hFf, hGg]⟩
  one_mem' := ⟨1, isWeightedHomogeneous_one _ _, map_one _⟩
  add_mem' := fun ⟨F, hF, hFf⟩ ⟨G, hG, hGg⟩ ↦ ⟨F + G, hF.add hG, by rw [map_add, hFf, hGg]⟩
  zero_mem' := ⟨0, isWeightedHomogeneous_zero .., map_zero _⟩
  algebraMap_mem' c := ⟨C c, isWeightedHomogeneous_C _ c, aeval_C _ c⟩

@[simp]
theorem mem_modPWeightZeroForms : f ∈ modPWeightZeroForms p ↔
    ∃ F, IsWeightedHomogeneous (ModularForm.E₄E₆WeightsModPSubOne p) F 0 ∧
      ModularForm.evalE₄E₆ModP F = f :=
  .rfl

namespace ModularForm

/-! ### Membership -/

/-- The evaluation of a weighted homogeneous polynomial of weight divisible by `p - 1` has degree
zero. -/
theorem mem_modPWeightZeroForms_of_isWeightedHomogeneous (hn : p - 1 ∣ n)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) :
    evalE₄E₆ModP F ∈ modPWeightZeroForms p := by
  have := isWeightedHomogeneous_modPSubOne hF
  rw [(ZMod.natCast_eq_zero_iff n (p - 1)).2 hn] at this
  exact ⟨F, this, rfl⟩

/-- A mod-`p` modular form of weight divisible by `p - 1` has degree zero. -/
theorem mem_modPWeightZeroForms_of_mem_modPModularForms (hp : 5 ≤ p) (hn : p - 1 ∣ n)
    (hf : f ∈ modPModularForms p n) : f ∈ modPWeightZeroForms p := by
  obtain ⟨F, hF, rfl⟩ := exists_isWeightedHomogeneous_of_mem_modPModularForms hp hf
  exact mem_modPWeightZeroForms_of_isWeightedHomogeneous hn hF

/-- A degree-zero form is the evaluation of a *single-weight* homogeneous polynomial, of weight
divisible by `p - 1`: multiply each monomial by a power of the Hasse invariant, raising it to the
sum of the weights of the monomials. -/
theorem exists_isWeightedHomogeneous_of_mem_modPWeightZeroForms (hp : 5 ≤ p)
    (hf : f ∈ modPWeightZeroForms p) : ∃ n F, p - 1 ∣ n ∧
      IsWeightedHomogeneous E₄E₆Weights F n ∧ evalE₄E₆ModP F = f := by
  obtain ⟨F, hF, rfl⟩ := hf
  have hw : ∀ d ∈ F.support, p - 1 ∣ Finsupp.weight E₄E₆Weights d := fun d hd ↦
    (ZMod.natCast_eq_zero_iff _ _).1
      (by rw [← weight_E₄E₆WeightsModPSubOne]; exact hF (mem_support_iff.1 hd))
  set N := ∑ d ∈ F.support, Finsupp.weight E₄E₆Weights d
  refine ⟨N, ∑ d ∈ F.support, hasseInvPoly hp ^ ((N - Finsupp.weight E₄E₆Weights d) / (p - 1)) *
    monomial d (F.coeff d), Finset.dvd_sum hw, IsWeightedHomogeneous.sum _ _ _ fun d hd ↦ ?_, ?_⟩
  · have := isWeightedHomogeneous_hasseInvPoly_pow_mul hp (isWeightedHomogeneous_monomial _ d
      (F.coeff d) rfl) ((N - Finsupp.weight E₄E₆Weights d) / (p - 1))
    rwa [Nat.div_mul_cancel (Nat.dvd_sub (Finset.dvd_sum hw) (hw d hd)),
      Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hd)] at this
  · simp only [map_sum, evalE₄E₆ModP_hasseInvPoly_pow_mul]
    rw [← map_sum, support_sum_monomial_coeff]

/-! ### Normality -/

section Normality

/-- The monic polynomial `T ^ d + ∑ i < d, c i T ^ i` over `(ZMod p)[X₀, X₁]`, with prescribed
coefficients below the leading one. -/
private def monicOfCoeffs (d : ℕ) (c : ℕ → MvPolynomial (Fin 2) (ZMod p)) :
    Polynomial (MvPolynomial (Fin 2) (ZMod p)) :=
  Polynomial.X ^ d + ∑ i ∈ Finset.range d, Polynomial.C (c i) * Polynomial.X ^ i

private theorem degree_lt_of_monicOfCoeffs (d : ℕ) (c : ℕ → MvPolynomial (Fin 2) (ZMod p)) :
    (∑ i ∈ Finset.range d, Polynomial.C (c i) * Polynomial.X ^ i).degree < (d : WithBot ℕ) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Polynomial.degree_sum_fin_lt _

private theorem monicOfCoeffs_monic (d : ℕ) (c : ℕ → MvPolynomial (Fin 2) (ZMod p)) :
    (monicOfCoeffs d c).Monic :=
  Polynomial.monic_X_pow_add (degree_lt_of_monicOfCoeffs d c)

@[simp]
private theorem natDegree_monicOfCoeffs (d : ℕ) (c : ℕ → MvPolynomial (Fin 2) (ZMod p)) :
    (monicOfCoeffs d c).natDegree = d := by
  rw [monicOfCoeffs, Polynomial.natDegree_add_eq_left_of_degree_lt
    (by rw [Polynomial.degree_X_pow]; exact degree_lt_of_monicOfCoeffs d c),
    Polynomial.natDegree_X_pow]

private theorem coeff_monicOfCoeffs_of_lt (d : ℕ) (c : ℕ → MvPolynomial (Fin 2) (ZMod p)) {i : ℕ}
    (hi : i < d) : (monicOfCoeffs d c).coeff i = c i := by
  rw [monicOfCoeffs, Polynomial.coeff_add, Polynomial.coeff_X_pow, ite_eq_right hi.ne,
    Polynomial.finsetSum_coeff, zero_add,
    Finset.sum_eq_single i
      (fun j _ hj ↦ by rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right (Ne.symm hj)])
      (fun h ↦ absurd (Finset.mem_range.2 hi) h),
    Polynomial.coeff_C_mul_X_pow, ite_eq_left rfl]

private theorem coeff_monicOfCoeffs_self (d : ℕ) (c : ℕ → MvPolynomial (Fin 2) (ZMod p)) :
    (monicOfCoeffs d c).coeff d = 1 := by
  have := (monicOfCoeffs_monic d c).coeff_natDegree
  rwa [natDegree_monicOfCoeffs] at this

/-- If the prescribed coefficients evaluate to those of a monic polynomial `P` over `𝓜⁰` of degree
`d` that kills `f`, then `monicOfCoeffs d c` evaluated at `f` vanishes too. -/
private theorem eval₂_monicOfCoeffs_eq_zero {d : ℕ} {c : ℕ → MvPolynomial (Fin 2) (ZMod p)}
    {P : Polynomial (modPWeightZeroForms p)} (hP : P.Monic) (hd : P.natDegree = d)
    (hPf : Polynomial.aeval f P = 0)
    (hc : ∀ i < d, evalE₄E₆ModP.toRingHom (c i) =
      algebraMap (modPWeightZeroForms p) (ZMod p)⟦X⟧ (P.coeff i)) :
    Polynomial.eval₂ evalE₄E₆ModP.toRingHom f (monicOfCoeffs d c) = 0 := by
  have hmap : (monicOfCoeffs d c).map evalE₄E₆ModP.toRingHom =
      P.map (algebraMap (modPWeightZeroForms p) (ZMod p)⟦X⟧) := by
    refine Polynomial.ext fun i ↦ ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    rcases lt_trichotomy i d with hi | hi | hi
    · rw [coeff_monicOfCoeffs_of_lt d c hi]
      exact hc i hi
    · have hPd : P.coeff d = 1 := by rw [← hd]; exact hP.coeff_natDegree
      rw [hi, coeff_monicOfCoeffs_self, hPd, map_one, map_one]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_monicOfCoeffs]; exact hi),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hi), map_zero, map_zero]
  rw [Polynomial.eval₂_eq_eval_map, hmap, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def,
    hPf]

/-- The polynomial `(monicOfCoeffs d c).scaleRoots W` evaluated at `U` — whose vanishing says that
`U / W` is a root of `monicOfCoeffs d c` — is weighted homogeneous of weight `d * a`, as soon as
each term `c i * W ^ (d - i) * U ^ i` has that weight. -/
private theorem isWeightedHomogeneous_eval_scaleRoots {d : ℕ}
    {c : ℕ → MvPolynomial (Fin 2) (ZMod p)} {U W : MvPolynomial (Fin 2) (ZMod p)} {a b : ℕ}
    (hU : IsWeightedHomogeneous E₄E₆Weights U a) (hW : IsWeightedHomogeneous E₄E₆Weights W b)
    (m : ℕ → ℕ) (hc : ∀ i < d, IsWeightedHomogeneous E₄E₆Weights (c i) (m i))
    (hm : ∀ i < d, m i + (d - i) * b + i * a = d * a) :
    IsWeightedHomogeneous E₄E₆Weights
      (Polynomial.eval U ((monicOfCoeffs d c).scaleRoots W)) (d * a) := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.natDegree_scaleRoots, natDegree_monicOfCoeffs]
  refine IsWeightedHomogeneous.sum _ _ _ fun i hi ↦ ?_
  rw [Polynomial.coeff_scaleRoots, natDegree_monicOfCoeffs]
  rcases (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).lt_or_eq with hi' | hi'
  · rw [coeff_monicOfCoeffs_of_lt d c hi']
    have := ((hc i hi').mul (hW.pow (d - i))).mul (hU.pow i)
    rwa [smul_eq_mul, smul_eq_mul, hm i hi'] at this
  · rw [hi', coeff_monicOfCoeffs_self, Nat.sub_self, pow_zero, one_mul, one_mul]
    have := hU.pow d
    rwa [smul_eq_mul] at this

/-- **The working form of normality**: a power series that is a quotient `f = u / w` of two
degree-zero forms and is integral over the degree-zero forms is itself a degree-zero form. This is
the only consequence of normality used in Serre's congruence theorem.

The proof is the integral root theorem in the unique factorization domain `(ZMod p)[X₀, X₁]`.
Choose homogeneous representatives `W` of `w` and `U` of `u`, multiplying `U` by a power of the
Hasse invariant so that its weight `a` dominates, and homogeneous representatives `C i` of the
coefficients of a monic equation `P` of degree `d` for `f` over `𝓜⁰`. Multiplying each `C i` in
turn by a power of the Hasse invariant produces a monic polynomial `R = monicOfCoeffs d c` over
`(ZMod p)[X₀, X₁]` whose coefficients still evaluate to those of `P`, and for which every term of
`R.scaleRoots W` evaluated at `U` is weighted homogeneous of weight `d * a`. That element evaluates
to `w ^ d * P(f) = 0`, hence vanishes, evaluation being injective in each fixed weight. So `U / W`
is a root of the monic polynomial `R`, whence `W ∣ U`, and the quotient `V` is a homogeneous
representative of `f` whose weight `a - b` is divisible by `p - 1`. -/
theorem mem_modPWeightZeroForms_of_isIntegral (hp : 5 ≤ p) {f u w : (ZMod p)⟦X⟧}
    (hu : u ∈ modPWeightZeroForms p) (hw : w ∈ modPWeightZeroForms p) (hw0 : w ≠ 0)
    (hf : w * f = u) (hint : IsIntegral (modPWeightZeroForms p) f) :
    f ∈ modPWeightZeroForms p := by
  obtain ⟨P, hP, hPf⟩ := hint
  obtain ⟨d, hd⟩ : ∃ d, P.natDegree = d := ⟨_, rfl⟩
  choose N C hN hC hCP using fun i ↦
    exists_isWeightedHomogeneous_of_mem_modPWeightZeroForms hp (P.coeff i).2
  obtain ⟨b, W, hb, hW, hWw⟩ := exists_isWeightedHomogeneous_of_mem_modPWeightZeroForms hp hw
  obtain ⟨a₀, U₀, ha₀, hU₀, hU₀u⟩ := exists_isWeightedHomogeneous_of_mem_modPWeightZeroForms hp hu
  have hp1 : 1 ≤ p - 1 := by lia
  -- Raise the weight `a` of the representative of `u` above `b + N i` for every `i < d`.
  obtain ⟨t, ht⟩ : ∃ t, t = b + ∑ i ∈ Finset.range d, N i := ⟨_, rfl⟩
  obtain ⟨a, ha_def⟩ : ∃ a, a = a₀ + t * (p - 1) := ⟨_, rfl⟩
  obtain ⟨U, hU_def⟩ : ∃ U, U = hasseInvPoly hp ^ t * U₀ := ⟨_, rfl⟩
  have hU : IsWeightedHomogeneous E₄E₆Weights U a := by
    rw [hU_def, ha_def]; exact isWeightedHomogeneous_hasseInvPoly_pow_mul hp hU₀ t
  have hUu : evalE₄E₆ModP U = u := by
    rw [hU_def, evalE₄E₆ModP_hasseInvPoly_pow_mul, hU₀u]
  have ha : p - 1 ∣ a := by rw [ha_def]; exact dvd_add ha₀ (dvd_mul_left _ _)
  have hle : ∀ i < d, N i + (d - i) * b + i * a ≤ d * a := fun i hi ↦ by
    have h1 : N i + b ≤ a := by
      have hsum := Finset.single_le_sum (f := N) (fun j _ ↦ Nat.zero_le (N j))
        (Finset.mem_range.2 hi)
      have h2 : t ≤ t * (p - 1) := Nat.le_mul_of_pos_right _ hp1
      lia
    have h3 : 1 ≤ d - i := by lia
    calc N i + (d - i) * b + i * a ≤ (d - i) * (N i + b) + i * a := by nlinarith
      _ ≤ (d - i) * a + i * a := by nlinarith
      _ = d * a := by rw [← add_mul, Nat.sub_add_cancel hi.le]
  -- The coefficients raised to a common weight, and the monic polynomial they define.
  obtain ⟨c, hc_def⟩ : ∃ c : ℕ → MvPolynomial (Fin 2) (ZMod p), ∀ i, c i =
      hasseInvPoly hp ^ ((d * a - (N i + (d - i) * b + i * a)) / (p - 1)) * C i :=
    ⟨_, fun _ ↦ rfl⟩
  have hc : ∀ i < d, IsWeightedHomogeneous E₄E₆Weights (c i) (d * a - (d - i) * b - i * a) := by
    intro i hi
    have hdvd : p - 1 ∣ d * a - (N i + (d - i) * b + i * a) :=
      Nat.dvd_sub (dvd_mul_of_dvd_right ha _) (dvd_add (dvd_add (hN i)
        (dvd_mul_of_dvd_right hb _)) (dvd_mul_of_dvd_right ha _))
    have hhom := isWeightedHomogeneous_hasseInvPoly_pow_mul hp (hC i)
      ((d * a - (N i + (d - i) * b + i * a)) / (p - 1))
    rw [Nat.div_mul_cancel hdvd, show N i + (d * a - (N i + (d - i) * b + i * a)) =
      d * a - (d - i) * b - i * a by have := hle i hi; lia] at hhom
    rw [hc_def i]
    exact hhom
  have hm : ∀ i < d, (d * a - (d - i) * b - i * a) + (d - i) * b + i * a = d * a := fun i hi ↦ by
    have := hle i hi; lia
  have hcP : ∀ i < d, evalE₄E₆ModP.toRingHom (c i) =
      algebraMap (modPWeightZeroForms p) (ZMod p)⟦X⟧ (P.coeff i) := fun i _ ↦ by
    have h : evalE₄E₆ModP (c i) = (P.coeff i : (ZMod p)⟦X⟧) := by
      rw [hc_def i, evalE₄E₆ModP_hasseInvPoly_pow_mul, hCP i]
    exact h
  have hW0 : W ≠ 0 := fun h ↦ hw0 (by rw [← hWw, h, map_zero])
  -- `U / W` is a root of the monic polynomial `monicOfCoeffs d c`.
  have hroot : Polynomial.eval U ((monicOfCoeffs d c).scaleRoots W) = 0 := by
    refine eq_of_evalE₄E₆ModP_eq hp (isWeightedHomogeneous_eval_scaleRoots hU hW _ hc hm)
      (isWeightedHomogeneous_zero ..) ?_
    have hUW : evalE₄E₆ModP U = evalE₄E₆ModP W * f := by rw [hUu, hWw, hf]
    have hUW' : evalE₄E₆ModP.toRingHom U = evalE₄E₆ModP.toRingHom W * f := hUW
    have key : evalE₄E₆ModP.toRingHom
        (Polynomial.eval U ((monicOfCoeffs d c).scaleRoots W)) = 0 := by
      rw [← Polynomial.eval₂_at_apply, hUW', Polynomial.scaleRoots_eval₂_mul,
        eval₂_monicOfCoeffs_eq_zero hP hd hPf hcP, mul_zero]
    rw [map_zero]
    exact key
  -- Hence `W ∣ U`, and the quotient is a homogeneous representative of `f`.
  obtain ⟨V, hV⟩ := (monicOfCoeffs_monic d c).dvd_of_eval_scaleRoots_eq_zero hW0 hroot
  have hfV : f = evalE₄E₆ModP V := by
    apply mul_left_cancel₀ hw0
    rw [hf, ← hUu, hV, map_mul, hWw]
  rcases eq_or_ne V 0 with rfl | hV0
  · rw [hfV, map_zero]
    exact zero_mem _
  obtain ⟨m₁, k, hm₁, hk, hm₁k⟩ := (hV ▸ hU).mul_factors hW0 hV0
  rw [hm₁.inj_right hW0 hW] at hm₁k
  rw [← hm₁k] at ha
  rw [hfV]
  exact mem_modPWeightZeroForms_of_isWeightedHomogeneous ((Nat.dvd_add_right hb).1 ha) hk

end Normality

end ModularForm
