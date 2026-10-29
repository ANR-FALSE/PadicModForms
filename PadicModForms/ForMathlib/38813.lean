/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Groebner

/-!
# `E₄` and `E₆` are algebraically independent

This file backports the part of mathlib4 PR #38813 that has not landed yet: the evaluation
homomorphism `ModularForm.evalE₄E₆ : ℂ[X₀, X₁] →ₐ[ℂ] ⨁ k, ModularForm 𝒮ℒ k` of
`Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing` is injective. Its definition and its
surjectivity are already in mathlib. Delete this file once the PR lands.

## Main results

* `ModularForm.evalE₄E₆_injective`: `evalE₄E₆` is injective, i.e. `E₄` and `E₆` are
  algebraically independent (`ModularForm.algebraicIndependent_E₄_E₆`); in particular
  `⨁ k, ModularForm 𝒮ℒ k` is an integral domain.
* `ModularForm.mvPolynomialEquivModularForms`: the `ℂ`-algebra isomorphism
  `ℂ[X₀, X₁] ≃ₐ[ℂ] ⨁ k, ModularForm 𝒮ℒ k` given by `evalE₄E₆`.

## Implementation notes

Injectivity is proved one weight at a time. Since `E₄` and `E₆` have constant term `1`, the
constant term of the `q`-expansion of the image of a polynomial `p` is `p (1, 1)`. Let
`D = (X₀³ - X₁²) / 1728`, which maps to `Δ`. Division with remainder by `D` for the lexicographic
monomial order (`MonomialOrder.div_single`), in which the leading monomial of `D` is `X₀³`,
followed by taking weight-`k` components, writes a weighted-homogeneous polynomial `p` of weight
`k ≥ 12` as `r + D * s` with `r` and `s` weighted-homogeneous, where every monomial
`X₀ ^ a * X₁ ^ b` of `r` has `a < 3` (for `k < 12`, `p` itself has this property); so `r` is a
multiple of a single monomial. If `p` maps to zero, then `r (1, 1) = 0` because `D (1, 1) = 0`, so
`r = 0`; and then `Δ * evalE₄E₆ s = 0` gives `s = 0` by induction on the weight.

Three lemmas are not public in the PR and will need local copies in `PadicModForms.Rational.Graded`
once it lands: `evalE₄E₆_eq_aeval`, which is not in the PR at all (the body of `evalE₄E₆` is not
exposed outside its mathlib file), and `evalE₄E₆_eq_of_isWeightedHomogeneous` and
`evalE₄E₆_weightedHomogeneousComponent_apply`, which are private in the PR.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm ModularFormClass EisensteinSeries

open scoped MatrixGroups

namespace ModularForm

/-- `evalE₄E₆` is evaluation at `E₄` and `E₆`: the definition of `evalE₄E₆`, stated as an
equation because its body is not exposed outside its mathlib file. Not part of the PR. -/
theorem evalE₄E₆_eq_aeval : evalE₄E₆ =
    MvPolynomial.aeval ![DirectSum.of (ModularForm 𝒮ℒ) 4 E₄, DirectSum.of (ModularForm 𝒮ℒ) 6 E₆] :=
  MvPolynomial.algHom_ext fun i ↦ by fin_cases i <;> simp

/-! ### `E₄` and `E₆` are algebraically independent -/

private def discriminantPoly : MvPolynomial (Fin 2) ℂ :=
  (1 / 1728 : ℂ) • (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2)

private lemma evalE₄E₆_discriminantPoly : evalE₄E₆ discriminantPoly =
    DirectSum.of (ModularForm 𝒮ℒ) 12 CuspForm.discriminant := by
  simp [discriminantPoly, discriminant_eq_E₄_cube_sub_E₆_sq_graded]

private lemma weight_four_six_apply (d : Fin 2 →₀ ℕ) :
    Finsupp.weight (![4, 6] : Fin 2 → ℕ) d = d 0 * 4 + d 1 * 6 := by
  simp [Finsupp.weight_eq_sum]

private lemma eq_of_weight_eq_of_lt_three {d d' : Fin 2 →₀ ℕ} (hd : d 0 < 3) (hd' : d' 0 < 3)
    (h : Finsupp.weight (![4, 6] : Fin 2 → ℕ) d = Finsupp.weight ![4, 6] d') : d = d' := by
  rw [weight_four_six_apply, weight_four_six_apply] at h
  exact Finsupp.ext fun i ↦ by fin_cases i <;> lia

private lemma evalE₄E₆_monomial_apply_eq_zero_of_ne (d : Fin 2 →₀ ℕ) (c : ℂ) (k : ℤ)
    (hk : k ≠ d 0 * 4 + d 1 * 6) : evalE₄E₆ (MvPolynomial.monomial d c) k = 0 := by
  simp [MvPolynomial.monomial_fin_two, MvPolynomial.C_mul', DirectSum.ofPow, DirectSum.of_mul_of,
    DirectSum.smul_apply, DirectSum.of_eq_of_ne, hk]

/-- The image of a weighted homogeneous polynomial of weight `n` is concentrated in weight `n`. -/
lemma evalE₄E₆_eq_of_isWeightedHomogeneous {n : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n) :
    evalE₄E₆ p = DirectSum.of (ModularForm 𝒮ℒ) n (evalE₄E₆ p n) := by
  ext k : 1
  obtain rfl | hk := eq_or_ne k n
  · simp
  -- Every monomial of `p` has weight `n`, so its image vanishes in degree `k ≠ n`.
  rw [DirectSum.of_eq_of_ne _ _ _ hk, p.as_sum, map_sum, DirectSum.sum_apply]
  refine Finset.sum_eq_zero fun d hd ↦ evalE₄E₆_monomial_apply_eq_zero_of_ne _ _ _ ?_
  simpa [← hp (MvPolynomial.mem_support_iff.mp hd), weight_four_six_apply] using hk

/-- Taking the weight-`n` component of a polynomial does not change the weight-`n` component of
its image. -/
lemma evalE₄E₆_weightedHomogeneousComponent_apply (p : MvPolynomial (Fin 2) ℂ) (n : ℕ) :
    evalE₄E₆ (MvPolynomial.weightedHomogeneousComponent ![4, 6] n p) n = evalE₄E₆ p n := by
  -- Both sides are sums over the monomials of `p`; those of weight `≠ n` vanish in degree `n`.
  conv_rhs => rw [p.as_sum]
  simp only [MvPolynomial.weightedHomogeneousComponent_apply, map_sum, DirectSum.sum_apply]
  exact Finset.sum_filter_of_ne fun d _ ↦ Not.imp_symm fun h ↦
    evalE₄E₆_monomial_apply_eq_zero_of_ne _ _ _ <| by lia [weight_four_six_apply d]

private lemma discriminantPoly_isWeightedHomogeneous :
    discriminantPoly.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) 12 :=
  (MvPolynomial.weightedHomogeneousSubmodule ℂ _ 12).smul_mem _ <|
    ((MvPolynomial.isWeightedHomogeneous_X ℂ _ 0).pow 3).sub <|
      (MvPolynomial.isWeightedHomogeneous_X ℂ _ 1).pow 2

private lemma constantCoeff_qExpansionAlgHom_evalE₄E₆ (p : MvPolynomial (Fin 2) ℂ) :
    PowerSeries.constantCoeff (qExpansionAlgHom 1 one_pos one_mem_strictPeriods_SL (evalE₄E₆ p)) =
      MvPolynomial.eval 1 p := by
  -- Both sides are ring homomorphisms in `p`; on `X 0` and `X 1` they are `1`, since `E₄` and `E₆`
  -- have constant term `1`.
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    fin_cases i
    · simpa [hp] using congr(MvPolynomial.eval 1 p * $(E_qExpansion_coeff_zero _ ⟨2, rfl⟩))
    · simpa [hp] using congr(MvPolynomial.eval 1 p * $(E_qExpansion_coeff_zero _ ⟨3, rfl⟩))

attribute [local instance] MvPolynomial.weightedGradedAlgebra in
private lemma weightedHomogeneousComponent_mul_of_isWeightedHomogeneous_right {σ R : Type*}
    [CommSemiring R] {w : σ → ℕ} {i n : ℕ} {f q : MvPolynomial σ R}
    (hq : q.IsWeightedHomogeneous w i) (hin : i ≤ n) :
    MvPolynomial.weightedHomogeneousComponent w n (f * q) =
      MvPolynomial.weightedHomogeneousComponent w (n - i) f * q := by
  simp_rw [← MvPolynomial.weightedDecomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_right_mem_of_le _ hq hin

private lemma div_single_of_isWeightedHomogeneous {σ R : Type*} [CommRing R] (m : MonomialOrder σ)
    {w : σ → ℕ} {i n : ℕ} {b f : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b))
    (hbi : b.IsWeightedHomogeneous w i) (hf : f.IsWeightedHomogeneous w n) (hin : i ≤ n) :
    ∃ g r : MvPolynomial σ R, g.IsWeightedHomogeneous w (n - i) ∧ r.IsWeightedHomogeneous w n ∧
      f = g * b + r ∧ ∀ c ∈ r.support, ¬m.degree b ≤ c := by
  obtain ⟨g, r, hgr, -, hr⟩ := m.div_single hb f
  -- Take weight-`n` components in `f = g * b + r`.
  apply_fun MvPolynomial.weightedHomogeneousComponent w n at hgr
  rw [hf.weightedHomogeneousComponent_same, map_add,
    weightedHomogeneousComponent_mul_of_isWeightedHomogeneous_right hbi hin] at hgr
  refine ⟨_, _, MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous (n - i) g,
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous n r, hgr, fun c hc ↦ ?_⟩
  rw [MvPolynomial.support_weightedHomogeneousComponent, Finset.mem_filter] at hc
  exact hr c hc.1

private lemma lex_degree_discriminantPoly : MonomialOrder.lex.degree discriminantPoly =
    Finsupp.single 0 3 := by
  -- The leading monomial of `X₀ ^ 3 - X₁ ^ 2` is `X₀ ^ 3`, as `X₁ ^ 2 < X₀ ^ 3` lexicographically.
  rw [discriminantPoly, MonomialOrder.degree_smul_of_isRegular (.of_ne_zero (by norm_num)),
    MonomialOrder.degree_sub_of_lt] <;>
    simp [MonomialOrder.degree_pow, MonomialOrder.degree_X, MonomialOrder.lex_lt_iff,
      Finsupp.Lex.lt_iff]

private lemma exists_eq_reduced_add_discriminantPoly_mul {n : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n) (hn : 12 ≤ n) :
    ∃ r s : MvPolynomial (Fin 2) ℂ, r.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n ∧
      s.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) (n - 12) ∧
      p = r + discriminantPoly * s ∧ ∀ d ∈ r.support, d 0 < 3 := by
  -- Divide by `discriminantPoly`, whose leading monomial for the lexicographic order is `X₀ ^ 3`:
  -- every monomial of the remainder `r` then has `X₀`-degree `< 3`.
  obtain ⟨s, r, hs, hr, rfl, hr_red⟩ := div_single_of_isWeightedHomogeneous .lex
    (MonomialOrder.isUnit_leadingCoeff.mpr <| MonomialOrder.lex.ne_zero_of_degree_ne_zero <| by
      simp [lex_degree_discriminantPoly])
    discriminantPoly_isWeightedHomogeneous hp hn
  refine ⟨r, s, hr, hs, by ring, fun d hd ↦ ?_⟩
  simpa [lex_degree_discriminantPoly, Finsupp.single_le_iff] using hr_red d hd

private lemma reduced_isWeightedHomogeneous_eq_monomial {n : ℕ} {r : MvPolynomial (Fin 2) ℂ}
    (hr : r.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n)
    (hr_red : ∀ d ∈ r.support, d 0 < 3) {d₀ : Fin 2 →₀ ℕ} (hd₀ : d₀ ∈ r.support) :
    r = MvPolynomial.monomial d₀ (r.coeff d₀) :=
  -- An exponent `(a, b)` with `a < 3` is determined by its weight `4 * a + 6 * b`.
  MvPolynomial.eq_monomial_of_support_subset_singleton fun d hd ↦
    eq_of_weight_eq_of_lt_three (hr_red d hd) (hr_red d₀ hd₀) <|
      (hr (MvPolynomial.mem_support_iff.mp hd)).trans
        (hr (MvPolynomial.mem_support_iff.mp hd₀)).symm

private lemma reduced_eq_zero_of_eval_one_eq_zero {n : ℕ} {r : MvPolynomial (Fin 2) ℂ}
    (hr : r.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n)
    (hr_red : ∀ d ∈ r.support, d 0 < 3) (h0 : MvPolynomial.eval 1 r = 0) : r = 0 := by
  -- A nonzero `r` is a single monomial `c • X₀ ^ a * X₁ ^ b` with `c ≠ 0`, since its monomials
  -- all have weight `n` and `a < 3`; its value at `(1, 1)` is `c`.
  contrapose! h0 with hr0
  obtain ⟨d₀, hd₀⟩ := MvPolynomial.exists_coeff_ne_zero hr0
  rw [reduced_isWeightedHomogeneous_eq_monomial hr hr_red (MvPolynomial.mem_support_iff.mpr hd₀)]
  simpa [MvPolynomial.eval_monomial] using hd₀

private lemma evalE₄E₆_apply_eq_zero_of_discriminantPoly_mul_eq_zero {n : ℕ}
    {s : MvPolynomial (Fin 2) ℂ} (hs : s.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n)
    (hds : evalE₄E₆ (discriminantPoly * s) = 0) : evalE₄E₆ s n = 0 := by
  rw [map_mul, evalE₄E₆_discriminantPoly, evalE₄E₆_eq_of_isWeightedHomogeneous hs,
    DirectSum.of_mul_of, map_eq_zero_iff _ (DirectSum.of_injective _)] at hds
  -- Now `hds : Δ * g = 0` with `g = (evalE₄E₆ s) n`, and `Δ` has no zeros on `ℍ`.
  simpa [DFunLike.ext_iff, discriminant_ne_zero, GradedMonoid.GMul.mul] using hds

private lemma eq_zero_of_isWeightedHomogeneous_of_evalE₄E₆_apply_eq_zero {n : ℕ}
    {p : MvPolynomial (Fin 2) ℂ} (hp : p.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n)
    (heval : evalE₄E₆ p n = 0) : p = 0 := by
  induction n using Nat.strong_induction_on generalizing p with | _ n ih => ?_
  -- `evalE₄E₆ p` lies in degree `n`, so it vanishes, and so does the constant term `p (1, 1)` of
  -- its `q`-expansion.
  replace heval : evalE₄E₆ p = 0 := by
    rw [evalE₄E₆_eq_of_isWeightedHomogeneous hp, heval, map_zero]
  have h1 : MvPolynomial.eval 1 p = 0 := by
    rw [← constantCoeff_qExpansionAlgHom_evalE₄E₆, heval, map_zero, map_zero]
  obtain hn12 | hn12 := lt_or_ge n 12
  · -- In weight `n < 12`, every monomial `X₀ ^ a * X₁ ^ b` has `a < 3`.
    refine reduced_eq_zero_of_eval_one_eq_zero hp (fun d hd ↦ ?_) h1
    lia [weight_four_six_apply d, hp (MvPolynomial.mem_support_iff.mp hd)]
  -- Otherwise `p = r + D * s` with `r` reduced: `D (1, 1) = 0` gives `r (1, 1) = 0`, so `r = 0`;
  -- then `Δ * evalE₄E₆ s = 0` gives `s = 0` by induction.
  obtain ⟨r, s, hr, hs, rfl, hr_red⟩ := exists_eq_reduced_add_discriminantPoly_mul hp hn12
  obtain rfl : r = 0 :=
    reduced_eq_zero_of_eval_one_eq_zero hr hr_red (by simpa [discriminantPoly] using h1)
  rw [zero_add] at heval
  simp [ih _ (by lia) hs (evalE₄E₆_apply_eq_zero_of_discriminantPoly_mul_eq_zero hs heval)]

/-- The evaluation homomorphism `evalE₄E₆` is injective, i.e. `E₄` and `E₆` are algebraically
independent over `ℂ` in the graded ring `⨁ k, ModularForm 𝒮ℒ k`. Together with
`evalE₄E₆_surjective`, this gives the isomorphism `mvPolynomialEquivModularForms`. -/
theorem evalE₄E₆_injective : Function.Injective evalE₄E₆ := by
  refine (injective_iff_map_eq_zero _).2 fun p hp ↦ ?_
  rw [← MvPolynomial.sum_weightedHomogeneousComponent ![4, 6] p]
  refine finsum_eq_zero_of_forall_eq_zero fun n ↦
    eq_zero_of_isWeightedHomogeneous_of_evalE₄E₆_apply_eq_zero
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _) ?_
  -- The weight-`n` component of `p` maps to the weight-`n` part of `evalE₄E₆ p = 0`.
  rw [evalE₄E₆_weightedHomogeneousComponent_apply, hp, DirectSum.zero_apply]

/-- `E₄` and `E₆` are algebraically independent over `ℂ` in the graded ring
`⨁ k, ModularForm 𝒮ℒ k`; this is `evalE₄E₆_injective` stated with `AlgebraicIndependent`. -/
theorem algebraicIndependent_E₄_E₆ : AlgebraicIndependent ℂ ![DirectSum.of (ModularForm 𝒮ℒ) 4 E₄,
    DirectSum.of (ModularForm 𝒮ℒ) 6 E₆] := by
  -- In the PR this is `evalE₄E₆_injective` by definitional unfolding.
  rw [algebraicIndependent_iff_injective_aeval, ← evalE₄E₆_eq_aeval]
  exact evalE₄E₆_injective

/-- The `ℂ`-algebra isomorphism `ℂ[X₀, X₁] ≃ₐ[ℂ] ⨁ k, ModularForm 𝒮ℒ k` given by `evalE₄E₆`,
sending `X₀` to `E₄` (in weight `4`) and `X₁` to `E₆` (in weight `6`). Its inverse writes each
element of the graded ring of level-1 modular forms uniquely as a polynomial in `E₄` and `E₆`. -/
def mvPolynomialEquivModularForms : MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] DirectSum ℤ (ModularForm 𝒮ℒ) :=
  AlgEquiv.ofBijective evalE₄E₆ ⟨evalE₄E₆_injective, evalE₄E₆_surjective⟩

/-- As a function, `mvPolynomialEquivModularForms` is the evaluation map `evalE₄E₆`, so `simp`
computes it on explicit polynomials via `evalE₄E₆_X_zero` and `evalE₄E₆_X_one`. -/
@[simp]
lemma mvPolynomialEquivModularForms_apply (p : MvPolynomial (Fin 2) ℂ) :
    mvPolynomialEquivModularForms p = evalE₄E₆ p :=
  AlgEquiv.ofBijective_apply _ _ p

/-- `mvPolynomialEquivModularForms.symm` inverts the evaluation map `evalE₄E₆`. -/
@[simp]
lemma mvPolynomialEquivModularForms_symm_evalE₄E₆ (p : MvPolynomial (Fin 2) ℂ) :
    mvPolynomialEquivModularForms.symm (evalE₄E₆ p) = p :=
  AlgEquiv.ofBijective_symm_apply_apply _ _ p

/-- The graded ring `⨁ k, ModularForm 𝒮ℒ k` of level-1 modular forms is an integral domain. -/
instance : IsDomain (DirectSum ℤ (ModularForm 𝒮ℒ)) :=
  -- The graded ring is isomorphic to the polynomial ring `ℂ[X₀, X₁]`, which is a domain.
  mvPolynomialEquivModularForms.symm.toMulEquiv.isDomain _

end ModularForm

end
