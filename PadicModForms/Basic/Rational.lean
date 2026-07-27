/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Algebra.DirectSum.Internal

public import PadicModForms.EisensteinSeries.Defs
public import PadicModForms.ForMathlib.«38813»

/-!
# Rational modular forms

This file defines rational modular forms in terms of their `q`-expansions and develops their
basic algebraic structure. It also upgrades the presentation of the graded ring of complex
level-one modular forms as `ℂ[E₄, E₆]` to rational modular forms.

The main steps are:

* show that rational modular forms of a fixed weight form a submodule of `ℚ⟦X⟧`, and that
  these submodules form a graded ring;
* define evaluation at the rational `q`-expansions of `E₄` and `E₆`;
* compare rational evaluation, after extending scalars to `ℂ`, with
  `ModularForm.evalE₄E₆`;
* descend the coefficients of a complex polynomial whose evaluated `q`-expansion is rational;
* identify the graded ring of rational modular forms with `ℚ[X₀, X₁]`.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups EisensteinSeries

open scoped MatrixGroups

namespace PowerSeries

/-! ## Rational modular forms -/

/-- A rational power series is a modular form of weight `k` if it is the `q`-expansion of a
classical modular form of level one and weight `k`. -/
def isModularForm (k : ℤ) (f : ℚ⟦X⟧) : Prop :=
  ∃ g : ModularForm 𝒮ℒ k, qExpansion 1 g = f.map (algebraMap ℚ ℂ)

/-! ## The graded pieces of rational modular forms -/

/-- The zero power series is a rational modular form of every weight. -/
theorem zero_isModularForm (k : ℤ) : (0 : ℚ⟦X⟧).isModularForm k := by
  sorry

/-- The sum of two rational modular forms of the same weight is modular of that weight. -/
theorem IsModularForm.add {k : ℤ} {f g : ℚ⟦X⟧}
    (hf : f.isModularForm k) (hg : g.isModularForm k) : (f + g).isModularForm k := by
  sorry

/-- The negative of a rational modular form is modular of the same weight. -/
theorem IsModularForm.neg {k : ℤ} {f : ℚ⟦X⟧} (hf : f.isModularForm k) :
    (-f).isModularForm k := by
  sorry

/-- The difference of two rational modular forms of the same weight is modular of that weight. -/
theorem IsModularForm.sub {k : ℤ} {f g : ℚ⟦X⟧}
    (hf : f.isModularForm k) (hg : g.isModularForm k) : (f - g).isModularForm k := by
  sorry

/-- A rational scalar multiple of a rational modular form is modular of the same weight. -/
theorem IsModularForm.smul {k : ℤ} {f : ℚ⟦X⟧} (hf : f.isModularForm k) (a : ℚ) :
    (a • f).isModularForm k := by
  sorry

/-- The constant power series `1` is a rational modular form of weight zero. -/
theorem one_isModularForm : (1 : ℚ⟦X⟧).isModularForm 0 := by
  sorry

/-- The product of rational modular forms of weights `k` and `l` is modular of weight `k + l`. -/
theorem IsModularForm.mul {k l : ℤ} {f g : ℚ⟦X⟧}
    (hf : f.isModularForm k) (hg : g.isModularForm l) : (f * g).isModularForm (k + l) := by
  sorry

/-- Rational modular forms of weight `k`, as a submodule of rational power series. -/
def rationalModularForms (k : ℤ) : Submodule ℚ ℚ⟦X⟧ where
  carrier := {f | f.isModularForm k}
  zero_mem' := zero_isModularForm k
  add_mem' hf hg := IsModularForm.add hf hg
  smul_mem' a _ hf := IsModularForm.smul hf a

@[simp]
theorem mem_rationalModularForms {k : ℤ} {f : ℚ⟦X⟧} :
    f ∈ rationalModularForms k ↔ f.isModularForm k :=
  Iff.rfl

/-- The submodules of rational modular forms form a graded monoid under multiplication. -/
instance rationalModularForms.instGradedMonoid :
    SetLike.GradedMonoid rationalModularForms where
  one_mem := one_isModularForm
  mul_mem _ _ _ _ hf hg := IsModularForm.mul hf hg

/-- Rational modular forms of a fixed weight, as a type. -/
abbrev RationalModularForm (k : ℤ) := ↥(rationalModularForms k)

/-- The graded ring of level-one rational modular forms. -/
abbrev GradedRationalModularForms := DirectSum ℤ RationalModularForm

/-! ## Rational Eisenstein series and evaluation -/

/-- The rational `q`-expansion of `E₄`, regarded as a rational modular form of weight four. -/
def E₄Rat : RationalModularForm 4 :=
  ⟨E_rat 4, by
    sorry⟩

/-- The rational `q`-expansion of `E₆`, regarded as a rational modular form of weight six. -/
def E₆Rat : RationalModularForm 6 :=
  ⟨E_rat 6, by
    sorry⟩

@[simp]
theorem coe_E₄Rat : (E₄Rat : ℚ⟦X⟧) = E_rat 4 :=
  rfl

@[simp]
theorem coe_E₆Rat : (E₆Rat : ℚ⟦X⟧) = E_rat 6 :=
  rfl

/-- Evaluation in the graded ring of rational modular forms, sending `X₀` to `E₄` and `X₁`
to `E₆`. -/
def evalE₄E₆Rat :
    MvPolynomial (Fin 2) ℚ →ₐ[ℚ] GradedRationalModularForms :=
  MvPolynomial.aeval
    ![DirectSum.of RationalModularForm 4 E₄Rat,
      DirectSum.of RationalModularForm 6 E₆Rat]

@[simp]
theorem evalE₄E₆Rat_X0 :
    evalE₄E₆Rat (MvPolynomial.X 0) = DirectSum.of RationalModularForm 4 E₄Rat := by
  sorry

@[simp]
theorem evalE₄E₆Rat_X1 :
    evalE₄E₆Rat (MvPolynomial.X 1) = DirectSum.of RationalModularForm 6 E₆Rat := by
  sorry

theorem evalE₄E₆Rat_C (a : ℚ) :
    evalE₄E₆Rat (MvPolynomial.C a) =
      algebraMap ℚ GradedRationalModularForms a := by
  sorry

theorem evalE₄E₆Rat_monomial (a b : ℕ) :
    evalE₄E₆Rat (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      DirectSum.of RationalModularForm 4 E₄Rat ^ a *
        DirectSum.of RationalModularForm 6 E₆Rat ^ b := by
  sorry

/-- Forgetting the weight gives the `q`-expansion homomorphism from the graded ring of rational
modular forms to rational power series. -/
def rationalQExpansion :
    GradedRationalModularForms →ₐ[ℚ] ℚ⟦X⟧ :=
  DirectSum.coeAlgHom rationalModularForms

@[simp]
theorem rationalQExpansion_of (k : ℤ) (f : rationalModularForms k) :
    rationalQExpansion (DirectSum.of RationalModularForm k f) = f := by
  sorry

/-- Polynomial evaluation directly in rational power series at the rational `q`-expansions of
`E₄` and `E₆`. -/
def evalE₄E₆RatQExpansion :
    MvPolynomial (Fin 2) ℚ →ₐ[ℚ] ℚ⟦X⟧ :=
  MvPolynomial.aeval ![E_rat 4, E_rat 6]

@[simp]
theorem evalE₄E₆RatQExpansion_X0 :
    evalE₄E₆RatQExpansion (MvPolynomial.X 0) = E_rat 4 := by
  sorry

@[simp]
theorem evalE₄E₆RatQExpansion_X1 :
    evalE₄E₆RatQExpansion (MvPolynomial.X 1) = E_rat 6 := by
  sorry

/-- Evaluating in the rational graded ring and then forgetting the weight agrees with direct
evaluation in rational power series. -/
theorem rationalQExpansion_comp_evalE₄E₆Rat :
    rationalQExpansion.comp evalE₄E₆Rat = evalE₄E₆RatQExpansion := by
  sorry

/-! ## Comparison with complex modular forms -/

/-- Extending the rational `q`-expansion of `E₄` to `ℂ` gives the `q`-expansion of the complex
modular form `E₄`. -/
theorem E₄Rat_map_complex :
    (E_rat 4).map (algebraMap ℚ ℂ) = qExpansion 1 E₄ := by
  sorry

/-- Extending the rational `q`-expansion of `E₆` to `ℂ` gives the `q`-expansion of the complex
modular form `E₆`. -/
theorem E₆Rat_map_complex :
    (E_rat 6).map (algebraMap ℚ ℂ) = qExpansion 1 E₆ := by
  sorry

/-- Extending rational polynomial evaluation to `ℂ` agrees with evaluating the scalar-extended
polynomial in the complex graded ring and then taking its `q`-expansion. -/
theorem evalE₄E₆RatQExpansion_map_complex (P : MvPolynomial (Fin 2) ℚ) :
    (evalE₄E₆RatQExpansion P).map (algebraMap ℚ ℂ) =
      ModularForm.qExpansionRingHom (h := 1) one_pos one_mem_strictPeriods_SL
        (ModularForm.evalE₄E₆ (MvPolynomial.map (algebraMap ℚ ℂ) P)) := by
  sorry

/-- Scalar extension from rational to complex coefficients is injective on multivariate
polynomials. -/
theorem map_complex_injective :
    Function.Injective
      (MvPolynomial.map (σ := Fin 2) (algebraMap ℚ ℂ)) := by
  sorry

/-- Direct evaluation at the rational `q`-expansions of `E₄` and `E₆` is injective. -/
theorem evalE₄E₆RatQExpansion_injective :
    Function.Injective evalE₄E₆RatQExpansion := by
  sorry

/-- Evaluation in the graded ring of rational modular forms is injective. -/
theorem evalE₄E₆Rat_injective :
    Function.Injective evalE₄E₆Rat := by
  sorry

/-! ## Rational descent -/

/-- The rational `q`-expansion associated with the monomial of exponent vector `d`. -/
def E₄E₆MonomialQExpansion (d : Fin 2 →₀ ℕ) : ℚ⟦X⟧ :=
  E_rat 4 ^ d 0 * E_rat 6 ^ d 1

/-- Extending a rational monomial `q`-expansion to `ℂ` agrees with evaluating the corresponding
monomial in the complex modular forms `E₄` and `E₆` and taking its `q`-expansion. -/
theorem E₄E₆MonomialQExpansion_map_complex (d : Fin 2 →₀ ℕ) :
    (E₄E₆MonomialQExpansion d).map (algebraMap ℚ ℂ) =
      ModularForm.qExpansionRingHom (h := 1) one_pos one_mem_strictPeriods_SL
        (ModularForm.evalE₄E₆ (MvPolynomial.monomial d 1)) := by
  sorry

/-- The complex scalar extensions of the rational monomial `q`-expansions in `E₄` and `E₆` are
linearly independent. -/
theorem E₄E₆MonomialQExpansion_linearIndependent :
    LinearIndependent ℂ
      (fun d : Fin 2 →₀ ℕ ↦ (E₄E₆MonomialQExpansion d).map (algebraMap ℚ ℂ)) := by
  sorry

/-- Finitely many coefficients detect all linear combinations of a finite linearly independent
family of rational power series. -/
theorem exists_coeff_finset_detecting_linear_combinations
    {ι : Type*} [Fintype ι] (v : ι → ℚ⟦X⟧) (hv : LinearIndependent ℚ v) :
    ∃ s : Finset ℕ,
      Function.Injective fun c : ι → ℚ ↦
        fun n : s ↦ coeff n (∑ i, c i • v i) := by
  sorry

/-- If a complex linear combination of rational power series is rational and the scalar-extended
family is linearly independent, then all coefficients in the linear combination are rational. -/
theorem exists_rat_coefficients_of_sum_map_eq
    {ι : Type*} [Fintype ι] (v : ι → ℚ⟦X⟧)
    (hv : LinearIndependent ℂ (fun i ↦ (v i).map (algebraMap ℚ ℂ)))
    (c : ι → ℂ) (f : ℚ⟦X⟧)
    (h : ∑ i, c i • (v i).map (algebraMap ℚ ℂ) = f.map (algebraMap ℚ ℂ)) :
    ∃ a : ι → ℚ, c = fun i ↦ (a i : ℂ) := by
  sorry

/-- A complex polynomial whose evaluation at `E₄` and `E₆` has rational `q`-expansion has
rational coefficients. -/
theorem exists_ratPolynomial_of_evalE₄E₆_qExpansion_eq_map
    (P : MvPolynomial (Fin 2) ℂ) (f : ℚ⟦X⟧)
    (hP :
      ModularForm.qExpansionRingHom (h := 1) one_pos one_mem_strictPeriods_SL
          (ModularForm.evalE₄E₆ P) =
        f.map (algebraMap ℚ ℂ)) :
    ∃ Q : MvPolynomial (Fin 2) ℚ, MvPolynomial.map (algebraMap ℚ ℂ) Q = P := by
  sorry

/-! ## Fixed weights -/

/-- The weights assigned to the variables corresponding to `E₄` and `E₆`. -/
abbrev E₄E₆Weights : Fin 2 → ℕ := ![4, 6]

/-- A weighted-homogeneous rational polynomial of weighted degree `n` evaluates to a rational
modular form of weight `n`. -/
theorem isModularForm_evalE₄E₆RatQExpansion_of_isWeightedHomogeneous
    {n : ℕ} {P : MvPolynomial (Fin 2) ℚ}
    (hP : P.IsWeightedHomogeneous E₄E₆Weights n) :
    (evalE₄E₆RatQExpansion P).isModularForm n := by
  sorry

/-- Evaluation of a weighted-homogeneous polynomial is supported in the corresponding component
of the graded ring of rational modular forms. -/
theorem evalE₄E₆Rat_eq_of_isWeightedHomogeneous
    {n : ℕ} {P : MvPolynomial (Fin 2) ℚ}
    (hP : P.IsWeightedHomogeneous E₄E₆Weights n) :
    evalE₄E₆Rat P =
      DirectSum.of RationalModularForm (n : ℤ)
        ⟨evalE₄E₆RatQExpansion P,
          isModularForm_evalE₄E₆RatQExpansion_of_isWeightedHomogeneous hP⟩ := by
  sorry

/-- A rational modular form of nonnegative integral weight is the evaluation of a rational
weighted-homogeneous polynomial in `E₄` and `E₆`. -/
theorem exists_isWeightedHomogeneous_evalE₄E₆RatQExpansion
    {n : ℕ} {f : ℚ⟦X⟧} (hf : f.isModularForm n) :
    ∃ P : MvPolynomial (Fin 2) ℚ,
      P.IsWeightedHomogeneous E₄E₆Weights n ∧ evalE₄E₆RatQExpansion P = f := by
  sorry

/-- Every rational modular form, in any integral weight, has a rational polynomial preimage in
the corresponding component of the graded ring. -/
theorem exists_evalE₄E₆Rat_eq_of_isModularForm
    {k : ℤ} {f : ℚ⟦X⟧} (hf : f.isModularForm k) :
    ∃ P : MvPolynomial (Fin 2) ℚ,
      evalE₄E₆Rat P = DirectSum.of RationalModularForm k ⟨f, hf⟩ := by
  sorry

/-! ## The rational graded-ring isomorphism -/

/-- Evaluation at `E₄` and `E₆` is surjective onto the graded ring of rational modular forms. -/
theorem evalE₄E₆Rat_surjective :
    Function.Surjective evalE₄E₆Rat := by
  sorry

/-- The graded ring of rational level-one modular forms is isomorphic to `ℚ[X₀, X₁]`. -/
def rationalModularFormsEquivMvPolynomial :
    MvPolynomial (Fin 2) ℚ ≃ₐ[ℚ] GradedRationalModularForms :=
  AlgEquiv.ofBijective evalE₄E₆Rat
    ⟨evalE₄E₆Rat_injective, evalE₄E₆Rat_surjective⟩

/-- The rational modular forms `E₄` and `E₆` generate the graded ring of rational modular
forms as a `ℚ`-algebra. -/
theorem E₄E₆Rat_generate :
    Algebra.adjoin ℚ
      ({DirectSum.of RationalModularForm 4 E₄Rat,
          DirectSum.of RationalModularForm 6 E₆Rat} :
        Set GradedRationalModularForms) = ⊤ := by
  sorry

end PowerSeries
