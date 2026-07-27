/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Algebra.DirectSum.Internal

public import PadicModForms.ForMathlib.«38813»
public import PadicModForms.Rational.Eisenstein

/-!
# The graded ring of rational modular forms

This file develops the graded algebra of rational modular forms and gives the planned
identification with `ℚ[E₄, E₆]`.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups EisensteinSeries SetLike DirectSum

open scoped MatrixGroups

namespace PowerSeries

/-- The submodules of rational modular forms form a graded monoid under multiplication. -/
instance : GradedMonoid rationalModularForms where
  one_mem := one_isModularForm
  mul_mem _ _ _ _ hf hg := IsModularForm.mul hf hg

/-- The graded ring of level-one rational modular forms. -/
abbrev GradedRationalModularForms := ⨁ i, RationalModularForm i

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
    ![of RationalModularForm 4 E₄Rat, of RationalModularForm 6 E₆Rat]

@[simp]
theorem evalE₄E₆Rat_X0 :
    evalE₄E₆Rat (MvPolynomial.X 0) = of RationalModularForm 4 E₄Rat := by
  sorry

@[simp]
theorem evalE₄E₆Rat_X1 :
    evalE₄E₆Rat (MvPolynomial.X 1) = of RationalModularForm 6 E₆Rat := by
  sorry

theorem evalE₄E₆Rat_C (a : ℚ) :
    evalE₄E₆Rat (MvPolynomial.C a) =
      algebraMap ℚ GradedRationalModularForms a := by
  sorry

theorem evalE₄E₆Rat_monomial (a b : ℕ) :
    evalE₄E₆Rat (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      of RationalModularForm 4 E₄Rat ^ a * of RationalModularForm 6 E₆Rat ^ b := by
  sorry

/-- Forgetting the weight gives the `q`-expansion homomorphism from the graded ring of rational
modular forms to rational power series. -/
def rationalQExpansion :
    GradedRationalModularForms →ₐ[ℚ] ℚ⟦X⟧ :=
  coeAlgHom rationalModularForms

@[simp]
theorem rationalQExpansion_of (k : ℤ) (f : rationalModularForms k) :
    rationalQExpansion (of RationalModularForm k f) = f := by
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
      of RationalModularForm (n : ℤ)
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
      evalE₄E₆Rat P = of RationalModularForm k ⟨f, hf⟩ := by
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
      ({of RationalModularForm 4 E₄Rat, of RationalModularForm 6 E₆Rat} :
        Set GradedRationalModularForms) = ⊤ := by
  sorry

end PowerSeries
