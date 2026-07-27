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

open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries SetLike DirectSum MvPolynomial

open scoped MatrixGroups PowerSeries

namespace ModularForm

/-- The submodules of rational modular forms form a graded monoid under multiplication. -/
instance : GradedMonoid rationalModularForms where
  one_mem := PowerSeries.one_isModularForm
  mul_mem _ _ := PowerSeries.IsModularForm.mul

/-- The graded ring of level-one rational modular forms. -/
abbrev _root_.GradedRationalModularForms := ⨁ i, rationalModularForms i

/-! ## Rational Eisenstein series and evaluation -/

variable {k : ℕ}

/-- The rational `q`-expansion of `Eₖ`, regarded as a rational modular form of weight `k`. -/
def ERat (hk : 3 ≤ k) (hk2 : Even k) : rationalModularForms k :=
  ⟨E_rat k, E_rat_isModularForm hk hk2⟩

@[simp]
theorem coe_ERat (hk : 3 ≤ k) (hk2 : Even k) : (ERat hk hk2 : ℚ⟦X⟧) = E_rat k := rfl

def E₄Rat : rationalModularForms 4 :=
  ERat (by norm_num) ⟨2, rfl⟩

def E₆Rat : rationalModularForms 6 :=
  ERat (by norm_num) ⟨3, rfl⟩

/-- Evaluation in the graded ring of rational modular forms, sending `X₀` to `E₄` and `X₁`
to `E₆`. -/
def evalE₄E₆Rat : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] GradedRationalModularForms :=
  aeval ![of _ 4 E₄Rat, of _ 6 E₆Rat]

@[simp]
theorem evalE₄E₆Rat_X0 :
    evalE₄E₆Rat (X 0) = of _ 4 E₄Rat := by
  simp [evalE₄E₆Rat]

@[simp]
theorem evalE₄E₆Rat_X1 :
    evalE₄E₆Rat (X 1) = of _ 6 E₆Rat := by
  simp [evalE₄E₆Rat]

theorem evalE₄E₆Rat_C (a : ℚ) : evalE₄E₆Rat (C a) = algebraMap ℚ _ a := by
  simp [evalE₄E₆Rat]

theorem evalE₄E₆Rat_monomial (a b : ℕ) :
    evalE₄E₆Rat (X 0 ^ a * X 1 ^ b) = of _ 4 E₄Rat ^ a * of _ 6 E₆Rat ^ b := by
  simp [evalE₄E₆Rat]

/-- Forgetting the weight gives the `q`-expansion homomorphism from the graded ring of rational
modular forms to rational power series. -/
@[simps!]
def rationalQExpansion : GradedRationalModularForms →ₐ[ℚ] ℚ⟦X⟧ :=
  coeAlgHom rationalModularForms

@[simp]
theorem rationalQExpansion_of {k : ℤ} (f : rationalModularForms k) :
    rationalQExpansion (of _ k f) = f :=
  coeAlgHom_of ..

/-! ## Comparison with complex modular forms -/

/-- Extending `ERat` to `ℂ` gives the `q`-expansion of the complex Eisenstein series. -/
theorem ERat_map_complex (hk : 3 ≤ k) (hk2 : Even k) :
    (ERat hk hk2 : ℚ⟦X⟧).map (algebraMap ℚ ℂ) = qExpansion 1 (E hk) := by
  simpa using (qExpansion_E_eq_E_rat_map hk hk2).symm

theorem rationalQExpansion_evalE₄E₆Rat_map_C (a : ℚ) :
    (rationalQExpansion (evalE₄E₆Rat (C a))).map (algebraMap ℚ ℂ) =
      qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL
        (evalE₄E₆ ((C a).map (algebraMap ℚ ℂ))) :=
  calc _ = (a : ℂ) • 1 := by simp [Algebra.smul_def]
    _ = (a : ℂ) • qExpansion 1 (1 : ModularForm 𝒮ℒ 0) := by rw [ModularForm.qExpansion_one]
    _ = qExpansion 1 (((a : ℂ) • 1 : ModularForm 𝒮ℒ 0)) :=
      (ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL _ _).symm
    _ = qExpansion 1 (const a : ModularForm 𝒮ℒ 0) := by rw [show const a = (a : ℂ) • 1 by ext; simp]
    _ = _ := by simp [DirectSum.algebraMap_apply]; rfl

theorem rationalQExpansion_evalE₄E₆Rat_map_X0 :
    (rationalQExpansion (evalE₄E₆Rat (X 0))).map (algebraMap ℚ ℂ) =
      qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL
        (evalE₄E₆ ((X 0).map (algebraMap ℚ ℂ))) := by
  calc _ = (E₄Rat : ℚ⟦X⟧).map _ := by rw [evalE₄E₆Rat_X0, rationalQExpansion_of]
    _ = qExpansion 1 E₄ := ERat_map_complex _ ⟨2, rfl⟩
    _ = _ := by simp

theorem rationalQExpansion_evalE₄E₆Rat_map_X1 :
    (rationalQExpansion (evalE₄E₆Rat (X 1))).map (algebraMap ℚ ℂ) =
      qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL
        (evalE₄E₆ ((X 1).map (algebraMap ℚ ℂ))) := by
  calc _ = (E₆Rat : ℚ⟦X⟧).map (algebraMap ℚ ℂ) := by rw [evalE₄E₆Rat_X1, rationalQExpansion_of]
    _ = qExpansion 1 E₆ := ERat_map_complex _ ⟨3, rfl⟩
    _ = _ := by simp

theorem rationalQExpansion_evalE₄E₆Rat_map_X (i : Fin 2) :
    (rationalQExpansion (evalE₄E₆Rat (X i))).map (algebraMap ℚ ℂ) =
      qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL
        (evalE₄E₆ ((X i).map (algebraMap ℚ ℂ))) := by
  fin_cases i
  · exact rationalQExpansion_evalE₄E₆Rat_map_X0
  · exact rationalQExpansion_evalE₄E₆Rat_map_X1

theorem rationalQExpansion_evalE₄E₆Rat_map (P : MvPolynomial (Fin 2) ℚ) :
    (rationalQExpansion (evalE₄E₆Rat P)).map (algebraMap ℚ ℂ) =
      qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL (evalE₄E₆ (P.map (algebraMap ℚ ℂ))) := by
  induction P using MvPolynomial.induction_on with
  | C a => exact rationalQExpansion_evalE₄E₆Rat_map_C a
  | add P Q hP hQ =>
    simpa only [map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simpa using congrArg₂ (· * ·) hP (rationalQExpansion_evalE₄E₆Rat_map_X i)

theorem map_complex_injective : Function.Injective (map (σ := Fin 2) (algebraMap ℚ ℂ)) := by
  sorry

theorem evalE₄E₆Rat_injective : Function.Injective evalE₄E₆Rat := by
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
        (ModularForm.evalE₄E₆ (monomial d 1)) := by
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
        fun n : s ↦ PowerSeries.coeff n (∑ i, c i • v i) := by
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
    ∃ Q : MvPolynomial (Fin 2) ℚ, Q.map (algebraMap ℚ ℂ) = P := by
  sorry

/-! ## Fixed weights -/

/-- The weights assigned to the variables corresponding to `E₄` and `E₆`. -/
abbrev E₄E₆Weights : Fin 2 → ℕ := ![4, 6]

/-- The underlying `q`-expansion of a weighted-homogeneous polynomial of weighted degree `n`
is a rational modular form of weight `n`. -/
theorem isModularForm_rationalQExpansion_evalE₄E₆Rat_of_isWeightedHomogeneous
    {n : ℕ} {P : MvPolynomial (Fin 2) ℚ}
    (hP : P.IsWeightedHomogeneous E₄E₆Weights n) :
    (rationalQExpansion (evalE₄E₆Rat P)).isModularForm n := by
  sorry

/-- Evaluation of a weighted-homogeneous polynomial is supported in the corresponding component
of the graded ring of rational modular forms. -/
theorem evalE₄E₆Rat_eq_of_isWeightedHomogeneous
    {n : ℕ} {P : MvPolynomial (Fin 2) ℚ}
    (hP : P.IsWeightedHomogeneous E₄E₆Weights n) :
    evalE₄E₆Rat P =
      of (fun i ↦ rationalModularForms i) (n : ℤ)
        ⟨rationalQExpansion (evalE₄E₆Rat P),
          isModularForm_rationalQExpansion_evalE₄E₆Rat_of_isWeightedHomogeneous hP⟩ := by
  sorry

/-- A rational modular form of nonnegative integral weight is the evaluation of a rational
weighted-homogeneous polynomial in `E₄` and `E₆`. -/
theorem exists_isWeightedHomogeneous_rationalQExpansion_evalE₄E₆Rat
    {n : ℕ} {f : ℚ⟦X⟧} (hf : f.isModularForm n) :
    ∃ P : MvPolynomial (Fin 2) ℚ,
      P.IsWeightedHomogeneous E₄E₆Weights n ∧ rationalQExpansion (evalE₄E₆Rat P) = f := by
  sorry

/-- Every rational modular form, in any integral weight, has a rational polynomial preimage in
the corresponding component of the graded ring. -/
theorem exists_evalE₄E₆Rat_eq_of_isModularForm
    {k : ℤ} {f : ℚ⟦X⟧} (hf : f.isModularForm k) :
    ∃ P : MvPolynomial (Fin 2) ℚ,
      evalE₄E₆Rat P = of (fun i ↦ rationalModularForms i) k ⟨f, hf⟩ := by
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
      ({of (fun i ↦ rationalModularForms i) 4 E₄Rat,
          of (fun i ↦ rationalModularForms i) 6 E₆Rat} : Set GradedRationalModularForms) = ⊤ := by
  sorry

end ModularForm
