/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.RingTheory.MvPolynomial.Tower

public import PadicModForms.ForMathlib.«38813»
public import PadicModForms.Rational.Basic

/-!
# The graded ring of rational modular forms

This file develops the graded algebra of rational modular forms and gives the identification with
`ℚ[E₄, E₆]`.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries SetLike DirectSum MvPolynomial

open scoped MatrixGroups PowerSeries

namespace ModularForm

variable {k : ℕ} {n m : ℤ}

/-- Evaluation in the graded ring of rational modular forms, sending `X₀` to `E₄` and `X₁`
to `E₆`. -/
def evalE₄E₆Rat : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] ⨁ i, rationalModularForms i :=
  aeval ![of _ 4 E₄Rat, of _ 6 E₆Rat]

@[simp]
theorem evalE₄E₆Rat_X0 : evalE₄E₆Rat (X 0) = of _ 4 E₄Rat := by
  simp [evalE₄E₆Rat]

@[simp]
theorem evalE₄E₆Rat_X1 : evalE₄E₆Rat (X 1) = of _ 6 E₆Rat := by
  simp [evalE₄E₆Rat]

theorem evalE₄E₆Rat_C (a : ℚ) : evalE₄E₆Rat (C a) = algebraMap ℚ _ a := by
  simp [evalE₄E₆Rat]

theorem evalE₄E₆Rat_monomial (a b : ℕ) :
    evalE₄E₆Rat (X 0 ^ a * X 1 ^ b) = of _ 4 E₄Rat ^ a * of _ 6 E₆Rat ^ b := by
  simp [evalE₄E₆Rat]

variable (f g : rationalModularForms n)

theorem ERat_map_complex (hk : 3 ≤ k) (hk2 : Even k) :
    (ERat hk hk2 : ℚ⟦X⟧).map (algebraMap ℚ ℂ) = qExpansion 1 (E hk) := by
  simpa using (qExpansion_E_eq_E_rat_map hk hk2).symm

@[simp]
private theorem rationalModularForms_gOne_eq_one :
    (1 : GradedMonoid (fun n ↦ ↥(rationalModularForms n))).2 = 1 := rfl

@[simp]
theorem rationalModularFormToComplex_one :
    rationalModularFormToComplex 1 = (1 : ModularForm 𝒮ℒ 0) :=
  (qExpansion_inj one_pos one_mem_strictPeriods_SL).1 (by simp [qExpansion_one 1])

open GradedMonoid

@[simp]
theorem rationalModularFormToComplex_mul (g : rationalModularForms m) :
    rationalModularFormToComplex (GMul.mul (A := fun n ↦ rationalModularForms n) f g) =
      (rationalModularFormToComplex f).mul (rationalModularFormToComplex g) := by
  refine (qExpansion_inj one_pos one_mem_strictPeriods_SL).1 ?_
  simpa using (ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL
    (rationalModularFormToComplex f) (rationalModularFormToComplex g)).symm

theorem rationalModularFormsToComplex_gOne :
    of _ 0 (rationalModularFormToComplex (GOne.one (A := fun n ↦ rationalModularForms n))) = 1 := by
  simp [← GradedMonoid.snd_one]

theorem rationalModularFormsToComplex_gMul (g : rationalModularForms m) :
    of _ (n + m) (rationalModularFormToComplex
        (GMul.mul (A := fun k ↦ rationalModularForms k) f g)) =
      of _ n (rationalModularFormToComplex f) * of _ m (rationalModularFormToComplex g) := by
  rw [rationalModularFormToComplex_mul, of_mul_of]
  exact congrArg (of (ModularForm 𝒮ℒ) (n + m)) rfl

/-- The underlying ring homomorphism for scalar extension from rational to complex modular forms. -/
def rationalModularFormsToComplexRingHom :
    (⨁ i, rationalModularForms i) →+* ⨁ k : ℤ, ModularForm 𝒮ℒ k :=
  toSemiring (fun m ↦ (of (fun n ↦ ModularForm 𝒮ℒ n) m).comp
      (rationalModularFormToComplex).toAddMonoidHom)
    rationalModularFormsToComplex_gOne rationalModularFormsToComplex_gMul

/-- The underlying scalar-extension ring homomorphism on homogeneous elements. -/
@[simp]
theorem rationalModularFormsToComplexRingHom_of :
    rationalModularFormsToComplexRingHom (of _ n f) =
      of _ n (rationalModularFormToComplex f) :=
  toSemiring_of ..

/-- Scalar extension from the graded ring of rational modular forms to the graded ring of
complex modular forms. -/
def rationalModularFormsToComplex :
    (⨁ i, rationalModularForms i) →ₐ[ℚ] ⨁ k : ℤ, ModularForm 𝒮ℒ k :=
  RingHom.toRatAlgHom (R := ⨁ i, rationalModularForms i)
    (S := ⨁ k : ℤ, ModularForm 𝒮ℒ k) rationalModularFormsToComplexRingHom

@[simp]
theorem rationalModularFormsToComplex_of :
    rationalModularFormsToComplex (of _ n f) = of _ n (rationalModularFormToComplex f) :=
  rationalModularFormsToComplexRingHom_of f

/-- The rational algebra structure on complex graded modular forms is compatible with its
complex algebra structure. -/
@[simp]
theorem algebraMap_rat_eq_complex (a : ℚ) :
    algebraMap ℚ (⨁ k : ℤ, ModularForm 𝒮ℒ k) a = algebraMap ℂ (⨁ k : ℤ, ModularForm 𝒮ℒ k) a :=
  rfl

@[simp]
theorem rationalModularFormToComplex_ERat (hk : 3 ≤ k) (hk2 : Even k) :
    rationalModularFormToComplex (ERat hk hk2) = E hk := by
  rw [← qExpansion_inj one_pos one_mem_strictPeriods_SL, qExpansion_rationalModularFormToComplex,
    ERat_map_complex]

@[simp]
theorem rationalModularFormToComplex_E₄Rat : rationalModularFormToComplex E₄Rat = E₄ :=
  rationalModularFormToComplex_ERat (by norm_num) ⟨2, rfl⟩

@[simp]
theorem rationalModularFormToComplex_E₆Rat : rationalModularFormToComplex E₆Rat = E₆ :=
  rationalModularFormToComplex_ERat (by norm_num) ⟨3, rfl⟩

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
  induction P using induction_on with
  | C a => exact rationalQExpansion_evalE₄E₆Rat_map_C a
  | add P Q hP hQ =>
    simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simpa using congrArg₂ (· * ·) hP (rationalQExpansion_evalE₄E₆Rat_map_X i)

/-- The scalar-extension square for evaluation at `E₄` and `E₆` commutes. -/
theorem rationalModularFormsToComplex_evalE₄E₆Rat (P : MvPolynomial (Fin 2) ℚ) :
    rationalModularFormsToComplex (evalE₄E₆Rat P) = evalE₄E₆ (P.map (algebraMap ℚ ℂ)) := by
  rw [evalE₄E₆Rat, comp_aeval_apply, evalE₄E₆, aeval_map_algebraMap]
  congr 2
  funext i
  fin_cases i <;> simp

/-- The rational `q`-expansion associated with the monomial of exponent vector `d`. -/
def E₄E₆MonomialQExpansion (d : Fin 2 →₀ ℕ) : ℚ⟦X⟧ := E_rat 4 ^ d 0 * E_rat 6 ^ d 1

@[simp]
theorem E₄E₆MonomialQExpansion_eq (d : Fin 2 →₀ ℕ) :
    E₄E₆MonomialQExpansion d = (E₄Rat : ℚ⟦X⟧) ^ d 0 * (E₆Rat : ℚ⟦X⟧) ^ d 1 := rfl

/-- Extending a rational monomial `q`-expansion to `ℂ` agrees with evaluating the corresponding
monomial in the complex modular forms `E₄` and `E₆` and taking its `q`-expansion. -/
theorem E₄E₆MonomialQExpansion_map_complex (d : Fin 2 →₀ ℕ) :
    (E₄E₆MonomialQExpansion d).map (algebraMap ℚ ℂ) = qExpansionRingHom 1 one_pos
      one_mem_strictPeriods_SL (evalE₄E₆ (monomial d 1)) :=
  calc _ = (rationalQExpansion _).map _ := congrArg (PowerSeries.map _) (by simp [monomial_fin_two])
    _ = qExpansionRingHom 1 one_pos _ _ := rationalQExpansion_evalE₄E₆Rat_map (monomial d 1)
    _ = _ := by simp

/-- The complex scalar extensions of the rational monomial `q`-expansions in `E₄` and `E₆` are
linearly independent. -/
theorem E₄E₆MonomialQExpansion_linearIndependent :
    LinearIndependent ℂ
      (fun d : Fin 2 →₀ ℕ ↦ (E₄E₆MonomialQExpansion d).map (algebraMap ℚ ℂ)) := by
  sorry

theorem evalE₄E₆Rat_injective : Function.Injective evalE₄E₆Rat := fun P Q hPQ ↦ by
  refine map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective (evalE₄E₆_injective ?_)
  simp [← rationalModularFormsToComplex_evalE₄E₆Rat, hPQ]

/-- Finitely many coefficients detect all linear combinations of a finite linearly independent
family of rational power series. -/
theorem exists_coeff_finset_detecting_linear_combinations
    {ι : Type*} [Fintype ι] (v : ι → ℚ⟦X⟧) (hv : LinearIndependent ℚ v) :
    ∃ s : Finset ℕ, Function.Injective fun c : ι → ℚ ↦
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
theorem exists_ratPolynomial_of_evalE₄E₆_qExpansion_eq_map (P : MvPolynomial (Fin 2) ℂ)
    (hP : ∃ f : ℚ⟦X⟧, qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL (evalE₄E₆ P) =
      f.map (algebraMap ℚ ℂ)) :
    ∃ Q : MvPolynomial (Fin 2) ℚ, Q.map (algebraMap ℚ ℂ) = P := by
  classical
  obtain ⟨f, hP⟩ := hP
  let v : P.support → ℚ⟦X⟧ := fun d ↦ E₄E₆MonomialQExpansion d
  let c : P.support → ℂ := fun d ↦ P.coeff d
  have hv : LinearIndependent ℂ (fun d ↦ (v d).map (algebraMap ℚ ℂ)) := by
    simpa [v, Function.comp_def] using
      E₄E₆MonomialQExpansion_linearIndependent.comp Subtype.val Subtype.val_injective
  have hC (a : ℂ) :
      qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL (evalE₄E₆ (C a)) =
        PowerSeries.C a := by
    calc _ = qExpansion 1 (const a) := by simp [algebraMap_apply]; rfl
      _ = qExpansion 1 (a • (1 : ModularForm 𝒮ℒ 0)) := by congr 2; ext; simp
      _ = a • qExpansion 1 (1 : ModularForm 𝒮ℒ 0) :=
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL _ _
      _ = PowerSeries.C a := by rw [ModularForm.qExpansion_one]; simp [Algebra.smul_def]
  have hsum : ∑ d, c d • (v d).map (algebraMap ℚ ℂ) = f.map (algebraMap ℚ ℂ) := by
    rw [← hP]
    calc
      ∑ d, c d • (v d).map (algebraMap ℚ ℂ) =
          ∑ d : P.support, qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL
            (evalE₄E₆ (monomial d (P.coeff d))) := by
              apply Finset.sum_congr rfl
              intro d _
              simp only [c, v, E₄E₆MonomialQExpansion_map_complex]
              rw [show monomial (d : Fin 2 →₀ ℕ) (P.coeff d) =
                C (P.coeff d) * monomial d 1 by
                  simpa using
                    (C_mul_monomial (a := P.coeff d) (a' := 1) (s := (d : Fin 2 →₀ ℕ))).symm]
              rw [map_mul, map_mul, hC]
              rw [Algebra.smul_def, PowerSeries.algebraMap_eq]
      _ = qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL
          (evalE₄E₆ (∑ d : P.support, monomial d (P.coeff d))) := by simp
      _ = qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL (evalE₄E₆ P) := by
        congr 2
        calc
          (∑ d : P.support, monomial d (P.coeff d)) =
              ∑ d ∈ P.support, monomial d (P.coeff d) :=
            (Finset.sum_subtype (p := fun d ↦ d ∈ P.support) P.support (by simp)
              (fun d ↦ monomial d (P.coeff d))).symm
          _ = P := P.support_sum_monomial_coeff
  obtain ⟨a, ha⟩ := exists_rat_coefficients_of_sum_map_eq v hv c f hsum
  refine ⟨∑ d : P.support, monomial d (a d), ?_⟩
  rw [map_sum]
  calc
    ∑ d : P.support, (monomial d (a d)).map (algebraMap ℚ ℂ) =
        ∑ d : P.support, monomial d (P.coeff d) := by
          apply Finset.sum_congr rfl
          intro d _
          rw [map_monomial]
          congr 1
          exact (congrFun ha d).symm
    _ = P := by
      calc
        (∑ d : P.support, monomial d (P.coeff d)) =
            ∑ d ∈ P.support, monomial d (P.coeff d) :=
          (Finset.sum_subtype (p := fun d ↦ d ∈ P.support) P.support (by simp)
            (fun d ↦ monomial d (P.coeff d))).symm
        _ = P := P.support_sum_monomial_coeff

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
    MvPolynomial (Fin 2) ℚ ≃ₐ[ℚ] ⨁ i, rationalModularForms i :=
  AlgEquiv.ofBijective evalE₄E₆Rat ⟨evalE₄E₆Rat_injective, evalE₄E₆Rat_surjective⟩

/-- The rational modular forms `E₄` and `E₆` generate the graded ring of rational modular
forms as a `ℚ`-algebra. -/
theorem E₄E₆Rat_generate :
    Algebra.adjoin ℚ ({of _ 4 E₄Rat, of _ 6 E₆Rat} : Set (⨁ i, rationalModularForms i)) = ⊤ := by
  sorry

end ModularForm
