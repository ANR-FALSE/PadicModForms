/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.RingTheory.MvPolynomial.Tower

import PadicModForms.ForMathlib.DirectSum
import PadicModForms.ForMathlib.LinearIndependent
import PadicModForms.ForMathlib.«38813»
public import PadicModForms.Rational.Basic

/-!
# The graded ring of rational modular forms

This file develops the graded algebra of rational modular forms and gives the identification with
`ℚ[E₄, E₆]`.
-/

noncomputable section

open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries SetLike DirectSum MvPolynomial

open scoped MatrixGroups PowerSeries

namespace ModularForm

variable {k : ℕ} {n m : ℤ}

/-- Evaluation in the graded ring of rational modular forms, sending `X₀` to `E₄` and `X₁`
to `E₆`. -/
def evalE₄E₆Rat : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] ⨁ i, rationalModularForms i :=
  aeval ![of _ _ E₄Rat, of _ _ E₆Rat]

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

@[simp]
theorem rationalModularForms_gOne_eq_one :
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

theorem rationalModularFormsToComplex_gOne : of _ 0 (rationalModularFormToComplex 1) = 1 := by
  simp

theorem rationalModularFormsToComplex_gMul (g : rationalModularForms m) :
    of _ (n + m) (rationalModularFormToComplex
        (GMul.mul (A := fun k ↦ rationalModularForms k) f g)) =
      of _ n (rationalModularFormToComplex f) * of _ m (rationalModularFormToComplex g) := by
  rw [rationalModularFormToComplex_mul, of_mul_of]
  exact congrArg (of (ModularForm 𝒮ℒ) (n + m)) rfl

/-- The underlying ring homomorphism for scalar extension from rational to complex modular forms. -/
def rationalModularFormsToComplexRingHom :
    (⨁ i, rationalModularForms i) →+* (⨁ k, ModularForm 𝒮ℒ k) :=
  toSemiring (fun m ↦ (of _ m).comp (rationalModularFormToComplex).toAddMonoidHom)
    rationalModularFormsToComplex_gOne rationalModularFormsToComplex_gMul

@[simp]
theorem rationalModularFormsToComplexRingHom_apply (F : ⨁ i, rationalModularForms i) :
    rationalModularFormsToComplexRingHom F =
      DirectSum.toAddMonoid
        (fun m ↦ (of (fun k ↦ ModularForm 𝒮ℒ k) m).comp
          (rationalModularFormToComplex).toAddMonoidHom) F := rfl

@[simp]
theorem rationalModularFormsToComplexRingHom_of :
    rationalModularFormsToComplexRingHom (of _ n f) = of _ n (rationalModularFormToComplex f) :=
  toSemiring_of ..

/-- Scalar extension from the graded ring of rational modular forms to the graded ring of
complex modular forms. -/
def rationalModularFormsToComplex : (⨁ i, rationalModularForms i) →ₐ[ℚ] (⨁ k, ModularForm 𝒮ℒ k) :=
  RingHom.toRatAlgHom rationalModularFormsToComplexRingHom

@[simp]
theorem rationalModularFormsToComplex_of :
    rationalModularFormsToComplex (of _ n f) = of _ n (rationalModularFormToComplex f) :=
  rationalModularFormsToComplexRingHom_of f

@[simp]
theorem rationalModularFormsToComplex_apply (F : ⨁ i, rationalModularForms i) (k : ℤ) :
    (rationalModularFormsToComplex F) k = rationalModularFormToComplex (F k) := by
  simp [rationalModularFormsToComplex]

/-- The rational algebra structure on complex graded modular forms is compatible with its
complex algebra structure. -/
@[simp]
theorem algebraMap_rat_eq_complex (a : ℚ) :
    algebraMap ℚ (⨁ k, ModularForm 𝒮ℒ k) a = algebraMap ℂ (⨁ k, ModularForm 𝒮ℒ k) a :=
  rfl

theorem rationalQExpansion_evalE₄E₆Rat_map_C (a : ℚ) :
    (rationalQExpansionAlgHom (evalE₄E₆Rat (C a))).map (algebraMap ℚ ℂ) =
      qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL
        (evalE₄E₆ ((C a).map (algebraMap ℚ ℂ))) :=
  calc _ = (a : ℂ) • 1 := by simp [Algebra.smul_def]
    _ = (a : ℂ) • qExpansion 1 (1 : ModularForm 𝒮ℒ 0) := by rw [ModularForm.qExpansion_one]
    _ = qExpansion 1 (((a : ℂ) • 1 : ModularForm 𝒮ℒ 0)) :=
      (ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL _ _).symm
    _ = qExpansion 1 (const a : ModularForm 𝒮ℒ 0) := by rw [show const a = (a : ℂ) • 1 by ext; simp]
    _ = _ := by simp [DirectSum.algebraMap_apply]; rfl

theorem rationalQExpansion_evalE₄E₆Rat_map_X0 :
    (rationalQExpansionAlgHom (evalE₄E₆Rat (X 0))).map (algebraMap ℚ ℂ) =
      qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL
        (evalE₄E₆ ((X 0).map (algebraMap ℚ ℂ))) := by
  calc _ = (E₄Rat : ℚ⟦X⟧).map _ := by rw [evalE₄E₆Rat_X0, rationalQExpansionAlgHom_of]
    _ = qExpansion 1 E₄ := ERat_map_complex _ ⟨2, rfl⟩
    _ = _ := by simp

theorem rationalQExpansion_evalE₄E₆Rat_map_X1 :
    (rationalQExpansionAlgHom (evalE₄E₆Rat (X 1))).map (algebraMap ℚ ℂ) =
      qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL
        (evalE₄E₆ ((X 1).map (algebraMap ℚ ℂ))) := by
  calc
    _ = (E₆Rat : ℚ⟦X⟧).map (algebraMap ℚ ℂ) := by
      rw [evalE₄E₆Rat_X1, rationalQExpansionAlgHom_of]
    _ = qExpansion 1 E₆ := ERat_map_complex _ ⟨3, rfl⟩
    _ = _ := by simp

theorem rationalQExpansion_evalE₄E₆Rat_map_X (i : Fin 2) :
    (rationalQExpansionAlgHom (evalE₄E₆Rat (X i))).map (algebraMap ℚ ℂ) =
      qExpansionRingHom 1 one_pos one_mem_strictPeriods_SL
        (evalE₄E₆ ((X i).map (algebraMap ℚ ℂ))) := by
  fin_cases i
  · exact rationalQExpansion_evalE₄E₆Rat_map_X0
  · exact rationalQExpansion_evalE₄E₆Rat_map_X1

theorem rationalQExpansion_evalE₄E₆Rat_map (P : MvPolynomial (Fin 2) ℚ) :
    (rationalQExpansionAlgHom (evalE₄E₆Rat P)).map (algebraMap ℚ ℂ) =
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
def E₄E₆MonomialQExpansion (d : Fin 2 →₀ ℕ) : ℚ⟦X⟧ :=
  (E₄Rat : ℚ⟦X⟧) ^ d 0 * (E₆Rat : ℚ⟦X⟧) ^ d 1

@[simp]
theorem E₄E₆MonomialQExpansion_eq (d : Fin 2 →₀ ℕ) :
    E₄E₆MonomialQExpansion d = (E₄Rat : ℚ⟦X⟧) ^ d 0 * (E₆Rat : ℚ⟦X⟧) ^ d 1 := rfl

/-- Extending a rational monomial `q`-expansion to `ℂ` agrees with evaluating the corresponding
monomial in the complex modular forms `E₄` and `E₆` and taking its `q`-expansion. -/
theorem E₄E₆MonomialQExpansion_map_complex (d : Fin 2 →₀ ℕ) :
    (E₄E₆MonomialQExpansion d).map (algebraMap ℚ ℂ) = qExpansionRingHom 1 one_pos
      one_mem_strictPeriods_SL (evalE₄E₆ (monomial d 1)) :=
  calc _ = (rationalQExpansionAlgHom _).map _ :=
      congrArg (PowerSeries.map _) (by simp [monomial_fin_two])
    _ = qExpansionRingHom 1 one_pos _ _ := rationalQExpansion_evalE₄E₆Rat_map (monomial d 1)
    _ = _ := by simp

/-- The complex scalar extensions of the rational monomial `q`-expansions in `E₄` and `E₆` are
linearly independent. -/
theorem E₄E₆MonomialQExpansion_linearIndependent :
    LinearIndependent ℂ (fun d ↦ (E₄E₆MonomialQExpansion d).map (algebraMap ℚ ℂ)) := by
  let x : Fin 2 → (⨁ k, ModularForm 𝒮ℒ k) := ![of _ 4 E₄, of _ 6 E₆]
  have hx : AlgebraicIndependent ℂ x := by
    simpa [algebraicIndependent_iff_injective_aeval, x, evalE₄E₆] using evalE₄E₆_injective
  convert! hx.linearIndependent_monomials.map'
    (qExpansionLinearMap one_pos one_mem_strictPeriods_SL) <|
      LinearMap.ker_eq_bot_of_injective
      (fun F G hFG ↦ levelOne_qExpansionRingHom_injective (by simpa using hFG))
  ext
  rw [E₄E₆MonomialQExpansion_map_complex, evalE₄E₆]
  simp [x]

theorem evalE₄E₆Rat_injective : Function.Injective evalE₄E₆Rat := fun P Q hPQ ↦ by
  refine map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective (evalE₄E₆_injective ?_)
  simp [← rationalModularFormsToComplex_evalE₄E₆Rat, hPQ]

abbrev E₄E₆Weights : Fin 2 → ℕ := ![4, 6]

abbrev E₄E₆WeightedMonomials (k : ℕ) :=
  {d : Fin 2 →₀ ℕ // Finsupp.weight E₄E₆Weights d = k}

abbrev E₄E₆WeightedHomogeneous (R : Type*) [CommSemiring R] (k : ℕ) :=
  weightedHomogeneousSubmodule R E₄E₆Weights k

noncomputable def E₄E₆WeightedMonomialBasis (R : Type*) [Field R] (k : ℕ) :
    Module.Basis (E₄E₆WeightedMonomials k) R (E₄E₆WeightedHomogeneous R k) :=
  (basisRestrictSupport R {d | Finsupp.weight E₄E₆Weights d = k}).map
    (LinearEquiv.ofEq _ _
      (weightedHomogeneousSubmodule_eq_finsupp_supported R E₄E₆Weights k).symm)

noncomputable instance E₄E₆WeightedHomogeneous_finiteDimensional
    (R : Type*) [Field R] (k : ℕ) :
    FiniteDimensional R (E₄E₆WeightedHomogeneous R k) := by
  rw [FiniteDimensional]
  exact Module.Finite.iff_fg.mpr
    (weightedHomogeneousSubmodule_fg R E₄E₆Weights (by decide) k)

theorem E₄E₆WeightedHomogeneous_finrank_eq (k : ℕ) :
    Module.finrank ℚ (E₄E₆WeightedHomogeneous ℚ k) =
      Module.finrank ℂ (E₄E₆WeightedHomogeneous ℂ k) := by
  letI : Fintype (E₄E₆WeightedMonomials k) :=
    (Finsupp.finite_of_nat_weight_eq E₄E₆Weights (by decide) k).fintype
  rw [Module.finrank_eq_card_basis (E₄E₆WeightedMonomialBasis ℚ k),
    Module.finrank_eq_card_basis (E₄E₆WeightedMonomialBasis ℂ k)]

noncomputable def evalE₄E₆AtWeight (k : ℕ) :
    E₄E₆WeightedHomogeneous ℂ k →ₗ[ℂ] ModularForm 𝒮ℒ k :=
  (DirectSum.component ℂ ℤ (fun k ↦ ModularForm 𝒮ℒ k) k).comp
    (evalE₄E₆.toLinearMap.comp (E₄E₆WeightedHomogeneous ℂ k).subtype)

@[simp]
theorem evalE₄E₆AtWeight_apply (k : ℕ)
    (p : E₄E₆WeightedHomogeneous ℂ k) :
    evalE₄E₆AtWeight k p = (evalE₄E₆ p) k := rfl

theorem evalE₄E₆AtWeight_injective (k : ℕ) :
    Function.Injective (evalE₄E₆AtWeight k) := by
  intro p q hpq
  apply Subtype.ext
  apply evalE₄E₆_injective
  rw [evalE₄E₆_eq_of_apply k p p.property, evalE₄E₆_eq_of_apply k q q.property]
  rw [show (evalE₄E₆ p) k = (evalE₄E₆ q) k by exact hpq]

theorem evalE₄E₆AtWeight_surjective (k : ℕ) :
    Function.Surjective (evalE₄E₆AtWeight k) := by
  intro f
  obtain ⟨p, hp⟩ := evalE₄E₆_surjective (DirectSum.of _ (k : ℤ) f)
  refine ⟨⟨weightedHomogeneousComponent E₄E₆Weights k p,
    weightedHomogeneousComponent_isWeightedHomogeneous k p⟩, ?_⟩
  rw [evalE₄E₆AtWeight_apply, evalE₄E₆_component_eq]
  simpa using congrArg (fun F ↦ F (k : ℤ)) hp

noncomputable def evalE₄E₆AtWeightEquiv (k : ℕ) :
    E₄E₆WeightedHomogeneous ℂ k ≃ₗ[ℂ] ModularForm 𝒮ℒ k :=
  LinearEquiv.ofBijective (evalE₄E₆AtWeight k)
    ⟨evalE₄E₆AtWeight_injective k, evalE₄E₆AtWeight_surjective k⟩

theorem isWeightedHomogeneous_map_rat {k : ℕ} {p : MvPolynomial (Fin 2) ℚ}
    (hp : IsWeightedHomogeneous E₄E₆Weights p k) :
    IsWeightedHomogeneous E₄E₆Weights (p.map (algebraMap ℚ ℂ)) k := by
  intro d hd
  apply hp
  intro hzero
  apply hd
  rw [coeff_map, hzero, map_zero]

noncomputable def evalE₄E₆RatAtWeight (k : ℕ) :
    E₄E₆WeightedHomogeneous ℚ k →ₗ[ℚ] rationalModularForms k :=
  (DirectSum.component ℚ ℤ (fun k ↦ rationalModularForms k) k).comp
    (evalE₄E₆Rat.toLinearMap.comp (E₄E₆WeightedHomogeneous ℚ k).subtype)

@[simp]
theorem evalE₄E₆RatAtWeight_apply (k : ℕ)
    (p : E₄E₆WeightedHomogeneous ℚ k) :
    evalE₄E₆RatAtWeight k p = (evalE₄E₆Rat p) k := rfl

theorem evalE₄E₆RatAtWeight_injective (k : ℕ) :
    Function.Injective (evalE₄E₆RatAtWeight k) := by
  intro p q hpq
  have hp : rationalModularFormToComplex ((evalE₄E₆Rat p) k) =
      (evalE₄E₆ (p.1.map (algebraMap ℚ ℂ))) k := by
    simpa using congrArg (fun F ↦ F (k : ℤ))
      (rationalModularFormsToComplex_evalE₄E₆Rat p)
  have hq : rationalModularFormToComplex ((evalE₄E₆Rat q) k) =
      (evalE₄E₆ (q.1.map (algebraMap ℚ ℂ))) k := by
    simpa using congrArg (fun F ↦ F (k : ℤ))
      (rationalModularFormsToComplex_evalE₄E₆Rat q)
  have hpq' : rationalModularFormToComplex ((evalE₄E₆Rat p) k) =
      rationalModularFormToComplex ((evalE₄E₆Rat q) k) := by
    exact congrArg rationalModularFormToComplex hpq
  have heval :
      evalE₄E₆ (p.1.map (algebraMap ℚ ℂ)) = evalE₄E₆ (q.1.map (algebraMap ℚ ℂ)) := by
    rw [evalE₄E₆_eq_of_apply k _ (isWeightedHomogeneous_map_rat p.property),
      evalE₄E₆_eq_of_apply k _ (isWeightedHomogeneous_map_rat q.property),
      hp.symm.trans (hpq'.trans hq)]
  apply Subtype.ext
  apply MvPolynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  exact evalE₄E₆_injective heval

theorem evalE₄E₆RatAtWeight_surjective (k : ℕ) :
    Function.Surjective (evalE₄E₆RatAtWeight k) := by
  have hinj := evalE₄E₆RatAtWeight_injective k
  have hle : Module.finrank ℚ (E₄E₆WeightedHomogeneous ℚ k) ≤
      Module.finrank ℚ (rationalModularForms k) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have hle' : Module.finrank ℚ (rationalModularForms k) ≤
      Module.finrank ℚ (E₄E₆WeightedHomogeneous ℚ k) := by
    calc
      _ ≤ Module.finrank ℂ (ModularForm 𝒮ℒ k) := rationalModularForms_finrank_le k
      _ = Module.finrank ℂ (E₄E₆WeightedHomogeneous ℂ k) :=
        (evalE₄E₆AtWeightEquiv k).finrank_eq.symm
      _ = _ := (E₄E₆WeightedHomogeneous_finrank_eq k).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (le_antisymm hle hle')).mp hinj

theorem evalE₄E₆Rat_eq_of_apply (k : ℕ)
    (p : E₄E₆WeightedHomogeneous ℚ k) :
    evalE₄E₆Rat p = DirectSum.of (fun k ↦ rationalModularForms k) k
      (evalE₄E₆RatAtWeight k p) := by
  apply DFinsupp.ext
  intro j
  by_cases hj : j = (k : ℤ)
  · subst j
    simp
  · rw [DirectSum.of_eq_of_ne _ _ _ hj]
    apply rationalModularFormToComplex_injective
    have hsquare : rationalModularFormToComplex ((evalE₄E₆Rat p) j) =
        (evalE₄E₆ (p.1.map (algebraMap ℚ ℂ))) j := by
      simpa using congrArg (fun F ↦ F j) (rationalModularFormsToComplex_evalE₄E₆Rat p)
    rw [hsquare, map_zero, evalE₄E₆_eq_of_apply k _
      (isWeightedHomogeneous_map_rat p.property), DirectSum.of_eq_of_ne _ _ _ hj]

/-- Evaluation at `E₄` and `E₆` is surjective onto the graded ring of rational modular forms. -/
theorem evalE₄E₆Rat_surjective :
    Function.Surjective evalE₄E₆Rat := fun F ↦ by
  induction F using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of k f =>
      by_cases hk : k < 0
      · have hfC : rationalModularFormToComplex f = 0 :=
          rank_zero_iff_forall_zero.mp (ModularForm.levelOne_neg_weight_rank_zero hk) _
        have hf : f = 0 := rationalModularFormToComplex_injective (by simpa using hfC)
        exact ⟨0, by simp [hf]⟩
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n := ⟨k.toNat, by omega⟩
        obtain ⟨p, hp⟩ := evalE₄E₆RatAtWeight_surjective n f
        exact ⟨p, (evalE₄E₆Rat_eq_of_apply n p).trans
          (congrArg (DirectSum.of (fun k : ℤ ↦ rationalModularForms k) (n : ℤ)) hp)⟩
  | add F G hF hG =>
      obtain ⟨p, hp⟩ := hF
      obtain ⟨q, hq⟩ := hG
      exact ⟨p + q, by rw [map_add, hp, hq]⟩

/-- The graded ring of rational level-one modular forms is isomorphic to `ℚ[X₀, X₁]`. -/
public def rationalModularFormsEquivMvPolynomial :
    MvPolynomial (Fin 2) ℚ ≃ₐ[ℚ] ⨁ i, rationalModularForms i :=
  AlgEquiv.ofBijective evalE₄E₆Rat ⟨evalE₄E₆Rat_injective, evalE₄E₆Rat_surjective⟩

/-- The rational modular forms `E₄` and `E₆` generate the graded ring of rational modular
forms as a `ℚ`-algebra. -/
theorem E₄E₆Rat_generate :
    Algebra.adjoin ℚ ({of _ 4 E₄Rat, of _ 6 E₆Rat} : Set (⨁ i, rationalModularForms i)) = ⊤ := by
  rw [show ({of _ 4 E₄Rat, of _ 6 E₆Rat} : Set (⨁ i, rationalModularForms i)) =
      Set.range ![of _ 4 E₄Rat, of _ 6 E₆Rat] by ext x; simp [or_comm]]
  rw [← MvPolynomial.aeval_range, ← evalE₄E₆Rat]
  exact (AlgHom.range_eq_top evalE₄E₆Rat).mpr evalE₄E₆Rat_surjective

end ModularForm
