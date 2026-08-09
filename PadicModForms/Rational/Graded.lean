/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.RingTheory.MvPolynomial.Tower
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

import PadicModForms.ForMathlib.DirectSum
import PadicModForms.ForMathlib.MvPolynomial
import PadicModForms.ForMathlib.«38813»
public import PadicModForms.Rational.Eisenstein

/-!
# The graded ring of rational modular forms

This file identifies the graded ring of rational level-one modular forms with `ℚ[E₄, E₆]`.

## Main results

* `rationalModularFormsEquivMvPolynomial`: `ℚ[X₀, X₁] ≃ₐ[ℚ] ⨁ i, rationalModularForms i`.
* `E₄E₆Rat_generate`: `E₄` and `E₆` generate the graded ring as a `ℚ`-algebra.
-/

noncomputable section

open UpperHalfPlane MatrixGroups EisensteinSeries DirectSum MvPolynomial Module Submodule

open scoped PowerSeries

namespace ModularForm

variable {n m : ℤ}

/-!
### The graded ring of complex modular forms as a scalar extension

None of this is needed to define `evalE₄E₆Rat`; it provides the algebra map
`rationalModularFormsToComplex` used to compare the rational and complex sides.
-/

section GradedMonoid

open GradedMonoid

variable (f : rationalModularForms n) (g : rationalModularForms m)

@[simp]
theorem rationalModularFormToComplex_one :
    rationalModularFormToComplex 1 = (1 : ModularForm 𝒮ℒ 0) :=
  (qExpansion_inj one_pos one_mem_strictPeriods_SL).1 (by simp [qExpansion_one 1])

@[simp]
theorem rationalModularFormToComplex_mul :
    rationalModularFormToComplex (GMul.mul (A := fun n ↦ rationalModularForms n) f g) =
      (rationalModularFormToComplex f).mul (rationalModularFormToComplex g) := by
  refine (qExpansion_inj one_pos one_mem_strictPeriods_SL).1 ?_
  simpa using (ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL
    (rationalModularFormToComplex f) (rationalModularFormToComplex g)).symm

theorem rationalModularFormsToComplex_gOne : of _ 0 (rationalModularFormToComplex 1) = 1 := by
  simp

theorem rationalModularFormsToComplex_gMul : of _ (n + m) (rationalModularFormToComplex
    (GMul.mul (A := fun k ↦ rationalModularForms k) f g)) =
      of _ n (rationalModularFormToComplex f) * of _ m (rationalModularFormToComplex g) := by
  rw [rationalModularFormToComplex_mul, of_mul_of]
  exact congrArg (of (ModularForm 𝒮ℒ) (n + m)) rfl

/-- The underlying ring homomorphism for scalar extension from rational to complex modular forms. -/
@[simps!]
def rationalModularFormsToComplexRingHom :
    (⨁ i, rationalModularForms i) →+* (⨁ k, ModularForm 𝒮ℒ k) :=
  toSemiring (fun m ↦ (of _ m).comp (rationalModularFormToComplex).toAddMonoidHom)
    rationalModularFormsToComplex_gOne rationalModularFormsToComplex_gMul

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

end GradedMonoid

/-! ### Evaluation at `E₄` and `E₆` -/

/-- Evaluation in the graded ring of rational modular forms, sending `X₀` to `E₄` and `X₁`
to `E₆`. -/
@[expose] public def evalE₄E₆Rat : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] ⨁ i, rationalModularForms i :=
  aeval ![of _ _ E₄Rat, of _ _ E₆Rat]

/-- The scalar-extension square for evaluation at `E₄` and `E₆` commutes. -/
theorem rationalModularFormsToComplex_evalE₄E₆Rat (P : MvPolynomial (Fin 2) ℚ) :
    rationalModularFormsToComplex (evalE₄E₆Rat P) = evalE₄E₆ (P.map (algebraMap ℚ ℂ)) := by
  rw [evalE₄E₆Rat, comp_aeval_apply, evalE₄E₆, aeval_map_algebraMap]
  congr 2
  funext i
  fin_cases i <;> simp

public theorem evalE₄E₆Rat_injective : Function.Injective evalE₄E₆Rat := fun P Q hPQ ↦ by
  refine map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective (evalE₄E₆_injective ?_)
  simp [← rationalModularFormsToComplex_evalE₄E₆Rat, hPQ]

/-! ### The weight grading on `R[X₀, X₁]` -/

/-- The weights `(4, 6)` of `E₄` and `E₆`, used to grade `R[X₀, X₁]` by modular weight. -/
public abbrev E₄E₆Weights : Fin 2 → ℕ := ![4, 6]

public theorem E₄E₆Weights_ne_zero (i : Fin 2) : E₄E₆Weights i ≠ 0 := by fin_cases i <;> simp

variable (k : ℕ)

/-- The monomials in `X₀, X₁` of weight `k` for the weights `E₄E₆Weights`. -/
abbrev E₄E₆WeightedMonomials := {d : Fin 2 →₀ ℕ // Finsupp.weight E₄E₆Weights d = k}

/-- The polynomials in `X₀, X₁` that are weighted homogeneous of weight `k` for the weights
`E₄E₆Weights`, that is, the weighted homogeneous polynomials of modular weight `k`. -/
public abbrev E₄E₆WeightedHomogeneous (R : Type*) [CommSemiring R] :=
  weightedHomogeneousSubmodule R E₄E₆Weights k

/-- The weighted homogeneous polynomials of weight `k` are free on the monomials of weight `k`. -/
noncomputable def E₄E₆WeightedMonomialBasis (R : Type*) [Field R] :
    Basis (E₄E₆WeightedMonomials k) R (E₄E₆WeightedHomogeneous k R) :=
  (basisRestrictSupport R {d | Finsupp.weight E₄E₆Weights d = k}).map
    (.ofEq _ _ (weightedHomogeneousSubmodule_eq_finsupp_supported R _ k).symm)

/-- Evaluation at `E₄` and `E₆`, restricted to weighted homogeneous polynomials of weight `k`. -/
noncomputable def evalE₄E₆AtWeight : E₄E₆WeightedHomogeneous k ℂ →ₗ[ℂ] ModularForm 𝒮ℒ k :=
  (component ℂ ℤ (fun k ↦ ModularForm 𝒮ℒ k) k).comp
    (evalE₄E₆.toLinearMap.comp (E₄E₆WeightedHomogeneous k ℂ).subtype)

@[simp]
theorem evalE₄E₆AtWeight_apply (p : E₄E₆WeightedHomogeneous k ℂ) :
    evalE₄E₆AtWeight k p = (evalE₄E₆ p) k := rfl

theorem evalE₄E₆AtWeight_injective : Function.Injective (evalE₄E₆AtWeight k) := fun p q hpq ↦ by
  refine Subtype.ext (evalE₄E₆_injective ?_)
  rw [evalE₄E₆_eq_of_apply k p p.property, evalE₄E₆_eq_of_apply k q q.property,
    show (evalE₄E₆ p) k = (evalE₄E₆ q) k by exact hpq]

theorem evalE₄E₆AtWeight_surjective : Function.Surjective (evalE₄E₆AtWeight k) := by
  intro f
  obtain ⟨p, hp⟩ := evalE₄E₆_surjective (.of _ (k : ℤ) f)
  refine ⟨⟨_, weightedHomogeneousComponent_isWeightedHomogeneous k p⟩, ?_⟩
  simpa [evalE₄E₆AtWeight_apply, evalE₄E₆_component_eq] using congrArg (fun F ↦ F k) hp

/-- The complex modular forms of weight `k` are exactly the weighted homogeneous polynomials of
weight `k` in `E₄` and `E₆`. -/
noncomputable def evalE₄E₆AtWeightEquiv : E₄E₆WeightedHomogeneous k ℂ ≃ₗ[ℂ] ModularForm 𝒮ℒ k :=
  .ofBijective _ ⟨evalE₄E₆AtWeight_injective k, evalE₄E₆AtWeight_surjective k⟩

theorem isWeightedHomogeneous_map_rat {k} {p : MvPolynomial (Fin 2) ℚ}
    (hp : IsWeightedHomogeneous E₄E₆Weights p k) :
    IsWeightedHomogeneous E₄E₆Weights (p.map (algebraMap ℚ ℂ)) k :=
  fun d hd ↦ hp (fun hzero ↦ hd <| by simp [coeff_map, hzero])

/-- Evaluation at `E₄` and `E₆` over `ℚ`, restricted to weighted homogeneous polynomials of
weight `k`. -/
noncomputable def evalE₄E₆RatAtWeight : E₄E₆WeightedHomogeneous k ℚ →ₗ[ℚ] rationalModularForms k :=
  (DirectSum.component ℚ ℤ (fun k ↦ rationalModularForms k) k).comp
    (evalE₄E₆Rat.toLinearMap.comp (E₄E₆WeightedHomogeneous k ℚ).subtype)

@[simp]
theorem evalE₄E₆RatAtWeight_apply (p : E₄E₆WeightedHomogeneous k ℚ) :
    evalE₄E₆RatAtWeight k p = (evalE₄E₆Rat p) k := rfl

/-! ### Monomial bases -/

/-- The weighted-homogeneous monomial basis consists of the monomials themselves. -/
theorem coe_E₄E₆WeightedMonomialBasis (R : Type*) [Field R] (d : E₄E₆WeightedMonomials k) :
    (E₄E₆WeightedMonomialBasis k R d : MvPolynomial (Fin 2) R) = monomial (d : Fin 2 →₀ ℕ) 1 := by
  rw [E₄E₆WeightedMonomialBasis, Basis.map_apply]
  exact basisRestrictSupport_apply_coe _ _

/-- The `ℂ`-basis of the complex modular forms of weight `k` given by the monomials in `E₄`
and `E₆`. -/
def complexMonomialBasis : Basis (E₄E₆WeightedMonomials k) ℂ (ModularForm 𝒮ℒ k) :=
  (E₄E₆WeightedMonomialBasis k ℂ).map (evalE₄E₆AtWeightEquiv k)

@[simp]
theorem complexMonomialBasis_apply (d : E₄E₆WeightedMonomials k) :
    complexMonomialBasis k d = evalE₄E₆AtWeight k (E₄E₆WeightedMonomialBasis k ℂ d) := rfl

/-- The rational modular form of weight `k` given by the monomial `d` in `E₄` and `E₆`. -/
def ratMonomial (d : E₄E₆WeightedMonomials k) : rationalModularForms k :=
  evalE₄E₆RatAtWeight k (E₄E₆WeightedMonomialBasis k ℚ d)

/-- Each complex monomial in `E₄` and `E₆` is the scalar extension of the corresponding rational
one. -/
theorem complexMonomialBasis_eq :
    (complexMonomialBasis k) = rationalModularFormToComplex ∘ ratMonomial k := by
  funext d
  have hsq := congrArg (fun F ↦ F k) (rationalModularFormsToComplex_evalE₄E₆Rat
    (E₄E₆WeightedMonomialBasis k ℚ d : MvPolynomial (Fin 2) ℚ))
  simp only [rationalModularFormsToComplex_apply] at hsq
  rw [Function.comp_apply, ratMonomial, evalE₄E₆RatAtWeight_apply, hsq,
    coe_E₄E₆WeightedMonomialBasis, map_monomial, map_one, complexMonomialBasis_apply,
    evalE₄E₆AtWeight_apply, coe_E₄E₆WeightedMonomialBasis]

/-- The `ℚ`-basis of `rationalModularForms k` given by the monomials in `E₄` and `E₆`, obtained by
descending `complexMonomialBasis k` along scalar extension. -/
noncomputable def ratMonomialBasis : Basis (E₄E₆WeightedMonomials k) ℚ (rationalModularForms k) :=
  basisOfComplexBasis (ratMonomial k) (complexMonomialBasis k) (complexMonomialBasis_eq k)

@[simp]
theorem ratMonomialBasis_apply (d : E₄E₆WeightedMonomials k) :
    ratMonomialBasis k d = ratMonomial k d := by
  simp [ratMonomialBasis]

theorem evalE₄E₆RatAtWeight_surjective :
    Function.Surjective (evalE₄E₆RatAtWeight k) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← (ratMonomialBasis k).span_eq, span_le]
  rintro _ ⟨d, rfl⟩
  exact ⟨E₄E₆WeightedMonomialBasis k ℚ d, (ratMonomialBasis_apply k d).symm⟩

theorem evalE₄E₆Rat_eq_of_apply (p : E₄E₆WeightedHomogeneous k ℚ) :
    evalE₄E₆Rat p = DirectSum.of (fun k ↦ rationalModularForms k) k (evalE₄E₆RatAtWeight k p) := by
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

/-! ### The structure theorem -/

theorem evalE₄E₆Rat_surjective : Function.Surjective evalE₄E₆Rat := fun F ↦ by
  induction F using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of k f =>
      by_cases hk : k < 0
      · have hf : f = 0 := Subtype.ext (by simpa [rationalModularForms_eq_bot_of_neg hk] using f.2)
        exact ⟨0, by simp [hf]⟩
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n := ⟨k.toNat, by lia⟩
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
  .ofBijective evalE₄E₆Rat ⟨evalE₄E₆Rat_injective, evalE₄E₆Rat_surjective⟩

theorem rationalQExpansionAlgHom_evalE₄E₆Rat (P : MvPolynomial (Fin 2) ℚ) :
    rationalQExpansionAlgHom (evalE₄E₆Rat P) =
      aeval ![(E₄Rat : ℚ⟦X⟧), (E₆Rat : ℚ⟦X⟧)] P := by
  rw [evalE₄E₆Rat, comp_aeval_apply]
  congr 2
  funext i
  fin_cases i <;> simp

/-- The `q`-expansion of a rational modular form of any weight is a polynomial in the
`q`-expansions of `E₄` and `E₆`. -/
public theorem exists_qExpansion_eq_aeval (F : rationalModularForms n) :
    ∃ P : MvPolynomial _ ℚ, (F : ℚ⟦X⟧) = aeval ![(E₄Rat : ℚ⟦X⟧), (E₆Rat : ℚ⟦X⟧)] P := by
  obtain ⟨P, hP⟩ := evalE₄E₆Rat_surjective (of _ n F)
  exact ⟨P, by rw [← rationalQExpansionAlgHom_evalE₄E₆Rat, hP, rationalQExpansionAlgHom_of]⟩

/-- The rational modular forms `E₄` and `E₆` generate the graded ring of rational modular
forms as a `ℚ`-algebra. -/
theorem E₄E₆Rat_generate :
    Algebra.adjoin ℚ ({of _ 4 E₄Rat, of _ 6 E₆Rat} : Set (⨁ i, rationalModularForms i)) = ⊤ := by
  rw [show ({of _ 4 E₄Rat, of _ 6 E₆Rat} : Set (⨁ i, rationalModularForms i)) =
    Set.range ![of _ 4 E₄Rat, of _ 6 E₆Rat] by ext x; simp [or_comm], ← aeval_range, ← evalE₄E₆Rat]
  exact (AlgHom.range_eq_top evalE₄E₆Rat).mpr evalE₄E₆Rat_surjective

end ModularForm
