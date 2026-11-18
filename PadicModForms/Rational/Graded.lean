/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import PadicModForms.Rational.Eisenstein

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.QExpansionInjective

/-!
# The graded ring of rational modular forms

This file identifies the graded ring of rational level-one modular forms with `ℚ[E₄, E₆]`.

## Main results

* `rationalModularFormsEquivMvPolynomial`: `ℚ[X₀, X₁] ≃ₐ[ℚ] ⨁ i, rationalModularForms i`.
* `E₄E₆Rat_generate`: `E₄` and `E₆` generate the graded ring as a `ℚ`-algebra.
-/

noncomputable section

open UpperHalfPlane MatrixGroups EisensteinSeries DirectSum MvPolynomial PowerSeries

namespace ModularForm

variable {n : ℤ}

/-! ### Evaluation at `E₄` and `E₆` -/

/-- Evaluation in the graded ring of rational modular forms, sending `X₀` to `E₄` and `X₁`
to `E₆`. -/
@[expose] public def evalE₄E₆Rat : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] ⨁ i, rationalModularForms i :=
  aeval ![of _ _ E₄Rat, of _ _ E₆Rat]

theorem rationalQExpansionAlgHom_evalE₄E₆Rat (P : MvPolynomial (Fin 2) ℚ) :
    rationalQExpansionAlgHom (evalE₄E₆Rat P) = aeval ![(E₄Rat : ℚ⟦X⟧), (E₆Rat : ℚ⟦X⟧)] P := by
  rw [evalE₄E₆Rat, comp_aeval_apply]
  congr 2
  funext i
  fin_cases i <;> simp

theorem qExpansionAlgHom_evalE₄E₆_map (P : MvPolynomial (Fin 2) ℚ) :
    qExpansionAlgHom 1 one_pos one_mem_strictPeriods_SL (evalE₄E₆ (P.map (algebraMap ℚ ℂ))) =
      (rationalQExpansionAlgHom (evalE₄E₆Rat P)).map (algebraMap ℚ ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [evalE₄E₆Rat]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => fin_cases i <;> simp [hP, evalE₄E₆Rat, E₄Rat_map_complex, E₆Rat_map_complex]

/-- The `q`-expansions `E₄Rat` and `E₆Rat` are algebraically independent over `ℚ` in `ℚ⟦X⟧`:
evaluating a polynomial at them is injective. -/
public theorem aeval_E₄Rat_E₆Rat_injective :
    Function.Injective (aeval (R := ℚ) ![(E₄Rat : ℚ⟦X⟧), (E₆Rat : ℚ⟦X⟧)]) := fun P Q hPQ ↦ by
  refine map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective <| evalE₄E₆_injective <|
    qExpansionAlgHom_injective one_pos one_mem_strictPeriods_SL ?_
  simp [qExpansionAlgHom_evalE₄E₆_map, rationalQExpansionAlgHom_evalE₄E₆Rat, hPQ]

public theorem evalE₄E₆Rat_injective : Function.Injective evalE₄E₆Rat :=
  .of_comp (f := rationalQExpansionAlgHom) <| by
    simpa [Function.comp_def, rationalQExpansionAlgHom_evalE₄E₆Rat] using
      aeval_E₄Rat_E₆Rat_injective

/-! ### The weight grading on `R[X₀, X₁]` -/

/-- The weight function on the two variables of `MvPolynomial (Fin 2) R`, giving `X₀` the weight
`4` of `E₄` and `X₁` the weight `6` of `E₆`. A polynomial that is weighted homogeneous of weight `k`
for these weights evaluates at `X₀ = E₄`, `X₁ = E₆` to a modular form of weight `k`. -/
public abbrev E₄E₆Weights : Fin 2 → ℕ := ![4, 6]

public theorem E₄E₆Weights_ne_zero (i : Fin 2) : E₄E₆Weights i ≠ 0 := by fin_cases i <;> simp

/-- The polynomials in `X₀, X₁` that are weighted homogeneous of weight `k` for the weights
`E₄E₆Weights`, that is, the weighted homogeneous polynomials of modular weight `k`. -/
public abbrev E₄E₆WeightedHomogeneous (k : ℕ) (R : Type*) [CommSemiring R] :=
  weightedHomogeneousSubmodule R E₄E₆Weights k

/-- Evaluation at `E₄` and `E₆` over `ℚ`, restricted to weighted homogeneous polynomials of
weight `k`. -/
public noncomputable def evalE₄E₆RatAtWeight (k : ℕ) :
    E₄E₆WeightedHomogeneous k ℚ →ₗ[ℚ] rationalModularForms k :=
  (DirectSum.component ℚ ℤ (fun k ↦ rationalModularForms k) k).comp
    (evalE₄E₆Rat.toLinearMap.comp (E₄E₆WeightedHomogeneous k ℚ).subtype)

/-! ### The structure theorem -/

theorem evalE₄E₆Rat_surjective : Function.Surjective evalE₄E₆Rat := fun F ↦ by
  obtain ⟨P, hP⟩ := evalE₄E₆_surjective
    (DirectSum.map (fun _ ↦ rationalModularFormToComplex.toAddMonoidHom) F)
  let π : ℂ →ₗ[ℚ] ℚ := (Algebra.linearMap ℚ ℂ).leftInverse
  have hπ (q : ℚ) : π (algebraMap ℚ ℂ q) = q :=
    (Algebra.linearMap ℚ ℂ).leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.2 (algebraMap ℚ ℂ).injective) q
  refine ⟨∑ d ∈ P.support, π (P.coeff d) • monomial d 1, rationalQExpansionAlgHom_injective ?_⟩
  have hP' := congr(qExpansionAlgHom 1 one_pos one_mem_strictPeriods_SL $hP)
  have hPsum : P = ∑ d ∈ P.support,
      P.coeff d • (monomial d 1 : MvPolynomial (Fin 2) ℚ).map (algebraMap ℚ ℂ) := by
    simp [smul_monomial]
  rw [qExpansionAlgHom_map_rationalModularFormToComplex, hPsum] at hP'
  simp only [map_sum, map_smul, qExpansionAlgHom_evalE₄E₆_map] at hP'
  ext m
  have hm := congr(π (PowerSeries.coeff m $hP'))
  simp only [map_sum, map_smul, PowerSeries.coeff_map, hπ, smul_eq_mul] at hm ⊢
  rw [← hm]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [mul_comm (P.coeff d), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- The graded ring of rational level-one modular forms is isomorphic to `ℚ[X₀, X₁]`. -/
public def rationalModularFormsEquivMvPolynomial :
    MvPolynomial (Fin 2) ℚ ≃ₐ[ℚ] ⨁ i, rationalModularForms i :=
  .ofBijective evalE₄E₆Rat ⟨evalE₄E₆Rat_injective, evalE₄E₆Rat_surjective⟩

/-- The `q`-expansion of a rational modular form of any weight is a polynomial in the
`q`-expansions of `E₄` and `E₆`. -/
public theorem exists_qExpansion_eq_aeval (F : rationalModularForms n) :
    ∃ P : MvPolynomial _ ℚ, (F : ℚ⟦X⟧) = aeval ![(E₄Rat : ℚ⟦X⟧), (E₆Rat : ℚ⟦X⟧)] P := by
  obtain ⟨P, hP⟩ := evalE₄E₆Rat_surjective (of _ n F)
  exact ⟨P, by rw [← rationalQExpansionAlgHom_evalE₄E₆Rat, hP, rationalQExpansionAlgHom_of]⟩

/-- The rational modular forms `E₄` and `E₆` generate the graded ring of rational modular
forms as a `ℚ`-algebra. -/
public theorem E₄E₆Rat_generate :
    Algebra.adjoin ℚ ({of _ 4 E₄Rat, of _ 6 E₆Rat} : Set (⨁ i, rationalModularForms i)) = ⊤ := by
  rw [← Matrix.range_cons_cons_empty _ _ ![], Algebra.adjoin_range_eq_range_aeval]
  exact evalE₄E₆Rat.range_eq_top.2 evalE₄E₆Rat_surjective

end ModularForm

end
