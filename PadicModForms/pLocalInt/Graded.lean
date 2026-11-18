/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.Rational.Graded
public import PadicModForms.pLocalInt.Eisenstein
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.NormNum.Parity

/-!
# The graded ring of `p`-integral modular forms

This file defines evaluation at the integral Eisenstein series `E₄_int` and `E₆_int` in the
graded ring of modular forms over `pLocalInt p`, and compares it with rational evaluation after
extending scalars to `ℚ`.
-/

noncomputable section

open DirectSum EisensteinSeries MvPolynomial PowerSeries

namespace ModularForm

variable {p : ℕ} [Fact p.Prime]

/-! ### Evaluation at `E₄_int` and `E₆_int` -/

/-- Evaluation in the graded ring of `p`-integral modular forms, sending `X₀` to `E₄_int` and
`X₁` to `E₆_int`. -/
@[expose] public def evalE₄E₆Int :
    MvPolynomial (Fin 2) (pLocalInt p) →ₐ[pLocalInt p] ⨁ i, pLocalIntModularForms p i :=
  aeval ![of _ 4 ⟨_, E₄_int_mem_pLocalIntModularForms⟩,
    of _ 6 ⟨_, E₆_int_mem_pLocalIntModularForms⟩]

/-- Evaluation at `E₄_int` and `E₆_int` directly in power series, forgetting the weight. -/
@[expose]
public def evalE₄E₆IntSeries : MvPolynomial (Fin 2) (pLocalInt p) →ₐ[pLocalInt p]
    (pLocalInt p)⟦X⟧ :=
  aeval ![E₄_int, E₆_int]

/-- Forgetting the weight after evaluating at `E₄_int` and `E₆_int` is evaluation in power
series. -/
public theorem pLocalIntQExpansionAlgHom_evalE₄E₆Int (P : MvPolynomial (Fin 2) (pLocalInt p)) :
    pLocalIntQExpansionAlgHom (evalE₄E₆Int P) = evalE₄E₆IntSeries P := by
  rw [evalE₄E₆Int, comp_aeval_apply, evalE₄E₆IntSeries]
  congr 2
  funext i
  fin_cases i <;> simp

theorem evalE₄E₆IntSeries_map (P : MvPolynomial (Fin 2) (pLocalInt p)) :
    (evalE₄E₆IntSeries P).map (algebraMap _ ℚ) =
      aeval ![(E₄Rat : ℚ⟦X⟧), (E₆Rat : ℚ⟦X⟧)] (P.map (algebraMap _ ℚ)) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [evalE₄E₆IntSeries]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, hP]
    fin_cases i <;> simp [evalE₄E₆IntSeries, E₄_int_map, E₆_int_map]

public theorem evalE₄E₆IntSeries_injective :
    Function.Injective (evalE₄E₆IntSeries (p := p)) := fun P Q hPQ ↦
  map_injective _ pLocalInt.algebraMap_injective <| aeval_E₄Rat_E₆Rat_injective <| by
    simp [← evalE₄E₆IntSeries_map, hPQ]

public theorem evalE₄E₆Int_injective : Function.Injective (evalE₄E₆Int (p := p)) :=
  .of_comp (f := pLocalIntQExpansionAlgHom) <| by
    simpa [Function.comp_def, pLocalIntQExpansionAlgHom_evalE₄E₆Int] using
      evalE₄E₆IntSeries_injective

section

variable {k : ℕ}

@[simp]
public theorem evalE₄E₆Int_X_zero : evalE₄E₆Int (MvPolynomial.X 0 : MvPolynomial _ (pLocalInt p)) =
    of _ 4 ⟨_, E₄_int_mem_pLocalIntModularForms⟩ := by
  simp [evalE₄E₆Int]

@[simp]
public theorem evalE₄E₆Int_X_one : evalE₄E₆Int (MvPolynomial.X 1 : MvPolynomial _ (pLocalInt p)) =
    of _ 6 ⟨_, E₆_int_mem_pLocalIntModularForms⟩ := by
  simp [evalE₄E₆Int]

public theorem weight_E₄E₆_apply (d : Fin 2 →₀ ℕ) :
    Finsupp.weight E₄E₆Weights d = d 0 * 4 + d 1 * 6 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_two, mul_comm]

/-- Evaluating a weighted homogeneous polynomial of weight `k` at `E₄_int` and `E₆_int` produces
a `p`-integral modular form of weight `k`. -/
public theorem evalE₄E₆IntSeries_mem {P : MvPolynomial (Fin 2) (pLocalInt p)}
    (hP : IsWeightedHomogeneous E₄E₆Weights P k) :
    evalE₄E₆IntSeries P ∈ pLocalIntModularForms p k := by
  induction hP using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add _ _ _ _ hp hq => rw [map_add]; exact add_mem hp hq
  | monomial d r hr =>
    rw [monomial_fin_two, mul_assoc, C_mul', map_smul, map_mul, map_pow, map_pow]
    refine Submodule.smul_mem _ r ?_
    simp only [evalE₄E₆IntSeries, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact E₄_int_pow_mul_E₆_int_pow_mem (by rw [weight_E₄E₆_apply] at hr; lia)

/-- The evaluation of a weighted homogeneous polynomial of weight `k` is concentrated in
degree `k`. -/
theorem evalE₄E₆Int_eq_of {P : MvPolynomial (Fin 2) (pLocalInt p)}
    (hP : IsWeightedHomogeneous E₄E₆Weights P k) :
    evalE₄E₆Int P = of _ (k : ℤ) ((evalE₄E₆Int P) (k : ℤ)) := by
  have h : evalE₄E₆Int P = of _ (k : ℤ) ⟨evalE₄E₆IntSeries P, evalE₄E₆IntSeries_mem hP⟩ :=
    pLocalIntQExpansionAlgHom_injective (by simp [pLocalIntQExpansionAlgHom_evalE₄E₆Int])
  rw [h, of_eq_same]

/-- Evaluation at `E₄_int` and `E₆_int`, restricted to polynomials that are weighted homogeneous
of weight `k`. -/
@[expose] public def evalE₄E₆IntAtWeight (k : ℕ) :
    E₄E₆WeightedHomogeneous k (pLocalInt p) →ₗ[pLocalInt p] pLocalIntModularForms p k :=
  (component (pLocalInt p) ℤ (fun i ↦ pLocalIntModularForms p i) k).comp
    ((evalE₄E₆Int (p := p)).toLinearMap.comp (E₄E₆WeightedHomogeneous k (pLocalInt p)).subtype)

@[simp]
public theorem evalE₄E₆IntAtWeight_apply (P : E₄E₆WeightedHomogeneous k (pLocalInt p)) :
    evalE₄E₆IntAtWeight k P = (evalE₄E₆Int (P : MvPolynomial (Fin 2) (pLocalInt p))) k := rfl

public theorem evalE₄E₆Int_eq_of_apply (P : E₄E₆WeightedHomogeneous k (pLocalInt p)) :
    evalE₄E₆Int (P : MvPolynomial (Fin 2) (pLocalInt p)) =
      of _ (k : ℤ) (evalE₄E₆IntAtWeight k P) :=
  evalE₄E₆Int_eq_of P.property

public theorem evalE₄E₆IntAtWeight_injective :
    Function.Injective (evalE₄E₆IntAtWeight (p := p) k) := fun P Q hPQ ↦
  Subtype.ext <| evalE₄E₆Int_injective <| by
    rw [evalE₄E₆Int_eq_of_apply, evalE₄E₆Int_eq_of_apply, hPQ]

/-- Taking the weighted homogeneous component of weight `k` does not change the degree-`k` part
of the evaluation. -/
public theorem evalE₄E₆Int_component_eq (P : MvPolynomial (Fin 2) (pLocalInt p)) (k : ℕ) :
    (evalE₄E₆Int (weightedHomogeneousComponent E₄E₆Weights k P)) (k : ℤ) = (evalE₄E₆Int P) k := by
  classical
  conv_rhs =>
    rw [← sum_weightedHomogeneousComponent E₄E₆Weights P,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp P)]
  rw [map_sum, DirectSum.sum_apply, Finset.sum_eq_single k]
  · intro m _ hmk
    rw [evalE₄E₆Int_eq_of (weightedHomogeneousComponent_isWeightedHomogeneous m P),
      of_eq_of_ne _ _ _ (by lia)]
  · intro hk
    rw [(weightedHomogeneousComponent_finsupp P).mem_toFinset, Function.notMem_support] at hk
    simp [hk]

end

end ModularForm

end
