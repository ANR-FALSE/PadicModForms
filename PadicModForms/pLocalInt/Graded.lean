/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import PadicModForms.Rational.Graded
public import PadicModForms.pLocalInt.Eisenstein

/-!
# The graded ring of `p`-integral modular forms

This file defines evaluation at the integral Eisenstein series `E₄_int` and `E₆_int` in the
graded ring of modular forms over `pLocalInt p`, and compares it with rational evaluation after
extending scalars to `ℚ`.
-/

@[expose] public noncomputable section

open DirectSum EisensteinSeries MvPolynomial PowerSeries GradedMonoid

namespace ModularForm

variable {p : ℕ} [Fact p.Prime] {n m : ℤ}
  (f : pLocalIntModularForms p n) (g : pLocalIntModularForms p m)

/-- Scalar extension from a `p`-integral modular form of fixed weight to a rational modular form. -/
def pLocalIntModularFormToRat :
    pLocalIntModularForms p n →ₗ[pLocalInt p] rationalModularForms n where
  toFun f := ⟨(f : (pLocalInt p)⟦X⟧).map (algebraMap _ ℚ), by
    obtain ⟨F, hF⟩ := f.2
    rw [hF, rationalQExpansion_apply]
    exact F.2⟩
  map_add' f g := Subtype.ext (by simp)
  map_smul' c f := Subtype.ext <| by
    ext i
    rw [PowerSeries.coeff_map]
    exact (pLocalInt p).subtype.map_mul c _

@[simp]
theorem pLocalIntModularFormToRat_one :
    pLocalIntModularFormToRat (1 : pLocalIntModularForms p 0) = 1 :=
  Subtype.ext (by simp [pLocalIntModularFormToRat])

@[simp]
theorem pLocalIntModularFormToRat_mul :
    pLocalIntModularFormToRat (GMul.mul (A := fun i ↦ pLocalIntModularForms p i) f g) =
      GMul.mul (A := fun i ↦ rationalModularForms i) (pLocalIntModularFormToRat f)
        (pLocalIntModularFormToRat g) :=
  Subtype.ext (by simp [pLocalIntModularFormToRat])

/-- Scalar extension from modular forms of weight `i` over `pLocalInt p` to rational ones. -/
@[simps]
def pLocalIntModularFormsToRatComponent (i : ℤ) :
    pLocalIntModularForms p i →ₗ[pLocalInt p] (⨁ i, rationalModularForms i) where
  toFun f := of (fun i ↦ rationalModularForms i) i (pLocalIntModularFormToRat f)
  map_add' := by intros; simp
  map_smul' := by intros; rw [map_smul, of_smul]; simp

theorem pLocalIntModularFormsToRatComponent_one : pLocalIntModularFormsToRatComponent 0
    (1 : pLocalIntModularForms p 0) = 1 := by
  have hOneRat : GOne.one (A := fun i ↦ rationalModularForms i) = 1 := Subtype.ext (by simp)
  simp [pLocalIntModularFormsToRatComponent, DirectSum.one_def, hOneRat]

theorem pLocalIntModularFormsToRatComponent_mul : pLocalIntModularFormsToRatComponent (n + m)
      (GMul.mul (A := fun i ↦ pLocalIntModularForms p i) f g) =
      pLocalIntModularFormsToRatComponent n f * pLocalIntModularFormsToRatComponent m g := by
  simp [pLocalIntModularFormToRat_mul, of_mul_of]

/-- Scalar extension from the graded ring of `p`-integral modular forms to the graded ring of
rational modular forms. -/
def pLocalIntModularFormsToRat :
    (⨁ i, pLocalIntModularForms p i) →ₐ[pLocalInt p] (⨁ i, rationalModularForms i) :=
  DirectSum.toAlgebra (pLocalInt p) _ pLocalIntModularFormsToRatComponent
    pLocalIntModularFormsToRatComponent_one pLocalIntModularFormsToRatComponent_mul

@[simp]
theorem pLocalIntModularFormsToRat_of :
    pLocalIntModularFormsToRat (of _ n f) = of _ n (pLocalIntModularFormToRat f) := by
  exact DirectSum.toSemiring_of
    (fun i ↦ (pLocalIntModularFormsToRatComponent (p := p) i).toAddMonoidHom)
    pLocalIntModularFormsToRatComponent_one pLocalIntModularFormsToRatComponent_mul n f

/-- Evaluation in the graded ring of `p`-integral modular forms, sending `X₀` to `E₄_int` and
`X₁` to `E₆_int`. -/
def evalE₄E₆Int :
    MvPolynomial (Fin 2) (pLocalInt p) →ₐ[pLocalInt p] ⨁ i, pLocalIntModularForms p i :=
  aeval ![of _ 4 ⟨_, E₄_int_mem_pLocalIntModularForms⟩,
    of _ 6 ⟨_, E₆_int_mem_pLocalIntModularForms⟩]

/-- The scalar-extension square for evaluation at `E₄_int` and `E₆_int` commutes. -/
theorem pLocalIntModularFormsToRat_evalE₄E₆Int (P : MvPolynomial (Fin 2) (pLocalInt p)) :
    pLocalIntModularFormsToRat (evalE₄E₆Int P) = evalE₄E₆Rat (P.map (algebraMap _ ℚ)) := by
  rw [evalE₄E₆Int, comp_aeval_apply, evalE₄E₆Rat, aeval_map_algebraMap]
  congr 2
  funext i
  fin_cases i <;> simp [pLocalIntModularFormToRat, E₄_int_map, E₆_int_map, rationalQExpansion_apply]

theorem evalE₄E₆Int_injective : Function.Injective (evalE₄E₆Int (p := p)) := fun P Q hPQ ↦ by
  refine map_injective (algebraMap _ ℚ) (fun _ _ ↦ Subtype.ext) (evalE₄E₆Rat_injective ?_)
  simp [← pLocalIntModularFormsToRat_evalE₄E₆Int, hPQ]

/-- Evaluation at `E₄_int` and `E₆_int` directly in power series, forgetting the weight. -/
def evalE₄E₆IntSeries : MvPolynomial (Fin 2) (pLocalInt p) →ₐ[pLocalInt p] (pLocalInt p)⟦X⟧ :=
  aeval ![E₄_int, E₆_int]

/-- Forgetting the weight after evaluating at `E₄_int` and `E₆_int` is evaluation in power
series. -/
theorem pLocalIntQExpansionAlgHom_evalE₄E₆Int (P : MvPolynomial (Fin 2) (pLocalInt p)) :
    pLocalIntQExpansionAlgHom (evalE₄E₆Int P) = evalE₄E₆IntSeries P := by
  rw [evalE₄E₆Int, comp_aeval_apply, evalE₄E₆IntSeries]
  congr 2
  funext i
  fin_cases i <;> simp

section

variable {k : ℕ}

@[simp]
theorem evalE₄E₆Int_X_zero : evalE₄E₆Int (MvPolynomial.X 0 : MvPolynomial _ (pLocalInt p)) =
    of _ 4 ⟨_, E₄_int_mem_pLocalIntModularForms⟩ := by
  simp [evalE₄E₆Int]

@[simp]
theorem evalE₄E₆Int_X_one : evalE₄E₆Int (MvPolynomial.X 1 : MvPolynomial _ (pLocalInt p)) =
    of _ 6 ⟨_, E₆_int_mem_pLocalIntModularForms⟩ := by
  simp [evalE₄E₆Int]

theorem evalE₄E₆Int_X_pow_mul (a b : ℕ) :
    evalE₄E₆Int ((MvPolynomial.X 0 : MvPolynomial _ (pLocalInt p)) ^ a * MvPolynomial.X 1 ^ b) =
      (of _ 4 ⟨_, E₄_int_mem_pLocalIntModularForms⟩) ^ a *
      (of _ 6 ⟨_, E₆_int_mem_pLocalIntModularForms⟩) ^ b := by
  simp

theorem weight_E₄E₆_apply (d : Fin 2 →₀ ℕ) : Finsupp.weight E₄E₆Weights d = d 0 * 4 + d 1 * 6 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_two, mul_comm]

private theorem evalE₄E₆Int_X_pow_mul_apply_eq_zero_of_ne (a b : ℕ) {k : ℤ}
    (hk : k ≠ (a * 4 + b * 6 : ℤ)) :
    (evalE₄E₆Int ((MvPolynomial.X 0 : MvPolynomial _ (pLocalInt p)) ^ a * MvPolynomial.X 1 ^ b)) k =
    0 := by
  simpa [ofPow, of_mul_of] using of_eq_of_ne _ _ _ fun heq ↦ hk (by simp_all)

private theorem evalE₄E₆Int_monomial_apply_eq_zero_of_ne (d : Fin 2 →₀ ℕ) (c : pLocalInt p)
    {k : ℤ} (hk : k ≠ (d 0 * 4 + d 1 * 6 : ℤ)) : (evalE₄E₆Int (monomial d c)) k = 0 := by
  rw [monomial_fin_two, mul_assoc, map_mul, algHom_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, DirectSum.smul_apply,
    evalE₄E₆Int_X_pow_mul_apply_eq_zero_of_ne (d 0) (d 1) hk, smul_zero]

/-- Outside its own weight, the evaluation of a weighted-homogeneous polynomial vanishes. -/
theorem evalE₄E₆Int_apply_eq_zero_of_ne {P : MvPolynomial (Fin 2) (pLocalInt p)}
    (hP : IsWeightedHomogeneous E₄E₆Weights P k) {j : ℤ} (hj : j ≠ k) : (evalE₄E₆Int P) j = 0 := by
  rw [← support_sum_monomial_coeff P, map_sum, DirectSum.sum_apply]
  refine Finset.sum_eq_zero fun d hd ↦ evalE₄E₆Int_monomial_apply_eq_zero_of_ne _ _ fun heq ↦ hj ?_
  rw [heq, ← (weight_E₄E₆_apply d).symm.trans (hP (mem_support_iff.mp hd))]
  grind

/-- The evaluation of a weighted-homogeneous polynomial of weight `k` is concentrated in
degree `k`. -/
theorem evalE₄E₆Int_eq_of {P : MvPolynomial (Fin 2) (pLocalInt p)}
    (hP : IsWeightedHomogeneous E₄E₆Weights P k) :
    evalE₄E₆Int P = of _ (k : ℤ) ((evalE₄E₆Int P) (k : ℤ)) := by
  refine DFinsupp.ext fun j ↦ ?_
  rcases eq_or_ne j k with rfl | hj
  · simp
  · rw [of_eq_of_ne _ _ _ hj, evalE₄E₆Int_apply_eq_zero_of_ne hP hj]

/-- Evaluation at `E₄_int` and `E₆_int`, restricted to polynomials that are weighted homogeneous
of weight `k`. -/
def evalE₄E₆IntAtWeight (k : ℕ) :
    E₄E₆WeightedHomogeneous k (pLocalInt p) →ₗ[pLocalInt p] pLocalIntModularForms p k :=
  (component (pLocalInt p) ℤ (fun i ↦ pLocalIntModularForms p i) k).comp
    ((evalE₄E₆Int (p := p)).toLinearMap.comp (E₄E₆WeightedHomogeneous k (pLocalInt p)).subtype)

@[simp]
theorem evalE₄E₆IntAtWeight_apply (P : E₄E₆WeightedHomogeneous k (pLocalInt p)) :
    evalE₄E₆IntAtWeight k P = (evalE₄E₆Int (P : MvPolynomial (Fin 2) (pLocalInt p))) k := rfl

theorem evalE₄E₆Int_eq_of_apply (P : E₄E₆WeightedHomogeneous k (pLocalInt p)) :
    evalE₄E₆Int (P : MvPolynomial (Fin 2) (pLocalInt p)) = of _ (k : ℤ) (evalE₄E₆IntAtWeight k P) :=
  evalE₄E₆Int_eq_of P.property

theorem evalE₄E₆IntAtWeight_injective :
    Function.Injective (evalE₄E₆IntAtWeight (p := p) k) := fun P Q hPQ ↦
  Subtype.ext <| evalE₄E₆Int_injective <| by
    rw [evalE₄E₆Int_eq_of_apply, evalE₄E₆Int_eq_of_apply, hPQ]

/-- Taking the weighted-homogeneous component of weight `k` does not change the degree-`k` part
of the evaluation. -/
theorem evalE₄E₆Int_component_eq (P : MvPolynomial (Fin 2) (pLocalInt p)) (k : ℕ) :
    (evalE₄E₆Int (weightedHomogeneousComponent E₄E₆Weights k P)) (k : ℤ) = (evalE₄E₆Int P) k := by
  set Q := P - weightedHomogeneousComponent E₄E₆Weights k P with hQ
  conv_rhs => rw [show P = weightedHomogeneousComponent E₄E₆Weights k P + Q by simp [hQ], map_add,
    DirectSum.add_apply]
  suffices h : (evalE₄E₆Int Q) k = 0 by rw [h, add_zero]
  rw [← support_sum_monomial_coeff Q, map_sum, DirectSum.sum_apply]
  refine Finset.sum_eq_zero fun d hd ↦
    evalE₄E₆Int_monomial_apply_eq_zero_of_ne _ _ fun heq ↦ mem_support_iff.mp hd ?_
  have hwd : Finsupp.weight E₄E₆Weights d = k := by rw [weight_E₄E₆_apply]; omega
  rw [hQ, coeff_sub, coeff_weightedHomogeneousComponent, if_pos hwd, sub_self]

end

end ModularForm
