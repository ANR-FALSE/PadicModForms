/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

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
def pLocalIntModularFormsToRatComponent (i : ℤ) :
    pLocalIntModularForms p i →ₗ[pLocalInt p] (⨁ i, rationalModularForms i) where
  toFun f := of (fun i ↦ rationalModularForms i) i (pLocalIntModularFormToRat f)
  map_add' := by intros; simp
  map_smul' := by intros; rw [map_smul, of_smul]; simp

@[simp]
theorem pLocalIntModularFormsToRatComponent_apply : pLocalIntModularFormsToRatComponent n f =
      of (fun i ↦ rationalModularForms i) n (pLocalIntModularFormToRat f) := rfl

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

end ModularForm
