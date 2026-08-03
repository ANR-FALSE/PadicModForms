/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.MvPolynomial
public import PadicModForms.ModP.Eisenstein
public import PadicModForms.pLocalInt.Discriminant

/-!
# Evaluation at `E₄` and `E₆` modulo `p`

This file defines evaluation of a polynomial at the reductions of `E₄` and `E₆` modulo `p` and
proves that it is injective on each weighted homogeneous component.

Unlike `evalE₄E₆Int`, the map `evalE₄E₆ModP` forgets the weight: its target is a ring of power
series rather than a graded ring, and it is very far from injective — the whole point of the
mod-`p` theory is that its kernel is nontrivial. Injectivity still holds in one fixed weight,
`evalE₄E₆ModPAtWeight_injective`.
-/

@[expose] public noncomputable section

open DirectSum EisensteinSeries MvPolynomial PowerSeries

namespace ModularForm

variable {p n : ℕ} [Fact p.Prime] (P : E₄E₆WeightedHomogeneous n (pLocalInt p))

/-! ### Evaluation modulo `p` -/

/-- Evaluation at the reductions of `E₄` and `E₆` modulo `p`. Unlike `evalE₄E₆Int` this lands in
power series, so it forgets the weight. -/
def evalE₄E₆ModP : MvPolynomial (Fin 2) (ZMod p) →ₐ[ZMod p] (ZMod p)⟦X⟧ :=
  aeval ![E₄ModP, E₆ModP]

@[simp]
theorem evalE₄E₆ModP_X_zero :
    evalE₄E₆ModP (MvPolynomial.X 0 : MvPolynomial _ (ZMod p)) = E₄ModP := by
  simp [evalE₄E₆ModP]

@[simp]
theorem evalE₄E₆ModP_X_one :
    evalE₄E₆ModP (MvPolynomial.X 1 : MvPolynomial _ (ZMod p)) = E₆ModP := by
  simp [evalE₄E₆ModP]

/-- Reducing coefficients commutes with evaluation at `E₄` and `E₆`. -/
theorem evalE₄E₆ModP_map (P : MvPolynomial (Fin 2) (pLocalInt p)) :
    evalE₄E₆ModP (P.map pLocalInt.toZMod) = (evalE₄E₆IntSeries P).map pLocalInt.toZMod := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [evalE₄E₆ModP, evalE₄E₆IntSeries]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [evalE₄E₆ModP, evalE₄E₆IntSeries, E₄ModP, E₆ModP]

/-! ### Injectivity in one fixed weight -/

/-- The `q`-expansion over `pLocalInt p` of the modular form attached to a weighted homogeneous
polynomial is its evaluation in power series. -/
theorem coe_evalE₄E₆IntAtWeight : (evalE₄E₆IntAtWeight n P : (pLocalInt p)⟦X⟧) =
      evalE₄E₆IntSeries (P : MvPolynomial (Fin 2) (pLocalInt p)) := by
  rw [← pLocalIntQExpansionAlgHom_evalE₄E₆Int, evalE₄E₆Int_eq_of_apply,
    pLocalIntQExpansionAlgHom_of]

/-- Evaluation at `E₄` and `E₆` modulo `p`, restricted to isobaric polynomials of weight `n`. -/
def evalE₄E₆ModPAtWeight (n : ℕ) :
    E₄E₆WeightedHomogeneous n (ZMod p) →ₗ[ZMod p] (ZMod p)⟦X⟧ :=
  evalE₄E₆ModP.toLinearMap.comp (E₄E₆WeightedHomogeneous n (ZMod p)).subtype

@[simp]
theorem evalE₄E₆ModPAtWeight_apply (P : E₄E₆WeightedHomogeneous n (ZMod p)) :
    evalE₄E₆ModPAtWeight n P = evalE₄E₆ModP (P : MvPolynomial (Fin 2) (ZMod p)) := rfl

private theorem eq_zero_of_evalE₄E₆ModP_eq_zero (hp : 5 ≤ p) {F : MvPolynomial (Fin 2) (ZMod p)}
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) (hzero : evalE₄E₆ModP F = 0) : F = 0 := by
  obtain ⟨G, hGhom, hGmap⟩ := exists_map_eq_of_isWeightedHomogeneous pLocalInt.toZMod_surjective hF
  set f : pLocalIntModularForms p n := evalE₄E₆IntAtWeight n ⟨G, hGhom⟩ with hf
  have hdvd m : (p : pLocalInt p) ∣ coeff m (f : (pLocalInt p)⟦X⟧) := by
    refine pLocalInt.dvd_of_toZMod_eq_zero ?_
    suffices (evalE₄E₆IntSeries G).map pLocalInt.toZMod = 0 by
      rw [hf, coe_evalE₄E₆IntAtWeight]
      simpa using congrArg (coeff m) this
    rw [← evalE₄E₆ModP_map, hGmap, hzero]
  obtain ⟨g, hgmem, hpg⟩ :=
    IsPLocalIntModularForm.exists_smul_eq_of_forall_dvd_coeff f.2  pLocalInt.natCast_ne_zero hdvd
  obtain ⟨H, hH⟩ := evalE₄E₆IntAtWeight_surjective hp ⟨g, hgmem⟩
  suffices G = (p : pLocalInt p) • (H : MvPolynomial (Fin 2) (pLocalInt p)) by
    simp [← hGmap, this, MvPolynomial.smul_eq_C_mul, map_mul]
  suffices ⟨G, hGhom⟩ = (p : pLocalInt p) • H by
    simpa using congrArg Subtype.val this
  exact evalE₄E₆IntAtWeight_injective (by simpa [hH, ← hf] using Subtype.ext hpg.symm)

/-- Evaluation modulo `p` is injective on isobaric polynomials of a fixed weight. This is the
mod-`p` analogue of `evalE₄E₆Int_injective`. -/
theorem evalE₄E₆ModPAtWeight_injective (hp : 5 ≤ p) :
    Function.Injective (evalE₄E₆ModPAtWeight (p := p) n) := fun P Q hPQ ↦
  Subtype.ext <| sub_eq_zero.mp <| eq_zero_of_evalE₄E₆ModP_eq_zero hp (sub_mem P.2 Q.2)
  (by rw [map_sub, ← evalE₄E₆ModPAtWeight_apply, ← evalE₄E₆ModPAtWeight_apply, hPQ, sub_self])

theorem evalE₄E₆ModPAtWeight_inj (hp : 5 ≤ p) {P Q : E₄E₆WeightedHomogeneous n (ZMod p)} :
    evalE₄E₆ModPAtWeight n P = evalE₄E₆ModPAtWeight n Q ↔ P = Q :=
  (evalE₄E₆ModPAtWeight_injective hp).eq_iff

end ModularForm
