/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.HomogeneousLocalization
public import PadicModForms.ModP.Weights
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The degree-zero mod-`p` modular forms and their normality

Let `p ≥ 5`. The algebra of mod-`p` modular forms of all weights is graded by `ZMod (p - 1)`,
because multiplication by the Hasse invariant `A = hasseInvPoly hp` identifies the weights `k` and
`k + (p - 1)`. This file defines its degree-zero part `modPWeightZeroForms p`, Serre's `𝓜⁰`: the
evaluations at `E₄`, `E₆` of polynomials supported in weights divisible by `p - 1`.

The key structural fact is that `𝓜⁰` is integrally closed in its fraction field. Through the
dehomogenized evaluation `F / A ^ N ↦ evalE₄E₆ModP F` it is isomorphic to the degree-zero part
`HomogeneousLocalization.Away` of the localization `(ZMod p)[X₀, X₁][A⁻¹]` — injectivity is
Swinnerton-Dyer's kernel theorem together with the vanishing of homogeneous elements of `(A - 1)`,
surjectivity is padding by powers of `A` — and the latter is integrally closed by
`HomogeneousLocalization.Away.isIntegrallyClosed`.

The working form of normality, used for Serre's congruence theorem, is
`ModularForm.mem_modPWeightZeroForms_of_isIntegral`: a power series that is a quotient of two
degree-zero forms and is integral over the degree-zero forms is itself a degree-zero form.

## Main definitions

* `modPWeightZeroForms`: the degree-zero mod-`p` modular forms, as a subalgebra of
  `(ZMod p)⟦X⟧`.
* `ModularForm.weightZeroEvalE₄E₆ModP`: the dehomogenized evaluation
  `F / A ^ N ↦ evalE₄E₆ModP F`.

## Main results

* `ModularForm.exists_isWeightedHomogeneous_of_mem_modPWeightZeroForms`: a degree-zero form is
  the evaluation of a single homogeneous polynomial of weight divisible by `p - 1`.
* `ModularForm.isIntegrallyClosed_modPWeightZeroForms`: `𝓜⁰` is integrally closed.
* `ModularForm.mem_modPWeightZeroForms_of_isIntegral`: the working form of normality.
-/

@[expose] public noncomputable section

open MvPolynomial HomogeneousLocalization
open PowerSeries hiding C X

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {p n : ℕ} [Fact p.Prime] {F : MvPolynomial (Fin 2) (ZMod p)} {f : (ZMod p)⟦X⟧}

/-- The mod-`p` modular forms of degree zero: evaluations at `E₄`, `E₆` of polynomials that are
weighted homogeneous of degree `0` for the grading by `ZMod (p - 1)`, that is, supported in
weights divisible by `p - 1`. This is Serre's `𝓜⁰`. -/
def modPWeightZeroForms (p : ℕ) [Fact p.Prime] : Subalgebra (ZMod p) (ZMod p)⟦X⟧ where
  carrier := {f | ∃ F, IsWeightedHomogeneous (ModularForm.E₄E₆WeightsModPSubOne p) F 0 ∧
    ModularForm.evalE₄E₆ModP F = f}
  mul_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  zero_mem' := by sorry
  algebraMap_mem' := by sorry

@[simp]
theorem mem_modPWeightZeroForms : f ∈ modPWeightZeroForms p ↔
    ∃ F, IsWeightedHomogeneous (ModularForm.E₄E₆WeightsModPSubOne p) F 0 ∧
      ModularForm.evalE₄E₆ModP F = f :=
  .rfl

namespace ModularForm

/-! ### Membership -/

/-- The evaluation of a weighted homogeneous polynomial of weight divisible by `p - 1` has degree
zero. -/
theorem mem_modPWeightZeroForms_of_isWeightedHomogeneous (hn : p - 1 ∣ n)
    (hF : IsWeightedHomogeneous E₄E₆Weights F n) :
    evalE₄E₆ModP F ∈ modPWeightZeroForms p := by
  sorry

/-- A mod-`p` modular form of weight divisible by `p - 1` has degree zero. -/
theorem mem_modPWeightZeroForms_of_mem_modPModularForms (hp : 5 ≤ p) (hn : p - 1 ∣ n)
    (hf : f ∈ modPModularForms p n) : f ∈ modPWeightZeroForms p := by
  sorry

/-- A degree-zero form is the evaluation of a *single-weight* homogeneous polynomial, of weight
divisible by `p - 1`: pad the components of smaller weight with powers of the Hasse invariant. -/
theorem exists_isWeightedHomogeneous_of_mem_modPWeightZeroForms (hp : 5 ≤ p)
    (hf : f ∈ modPWeightZeroForms p) : ∃ n F, p - 1 ∣ n ∧
      IsWeightedHomogeneous E₄E₆Weights F n ∧ evalE₄E₆ModP F = f := by
  sorry

/-! ### The dehomogenized evaluation -/

/-- The dehomogenized evaluation, from the degree-zero part of the localization of
`(ZMod p)[X₀, X₁]` away from the Hasse invariant, sending `F / A ^ N` to `evalE₄E₆ModP F`. It is
obtained by localizing `evalE₄E₆ModP`, which sends the Hasse invariant to the unit `1`. -/
def weightZeroEvalE₄E₆ModP (hp : 5 ≤ p) :
    HomogeneousLocalization.Away (weightedHomogeneousSubmodule (ZMod p) E₄E₆Weights)
      (hasseInvPoly hp) →+* (ZMod p)⟦X⟧ :=
  (Localization.awayLift evalE₄E₆ModP.toRingHom (hasseInvPoly hp)
    (by simp [evalE₄E₆ModP_hasseInvPoly hp])).comp
    (algebraMap _ (Localization.Away (hasseInvPoly hp)))

@[simp]
theorem weightZeroEvalE₄E₆ModP_mk (hp : 5 ≤ p) {N : ℕ}
    (hA : hasseInvPoly hp ∈ weightedHomogeneousSubmodule (ZMod p) E₄E₆Weights (p - 1))
    (hF : F ∈ weightedHomogeneousSubmodule (ZMod p) E₄E₆Weights (N • (p - 1))) :
    weightZeroEvalE₄E₆ModP hp (HomogeneousLocalization.Away.mk _ hA N F hF) =
      evalE₄E₆ModP F := by
  sorry

/-- The dehomogenized evaluation is injective: a homogeneous polynomial whose evaluation vanishes
lies in `(A - 1)` by the kernel theorem, hence vanishes. -/
theorem injective_weightZeroEvalE₄E₆ModP (hp : 5 ≤ p) :
    Function.Injective (weightZeroEvalE₄E₆ModP hp) := by
  sorry

/-- The range of the dehomogenized evaluation is exactly the degree-zero forms: grouping a
degree-zero polynomial by actual weights `n_j (p - 1)` and padding with powers of the Hasse
invariant realizes its evaluation as the image of a single fraction `F / A ^ N`. -/
theorem range_weightZeroEvalE₄E₆ModP (hp : 5 ≤ p) :
    (weightZeroEvalE₄E₆ModP hp).range = (modPWeightZeroForms p).toSubring := by
  sorry

/-! ### Normality -/

/-- **Normality of the degree-zero mod-`p` modular forms**: through the dehomogenized evaluation,
`𝓜⁰` is isomorphic to the degree-zero part of `(ZMod p)[X₀, X₁][A⁻¹]`, which is integrally closed
by `HomogeneousLocalization.Away.isIntegrallyClosed`. -/
theorem isIntegrallyClosed_modPWeightZeroForms (hp : 5 ≤ p) :
    IsIntegrallyClosed (modPWeightZeroForms p) := by
  sorry

/-- **The working form of normality**: a power series that is a quotient `f = u / w` of two
degree-zero forms and is integral over the degree-zero forms is itself a degree-zero form. This
is the only consequence of normality used in Serre's congruence theorem. -/
theorem mem_modPWeightZeroForms_of_isIntegral (hp : 5 ≤ p) {f u w : (ZMod p)⟦X⟧}
    (hu : u ∈ modPWeightZeroForms p) (hw : w ∈ modPWeightZeroForms p) (hw0 : w ≠ 0)
    (hf : w * f = u) (hint : IsIntegral (modPWeightZeroForms p) f) :
    f ∈ modPWeightZeroForms p := by
  sorry

end ModularForm
