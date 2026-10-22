/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.PAdic.Eisenstein
public import PadicModForms.PAdic.Weights.Defs

/-!
# Classical modular forms as p-adic modular forms

A rational modular form `F` of weight `k` becomes a `p`-adic modular form by extending scalars
from `ℚ` to `ℚ_[p]`: the constant sequence `F, F, …` is a presentation of the resulting power
series (`pAdicModularFormStruct.const`). This file packages the scalar extension as the `ℚ`-linear
map `rationalModularFormToPAdic p : rationalModularForms k →ₗ[ℚ] ℚ_[p]⟦X⟧` and proves its
properties: it is injective, it is the restriction to weight `k` of the `ℚ`-algebra homomorphism
`rationalModularFormsToPAdic p` on the graded ring of rational modular forms, its values are
`p`-adic modular forms and, for `p ≥ 5` and `F ≠ 0`, the `p`-adic weight of its value is `ι k`.

## Main results

* `rationalModularFormToPAdic`: the scalar extension from `ℚ` to `ℚ_[p]` of rational modular forms
  of weight `k`, as a `ℚ`-linear map into `ℚ_[p]⟦X⟧`.
* `rationalModularFormsToPAdic`: the same map on the graded ring, as a `ℚ`-algebra homomorphism.
* `rationalModularFormToPAdic_isPAdicModularForm`: its values are `p`-adic modular forms.
* `w_rationalModularFormToPAdicForm`: for `p ≥ 5`, the `p`-adic weight of the scalar extension of a
  nonzero rational modular form of weight `k` is `ι k`.
-/

@[expose] public noncomputable section

open PowerSeries Filter Topology ModularForm EisensteinSeries DirectSum

variable {p : ℕ} [Fact p.Prime] {k : ℤ}

namespace pAdicModularFormStruct

/-- The constant presentation of the scalar extension of a rational modular form. -/
def const (F : rationalModularForms k) :
    pAdicModularFormStruct ((F : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])) where
  w _ := k
  F _ := F
  tendsTo u hu := by
    filter_upwards with i n
    simpa using refl_mem_uniformity hu

@[simp]
theorem const_w (F : rationalModularForms k) (i : ℕ) : (const (p := p) F).w i = k := rfl

@[simp]
theorem const_F (F : rationalModularForms k) (i : ℕ) : (const (p := p) F).F i = F := rfl

end pAdicModularFormStruct

namespace ModularForm

variable (p)

/-- Extension of scalars from `ℚ` to `ℚ_[p]` of rational modular forms of weight `k`, as a
`ℚ`-linear map into `p`-adic power series. Its values are `p`-adic modular forms
(`rationalModularFormToPAdic_isPAdicModularForm`), of weight `ι k` when nonzero
(`w_rationalModularFormToPAdicForm`). -/
def rationalModularFormToPAdic : rationalModularForms k →ₗ[ℚ] ℚ_[p]⟦X⟧ where
  toFun F := (F : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])
  map_add' F G := by simp
  map_smul' a F := by
    ext n
    simp [Rat.smul_def]

variable {p}

@[simp]
theorem rationalModularFormToPAdic_apply (F : rationalModularForms k) :
    rationalModularFormToPAdic p F = (F : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p]) := rfl

theorem rationalModularFormToPAdic_injective :
    Function.Injective (rationalModularFormToPAdic p (k := k)) := fun _ _ h ↦
  Subtype.ext (map_injective _ (algebraMap ℚ ℚ_[p]).injective h)

@[simp]
theorem rationalModularFormToPAdic_eq_zero_iff {F : rationalModularForms k} :
    rationalModularFormToPAdic p F = 0 ↔ F = 0 :=
  map_eq_zero_iff _ rationalModularFormToPAdic_injective

variable (p)

/-- Extension of scalars from `ℚ` to `ℚ_[p]` on the graded ring of rational modular forms, as a
`ℚ`-algebra homomorphism into `p`-adic power series: the `q`-expansion map followed by the
extension of scalars. On the forms of weight `k` it is `rationalModularFormToPAdic`
(`rationalModularFormsToPAdic_of`). -/
def rationalModularFormsToPAdic : (⨁ i, rationalModularForms i) →ₐ[ℚ] ℚ_[p]⟦X⟧ :=
  (mapAlgHom (Algebra.ofId ℚ ℚ_[p])).comp rationalQExpansionAlgHom

variable {p}

@[simp]
theorem rationalModularFormsToPAdic_of (F : rationalModularForms k) :
    rationalModularFormsToPAdic p (of _ k F) = rationalModularFormToPAdic p F := by
  simp [rationalModularFormsToPAdic, mapAlgHom_apply]

@[simp]
theorem rationalModularFormToPAdic_E₄Rat : rationalModularFormToPAdic p E₄Rat = E₄PAdic := by
  simp [E₄PAdic]

@[simp]
theorem rationalModularFormToPAdic_E₆Rat : rationalModularFormToPAdic p E₆Rat = E₆PAdic := by
  simp [E₆PAdic]

/-- The scalar extension of a rational modular form is a `p`-adic modular form. -/
theorem rationalModularFormToPAdic_isPAdicModularForm (F : rationalModularForms k) :
    (rationalModularFormToPAdic p F).isPAdicModularForm p :=
  ⟨.const F⟩

/-- Extension of scalars from `ℚ` to `ℚ_[p]`, with values in the type of `p`-adic modular
forms. -/
def rationalModularFormToPAdicForm (p : ℕ) [Fact p.Prime] (F : rationalModularForms k) :
    PAdicModularForms p :=
  ⟨rationalModularFormToPAdic p F, rationalModularFormToPAdic_isPAdicModularForm F⟩

@[simp]
theorem rationalModularFormToPAdicForm_val (F : rationalModularForms k) :
    (rationalModularFormToPAdicForm p F).1 = rationalModularFormToPAdic p F := rfl

theorem rationalModularFormToPAdicForm_injective :
    Function.Injective (rationalModularFormToPAdicForm p (k := k)) := fun _ _ h ↦
  rationalModularFormToPAdic_injective congr(($h).1)

theorem rationalModularFormToPAdicForm_eq_zero_iff {F : rationalModularForms k} :
    rationalModularFormToPAdicForm p F = 0 ↔ F = 0 := by
  rw [← PAdicModularForms.val_eq_zero_iff, rationalModularFormToPAdicForm_val,
    rationalModularFormToPAdic_eq_zero_iff]

/-- **The weight of a classical form**, for `p ≥ 5`: the `p`-adic weight of the scalar extension of
a nonzero rational modular form of weight `k` is the classical weight `ι k`. -/
theorem w_rationalModularFormToPAdicForm [Fact (5 ≤ p)] {F : rationalModularForms k} (hF : F ≠ 0) :
    w (rationalModularFormToPAdicForm p F) = ι k :=
  w_eq_of_tendsto (rationalModularFormToPAdicForm_eq_zero_iff.not.2 hF) (.const F)
    tendsto_const_nhds

/-- The `p`-adic weight of `E₄` is `ι 4`, for `p ≥ 5`. -/
theorem w_E₄PAdic [Fact (5 ≤ p)] : w (rationalModularFormToPAdicForm p E₄Rat) = ι 4 :=
  w_rationalModularFormToPAdicForm E₄Rat_ne_zero

/-- The `p`-adic weight of `E₆` is `ι 6`, for `p ≥ 5`. -/
theorem w_E₆PAdic [Fact (5 ≤ p)] : w (rationalModularFormToPAdicForm p E₆Rat) = ι 6 :=
  w_rationalModularFormToPAdicForm E₆Rat_ne_zero

end ModularForm
