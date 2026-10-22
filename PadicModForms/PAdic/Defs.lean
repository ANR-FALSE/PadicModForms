/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.Padics.PadicIntegers

public import PadicModForms.Rational.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.NormNum.Parity

/-!
# p-adic modular forms

This file defines p-adic weight space and p-adic modular forms as limits of rational classical
modular forms. A *presentation* of a p-adic modular form `f` (`pAdicModularFormStruct f`) is a
sequence of classical rational modular forms whose coefficients converge uniformly to those of
`f`; a `p`-adic power series is a p-adic modular form when it admits a presentation.
-/

@[expose] public section

open UpperHalfPlane PowerSeries ModularFormClass Filter ModularForm

open scoped MatrixGroups Topology

variable {p : ℕ} [Fact p.Prime]

/-- The p-adic weight space. -/
notation "X_[" p "]" => ContinuousMonoidHom ℤ_[p]ˣ ℤ_[p]ˣ

/-- The classical integral weight `n`, regarded as a p-adic weight. -/
noncomputable def ι : ℤ → X_[p] := fun n ↦ ⟨zpowGroupHom n, by fun_prop⟩

/-- A presentation of a p-adic modular form by classical rational modular forms whose
coefficients converge uniformly. -/
structure pAdicModularFormStruct (f : ℚ_[p]⟦X⟧) where
  /-- The weights of the classical modular forms of the presentation. -/
  w : ℕ → ℤ
  /-- The classical rational modular forms of the presentation, `F i` having weight `w i`. -/
  F : (i : ℕ) → rationalModularForms (w i)
  /-- The coefficients of `F i` converge to those of `f` in `ℚ_[p]`, uniformly in the degree. -/
  tendsTo : TendstoUniformly (fun i n ↦ ↑(coeff n (rationalQExpansion (F i)))) (coeff · f) atTop

variable (p)

/-- A `p`-adic power series is a `p`-adic modular form if it admits a presentation by classical
rational modular forms. -/
def PowerSeries.isPAdicModularForm (f : ℚ_[p]⟦X⟧) := Nonempty (pAdicModularFormStruct f)

/-- The type of p-adic modular forms. -/
def PAdicModularForms := {f // PowerSeries.isPAdicModularForm p f}

namespace PAdicModularForms

variable {p}

/-- The zero power series is a `p`-adic modular form, presented by the zero form of weight `0`. -/
noncomputable instance : Zero (PAdicModularForms p) :=
  ⟨⟨0, ⟨⟨fun _ ↦ 0, fun _ ↦ 0, fun u hu ↦ by
    filter_upwards with i n
    simpa using refl_mem_uniformity hu⟩⟩⟩⟩

@[simp]
theorem val_zero : (0 : PAdicModularForms p).1 = 0 := rfl

theorem val_eq_zero_iff {f : PAdicModularForms p} : f.1 = 0 ↔ f = 0 :=
  ⟨fun h ↦ Subtype.ext (h.trans val_zero.symm), fun h ↦ h ▸ rfl⟩

end PAdicModularForms
