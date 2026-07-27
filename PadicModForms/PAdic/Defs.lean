/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Group.CompactOpen

public import PadicModForms.Rational.Defs

/-!
# p-adic modular forms

This file defines p-adic weight space and p-adic modular forms as limits of rational classical
modular forms.
-/

@[expose] public section

open UpperHalfPlane PowerSeries ModularFormClass Filter

open scoped MatrixGroups Topology

variable {p : ℕ} [Fact p.Prime]

/-- The p-adic weight space. -/
notation "X_[" p "]" => ContinuousMonoidHom ℤ_[p]ˣ ℤ_[p]ˣ

/-- The classical integral weight `n`, regarded as a p-adic weight. -/
noncomputable def ι : ℤ → X_[p] := fun n ↦ ⟨zpowGroupHom n, by fun_prop⟩

/-- A presentation of a p-adic modular form by classical rational modular forms whose
coefficients converge uniformly. -/
structure pAdicModularFormStruct (f : ℚ_[p]⟦X⟧) where
  F : ℕ → ℚ⟦X⟧
  w : ℕ → ℤ
  modF : ∀ i, (F i).isModularForm (w i)
  tendsTo : TendstoUniformly (fun i n ↦ (↑(coeff n (F i)) : ℚ_[p])) (coeff · f) atTop

variable (p)

/-- A p-adic power series is a p-adic modular form if it admits a presentation by classical
rational modular forms. -/
def PowerSeries.isPAdicModularForm (f : ℚ_[p]⟦X⟧) :=
  Nonempty (pAdicModularFormStruct f)

/-- The type of p-adic modular forms. -/
def PAdicModularForms := {f // PowerSeries.isPAdicModularForm p f}
