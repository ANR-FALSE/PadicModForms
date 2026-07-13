/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib

/-!
# Auxiliary results on modular forms
-/

@[expose] public section

open UpperHalfPlane

open scoped MatrixGroups

variable {k : ℤ} {Γ Γ' : Subgroup (GL (Fin 2) ℝ)}

-- should go to Mathlib.NumberTheory.ModularForms.Basic
@[simp]
theorem ModularForm.coe_copy (f : ModularForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) (hΓ : Γ' = Γ) :
    ⇑(f.copy f' h hΓ) = ⇑f := h

-- should go to Mathlib.NumberTheory.ModularForms.Basic
@[simp]
theorem CuspForm.coe_copy (f : CuspForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) (hΓ : Γ' = Γ) :
    ⇑(f.copy f' h hΓ) = ⇑f := h
