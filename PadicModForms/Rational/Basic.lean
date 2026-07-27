/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.Rational.Defs

/-!
# Basic results about rational modular forms

This file gives rational modular forms of a fixed weight their linear structure.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm ModularFormClass MatrixGroups

open scoped MatrixGroups

namespace PowerSeries

/-- The zero power series is a rational modular form of every weight. -/
theorem zero_isModularForm (k : ℤ) : (0 : ℚ⟦X⟧).isModularForm k := by
  sorry

/-- The sum of two rational modular forms of the same weight is modular of that weight. -/
theorem IsModularForm.add {k : ℤ} {f g : ℚ⟦X⟧}
    (hf : f.isModularForm k) (hg : g.isModularForm k) : (f + g).isModularForm k := by
  sorry

/-- The negative of a rational modular form is modular of the same weight. -/
theorem IsModularForm.neg {k : ℤ} {f : ℚ⟦X⟧} (hf : f.isModularForm k) :
    (-f).isModularForm k := by
  sorry

/-- The difference of two rational modular forms of the same weight is modular of that weight. -/
theorem IsModularForm.sub {k : ℤ} {f g : ℚ⟦X⟧}
    (hf : f.isModularForm k) (hg : g.isModularForm k) : (f - g).isModularForm k := by
  sorry

/-- A rational scalar multiple of a rational modular form is modular of the same weight. -/
theorem IsModularForm.smul {k : ℤ} {f : ℚ⟦X⟧} (hf : f.isModularForm k) (a : ℚ) :
    (a • f).isModularForm k := by
  sorry

/-- The constant power series `1` is a rational modular form of weight zero. -/
theorem one_isModularForm : (1 : ℚ⟦X⟧).isModularForm 0 := by
  sorry

/-- The product of rational modular forms of weights `k` and `l` is modular of weight `k + l`. -/
theorem IsModularForm.mul {k l : ℤ} {f g : ℚ⟦X⟧}
    (hf : f.isModularForm k) (hg : g.isModularForm l) : (f * g).isModularForm (k + l) := by
  sorry

/-- Rational modular forms of weight `k`, as a submodule of rational power series. -/
def rationalModularForms (k : ℤ) : Submodule ℚ ℚ⟦X⟧ where
  carrier := {f | f.isModularForm k}
  zero_mem' := zero_isModularForm k
  add_mem' hf hg := IsModularForm.add hf hg
  smul_mem' a _ hf := IsModularForm.smul hf a

@[simp]
theorem mem_rationalModularForms {k : ℤ} {f : ℚ⟦X⟧} :
    f ∈ rationalModularForms k ↔ f.isModularForm k :=
  Iff.rfl

end PowerSeries
