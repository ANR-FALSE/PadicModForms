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

@[expose] public section

namespace PowerSeries

theorem zero_isModularForm (k : ℤ) : isModularForm k 0 :=
  ⟨0, by simpa using UpperHalfPlane.qExpansion_zero 1⟩

variable {k l : ℤ} {f g : ℚ⟦X⟧} (hf : f.isModularForm k) (hg : g.isModularForm k)

theorem one_isModularForm : (1 : ℚ⟦X⟧).isModularForm 0 :=
  ⟨1, by simpa using UpperHalfPlane.qExpansion_one 1⟩

include hf

theorem IsModularForm.neg : (-f).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  exact ⟨-F, by simp [ModularForm.qExpansion_neg one_pos one_mem_strictPeriods_SL, hF]⟩

theorem IsModularForm.smul (a : ℚ) : (a • f).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  exact ⟨(a : ℂ) • F, by simp [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hF,
    smul_eq_C_mul]⟩

theorem IsModularForm.mul (hg : g.isModularForm l) : (f * g).isModularForm (k + l) := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨F.mul G, by
    simp only [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL, hF, hG, map_mul]⟩

include hg

theorem IsModularForm.add : (f + g).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨F + G, by simp [ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL, hF, hG]⟩

theorem IsModularForm.sub : (f - g).isModularForm k := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨F - G, by simp [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL, hF, hG]⟩

def _root_.rationalModularForms (k : ℤ) : Submodule ℚ ℚ⟦X⟧ where
  carrier := {f | f.isModularForm k}
  zero_mem' := zero_isModularForm k
  add_mem' hf hg := IsModularForm.add hf hg
  smul_mem' a _ hf := IsModularForm.smul hf a

omit hf hg

@[simp]
theorem mem_rationalModularForms : f ∈ rationalModularForms k ↔ f.isModularForm k := .rfl

end PowerSeries
