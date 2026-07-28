/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.QExpansion
public import PadicModForms.Rational.Defs

/-!
# Basic results about rational modular forms

This file gives rational modular forms of a fixed weight their linear structure.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm MatrixGroups

open scoped MatrixGroups PowerSeries

namespace PowerSeries

/-- The rational-coefficient complex power series. -/
abbrev rationalSubmodule : Submodule ℚ ℂ⟦X⟧ :=
  (mapAlgHom (Algebra.ofId ℚ ℂ)).toLinearMap.range

/-- Rational power series are linearly equivalent to rational-coefficient complex power series. -/
def rationalEquiv : ℚ⟦X⟧ ≃ₗ[ℚ] rationalSubmodule :=
  .ofInjective (mapAlgHom _).toLinearMap (map_injective _ (algebraMap ℚ ℂ).injective)

@[simp]
theorem coe_rationalEquiv_apply (f : ℚ⟦X⟧) :
    (rationalEquiv f : ℂ⟦X⟧) = f.map (algebraMap ℚ ℂ) :=
  LinearEquiv.ofInjective_apply _ f

@[simp]
theorem rationalEquiv_symm_map (f : rationalSubmodule) :
    (rationalEquiv.symm f).map (algebraMap ℚ ℂ) = (f : ℂ⟦X⟧) := by
  rw [← coe_rationalEquiv_apply]
  exact congrArg Subtype.val (rationalEquiv.apply_symm_apply f)

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

omit hf hg

end PowerSeries

open PowerSeries

/-- The rational modular forms of weight `k`, as the pullback of rational-coefficient power
series under the complex `q`-expansion map. -/
def rationalModularForms (k : ℤ) : Submodule ℚ (ModularForm 𝒮ℒ k) :=
  rationalSubmodule.comap
    ((qExpansionLinearMap one_pos one_mem_strictPeriods_SL k).restrictScalars ℚ)

namespace ModularForm

variable {k : ℤ}

@[simp]
theorem mem_rationalModularForms (F : ModularForm 𝒮ℒ k) : F ∈ rationalModularForms k ↔
    ∃ f : ℚ⟦X⟧, qExpansion 1 F = f.map (algebraMap ℚ ℂ) :=
  ⟨fun ⟨f, hf⟩ ↦ ⟨f, hf.symm⟩, fun ⟨f, hf⟩ ↦ ⟨f, hf.symm⟩⟩

/-- The rational `q`-expansion of a rational modular form of fixed weight. -/
def rationalQExpansionToRationalSubmodule :
    rationalModularForms k →ₗ[ℚ] rationalSubmodule :=
  (((qExpansionLinearMap one_pos one_mem_strictPeriods_SL k).restrictScalars ℚ).domRestrict
    (rationalModularForms k)).codRestrict _ fun f ↦ f.property

@[simp]
theorem coe_rationalQExpansionToRationalSubmodule (f : rationalModularForms k) :
    (rationalQExpansionToRationalSubmodule f : ℂ⟦X⟧) = qExpansion 1 (f : ModularForm 𝒮ℒ k) := rfl

/-- The rational `q`-expansion of a rational modular form of fixed weight. -/
def rationalQExpansionLinearMap : rationalModularForms k →ₗ[ℚ] ℚ⟦X⟧ :=
  rationalEquiv.symm.toLinearMap.comp rationalQExpansionToRationalSubmodule

@[simp]
theorem rationalQExpansionLinearMap_map (f : rationalModularForms k) :
    (rationalQExpansionLinearMap f).map (algebraMap ℚ ℂ) = qExpansion 1 (f : ModularForm 𝒮ℒ k) := by
  simp [rationalQExpansionLinearMap]

end ModularForm

namespace PowerSeries

variable {k : ℤ}

/-- A rational power series which is modular defines a rational modular form. -/
def IsModularForm.toRationalModularForm {f : ℚ⟦X⟧} (hf : f.isModularForm k) :
    rationalModularForms k :=
  ⟨hf.choose, (ModularForm.mem_rationalModularForms hf.choose).2 ⟨f, hf.choose_spec⟩⟩

@[simp]
theorem IsModularForm.rationalQExpansionLinearMap_toRationalModularForm
    {f : ℚ⟦X⟧} (hf : f.isModularForm k) :
    ModularForm.rationalQExpansionLinearMap (IsModularForm.toRationalModularForm hf) = f := by
  apply PowerSeries.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  rw [ModularForm.rationalQExpansionLinearMap_map]
  exact hf.choose_spec

end PowerSeries
