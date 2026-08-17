/-
Copyright (c) 2025 Christopher Birkbeck, Sidharth Hariharan, Seewoo Lee, Ho Kiu Gareth Ma,
Bhavik Mehta, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Sidharth Hariharan, Seewoo Lee, Ho Kiu Gareth Ma, Bhavik Mehta,
Maryna Viazovska
-/
-- Vendored from the Sphere-Packing-Lean project at commit d5e6f11:
--   https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean
-- See `PadicModForms/SpherePacking/README.md` for the licence and the list of adaptations.

module

public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import PadicModForms.SpherePacking.ModularForms.Eisenstein

/-!
# Dimension formulas for level-one modular forms

Mathlib (≥ v4.30.0) proves the level-one dimension formulas in
`Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula`
(`ModularForm.dimension_level_one`, the rank lemmas for small weights, and
`CuspForm.discriminantEquiv`) and the identity `Δ = (E₄³ - E₆²) / 1728` in
`Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing`. Those results are stated for the
subgroup `𝒮ℒ`; this file transports the ones the project uses to the `Γ(1)`-indexed
spaces used here (`CongruenceSubgroup.Gamma_one_coe_eq_SL`).
-/

-- Vendored code: Mathlib's style linters are switched off so the proofs can stay
-- byte-identical to upstream (which disables `linter.flexible` project-wide anyway).
set_option linter.mathlibStandardSet false


@[expose] public section

open ModularForm hiding E₄ E₆
open EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup

noncomputable section

private theorem slashInvariantForm_mul_apply {k₁ k₂ : ℤ} {Γ : Subgroup SL(2, ℤ)}
    (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) (z : ℍ) : (f.mul g) z = f z * g z := rfl

/-- `Module.rank` of a `ModularForm` space is invariant under equality of the underlying subgroup.
Bridges the project's `Γ(1)`-indexed spaces to mathlib's `𝒮ℒ`-indexed level-one dimension lemmas
(`𝒮ℒ = (mapGL ℝ).range = ↑Γ(1)`, via `CongruenceSubgroup.Gamma_one_coe_eq_SL`). -/
private lemma rank_modularForm_congr {k : ℤ} {G₁ G₂ : Subgroup (GL (Fin 2) ℝ)}
    [G₁.HasDetOne] [G₂.HasDetOne] (h : G₁ = G₂) :
    Module.rank ℂ (ModularForm G₁ k) = Module.rank ℂ (ModularForm G₂ k) := by
  subst h; rfl

/-- `CuspForm` analogue of `rank_modularForm_congr`. -/
private lemma rank_cuspForm_congr {k : ℤ} {G₁ G₂ : Subgroup (GL (Fin 2) ℝ)}
    [G₁.HasDetOne] [G₂.HasDetOne] (h : G₁ = G₂) :
    Module.rank ℂ (CuspForm G₁ k) = Module.rank ℂ (CuspForm G₂ k) := by
  subst h; rfl

lemma cuspform_weight_lt_12_zero (k : ℤ) (hk : k < 12) : Module.rank ℂ (CuspForm Γ(1) k) = 0 :=
  (rank_cuspForm_congr CongruenceSubgroup.Gamma_one_coe_eq_SL).trans
    (CuspForm.rank_eq_zero_of_weight_lt_twelve hk)

lemma IsCuspForm_weight_lt_eq_zero (k : ℤ) (hk : k < 12) (f : ModularForm Γ(1) k)
    (hf : IsCuspForm Γ(1) k f) : f = 0 := by
  have hfc2 := CuspForm_to_ModularForm_coe _ _ f hf
  ext z
  simp only [zero_apply] at *
  have hy := congr_arg (fun x ↦ x.1) hfc2
  have hz := congr_fun hy z
  simp only [SlashInvariantForm.toFun_eq_coe, CuspForm.toSlashInvariantForm_coe,
  toSlashInvariantForm_coe] at hz
  rw [← hz]
  have := rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero k hk)
    (IsCuspForm_to_CuspForm Γ(1) k f hf)
  rw [this]
  simp only [zero_apply]

lemma weight_six_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 6) = 1 :=
  (rank_modularForm_congr CongruenceSubgroup.Gamma_one_coe_eq_SL).trans
    ModularForm.levelOne_weight_six_rank_one

lemma weight_four_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 4) = 1 :=
  (rank_modularForm_congr CongruenceSubgroup.Gamma_one_coe_eq_SL).trans
    ModularForm.levelOne_weight_four_rank_one

lemma weight_eight_one_dimensional (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (hk3 : k < 12) :
    Module.rank ℂ (ModularForm Γ(1) k) = 1 := by
  rw [rank_modularForm_congr CongruenceSubgroup.Gamma_one_coe_eq_SL,
    ModularForm.rank_eq_one_add_rank_cuspForm (by exact_mod_cast hk) hk2,
    CuspForm.rank_eq_zero_of_weight_lt_twelve (by exact_mod_cast hk3)]
  simp

-- Removed when vendoring: `dim_gen_cong_levels` (finite-dimensionality of `ModularForm Γ k` for a
-- finite-index congruence subgroup) was stated with a `sorry` upstream, is unused here, and is not
-- needed by any of the `weight_*_one_dimensional` lemmas above.
