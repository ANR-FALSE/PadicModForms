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

public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

/-!
# Cusps

Auxiliary lemmas about cusps used in the modular forms development.
-/

-- Vendored code: Mathlib's style linters are switched off so the proofs can stay
-- byte-identical to upstream (which disables `linter.flexible` project-wide anyway).
set_option linter.mathlibStandardSet false


@[expose] public section

open scoped MatrixGroups ModularForm UpperHalfPlane

theorem zero_at_cusps_of_zero_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {k : ℤ}
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic]
    (hc : IsCusp c 𝒢) (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsZeroAtImInfty (f ∣[k] A)) :
    c.IsZeroAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  refine (OnePoint.isZeroAt_iff_forall_SL2Z hc).mpr fun A hA ↦ hb A ⟨A, rfl⟩

theorem bounded_at_cusps_of_bounded_at_infty {f : ℍ → ℂ} {c : OnePoint ℝ} {k : ℤ}
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic]
    (hc : IsCusp c 𝒢) (hb : ∀ A ∈ 𝒮ℒ, UpperHalfPlane.IsBoundedAtImInfty (f ∣[k] A)) :
    c.IsBoundedAt f k := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  exact (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun A hA ↦ hb A ⟨A, rfl⟩
