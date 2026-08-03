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

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Auxiliary theorems for the slash actions groups SL(2, ℤ) and Γ(2)

Define special generators S, T, -I (resp. α, β, -I) for SL(2,ℤ) (resp. Γ(2)) and prove that
they are indeed generators.
As a corollary, we only need to check the invariance under these special elements to check
the invariance under the whole group.
These theorems will be used to prove that 4-th powers of Jacobi theta functions Θ_2^4, Θ_3^4,
Θ_4^4 are modular forms of weight 2 and level Γ(2).
-/

-- Vendored code: Mathlib's style linters are switched off so the proofs can stay
-- byte-identical to upstream (which disables `linter.flexible` project-wide anyway).
set_option linter.mathlibStandardSet false


@[expose] public section

open scoped ModularForm MatrixGroups
open Matrix UpperHalfPlane CongruenceSubgroup ModularGroup

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => Gamma n

-- Removed when vendoring: the `Gamma 2` elements `α`, `β`, `negI` and the lemmas about
-- them are unused downstream and their proofs no longer compile against current Mathlib.
section slash_action

variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)

open ModularForm

theorem modular_slash_S_apply :
    (f ∣[k] S) z = f (UpperHalfPlane.mk (-z)⁻¹ z.im_inv_neg_coe_pos) * z ^ (-k) := by
  rw [SL_slash_apply, UpperHalfPlane.modular_S_smul, ModularGroup.denom_S]

theorem modular_slash_T_apply : (f ∣[k] T) z = f ((1 : ℝ) +ᵥ z) := by
  rw [SL_slash_apply, UpperHalfPlane.modular_T_smul]
  simp [denom_apply, ModularGroup.coe_T]

end slash_action

-- Removed when vendoring: the `slashaction_generators*` section (generation of `SL(2, ℤ)` and
-- `Γ 2` by `{S, T, -I}` / `{α, β, -I}`) is unused downstream.  It existed to derive the slash
-- action of `E₂` from generators; current Mathlib proves `EisensteinSeries.E2_slash_action`
-- for every `γ` directly.
