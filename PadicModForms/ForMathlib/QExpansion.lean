/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Additional results about `q`-expansions of modular forms

This file contains results about `q`-expansions that are not tied to a temporary mathlib backport.
-/

@[expose] public noncomputable section

open UpperHalfPlane

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ}

@[simp]
theorem qExpansionAddHom_apply (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ)
    (f : ModularForm Γ k) : qExpansionAddHom hh hΓ k f = qExpansion h f :=
  rfl

/-- The `q`-expansion map is injective on modular forms of a fixed weight. -/
theorem qExpansion_injective (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {k : ℤ} :
    Function.Injective (fun f : ModularForm Γ k ↦ qExpansion h f) := by
  simp only [← qExpansionAddHom_apply hh hΓ k]
  refine (AddMonoidHom.ker_eq_bot_iff _).1 (AddSubgroup.ext fun F ↦ ?_)
  exact ModularForm.qExpansion_eq_zero_iff hh hΓ F

@[simp]
theorem qExpansion_inj (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {k : ℤ}
    {f g : ModularForm Γ k} : qExpansion h f = qExpansion h g ↔ f = g :=
  (qExpansion_injective hh hΓ).eq_iff

end ModularForm
