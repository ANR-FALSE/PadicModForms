/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# p-adic weight space

This file defines the p-adic weight space used for p-adic modular forms.
-/

@[expose] public section

variable {p : ℕ} [Fact p.Prime]

notation "X_[" p "]" => ContinuousMonoidHom ℤ_[p]ˣ ℤ_[p]ˣ

noncomputable def ι : ℤ → X_[p] := fun n ↦ ⟨zpowGroupHom n, by fun_prop⟩
