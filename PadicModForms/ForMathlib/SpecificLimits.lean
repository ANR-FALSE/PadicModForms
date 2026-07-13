/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib

/-!
# Existence of arbitrarily small integer powers
-/

@[expose] public section

-- should go to Mathlib.Analysis.SpecificLimits.Basic
theorem exists_zpow_neg_lt {b : ℝ} (hb : 1 < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℤ, b ^ (-k) < ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hb)
  exact ⟨n, by rwa [zpow_neg, zpow_natCast, ← inv_pow]⟩
