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

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

public import PadicModForms.SpherePacking.ModularForms.Delta

/-!
# `q`-Expansions of Eisenstein Series

The `q`-expansions of the Eisenstein series.
-/

-- Vendored code: Mathlib's style linters are switched off so the proofs can stay
-- byte-identical to upstream (which disables `linter.flexible` project-wide anyway).
set_option linter.mathlibStandardSet false


@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma

noncomputable section Definitions

def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0

def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2 : ℂ) • eisensteinSeriesMF hk standardcongruencecondition /-they need 1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/

/-Forwards to `EisensteinSeries.q_expansion_riemannZeta` from mathlib. -/
lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
        (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by
  rw [_root_.E]
  let F : ℍ → ℂ :=
    (1 / 2 : ℂ) • (ModularForm.eisensteinSeriesMF hk standardcongruencecondition : ℍ → ℂ)
  change F z = _
  calc
    F z =
        1 + (riemannZeta k)⁻¹ * (-2 * ↑π * Complex.I) ^ k / (k - 1)! *
          ∑' n : ℕ+, σ (k - 1) n * cexp (2 * ↑π * Complex.I * z) ^ (n : ℤ) := by
      have hq := EisensteinSeries.q_expansion_riemannZeta (k := k) (by lia) hk2 z
      rw [ModularForm.E] at hq
      change F z = _ at hq
      exact hq
    _ = 1 + (1 / riemannZeta k) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
          ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by
      rw [show ∑' n : ℕ+, σ (k - 1) n * cexp (2 * ↑π * Complex.I * z) ^ (n : ℤ) =
          ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) from by
            apply tsum_congr
            intro n
            rw [zpow_natCast, ← Complex.exp_nat_mul]
            ring_nf]
      simp [div_eq_mul_inv, mul_assoc]
