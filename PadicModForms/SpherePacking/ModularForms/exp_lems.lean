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

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


/-!
# Exponential Lemmas

Auxiliary lemmas about the complex exponential.
-/

-- Vendored code: Mathlib's style linters are switched off so the proofs can stay
-- byte-identical to upstream (which disables `linter.flexible` project-wide anyway).
set_option linter.mathlibStandardSet false


@[expose] public section


open UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

theorem exp_upperHalfPlane_lt_one (z : ℍ) :
    ‖(Complex.exp (2 * ↑π * Complex.I * z))‖ < 1 := by
  simp only [norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
    Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im,
    zero_sub, Real.exp_lt_one_iff, Left.neg_neg_iff]
  positivity

theorem exp_upperHalfPlane_lt_one_nat (z : ℍ) (n : ℕ) :
    ‖(Complex.exp (2 * ↑π * Complex.I * (n+1) * z))‖ < 1 := by
  simp [norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
    Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im,
    zero_sub, Real.exp_lt_one_iff, Left.neg_neg_iff]
  positivity
