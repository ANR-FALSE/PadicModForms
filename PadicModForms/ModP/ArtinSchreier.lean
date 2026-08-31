/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.SigmaSeries
public import PadicModForms.ModP.ThetaFiltration
public import PadicModForms.ModP.WeightZero

/-!
# The Artin–Schreier identity and the forbidden divisor-sum series

Let `p ≥ 5` and let `h` be a positive multiple of `p - 1`. Serre's series
`φ_h = ∑_{n ≥ 1} σ_{h-1}(n) qⁿ` and `ψ = ∑_{p ∤ n} σ_{p-2}(n) qⁿ` over `ZMod p` satisfy the
Artin–Schreier identity `φ_h - φ_h ^ p = ψ`, where the right-hand side does not depend on `h`
because divisor sums prime to `p` only see the exponent modulo `p - 1`.

The series `ψ` is a degree-zero mod-`p` modular form: it is a scalar multiple of
`Θ^[p - 2] E₂ModP`, since `E₂ = 1 - 24 ∑ σ₁(n) qⁿ`, and its filtration is exactly `p² - 1` by the
sharp theta filtration formula. The main result is that `φ_h` is **not** a degree-zero form: if
it were, of filtration `a > 0`, the Artin–Schreier identity and the filtration package would give
`p a = p² - 1`, which is impossible modulo `p`. This is the lemma quoted without proof at the end
of Serre's proof of his Theorem 1.

## Main results

* `ModularForm.iterate_Θ_E₂ModP`: `Θ^[p - 2] E₂ = -24 ψ`.
* `ModularForm.sigmaSeriesPrimeTo_mem_modPWeightZeroForms`,
  `ModularForm.modPFiltration_sigmaSeriesPrimeTo`: `ψ ∈ 𝓜⁰` with filtration `p² - 1`.
* `ModularForm.sigmaSeries_sub_pow_eq`: the Artin–Schreier identity `φ_h - φ_h ^ p = ψ`.
* `ModularForm.sigmaSeries_notMem_modPWeightZeroForms`: `φ_h ∉ 𝓜⁰`.
-/

@[expose] public noncomputable section

open ArithmeticFunction sigma EisensteinSeries MvPolynomial
open PowerSeries hiding C X

namespace ModularForm

variable {p h : ℕ} [Fact p.Prime]

/-- Serre's `P` in terms of the divisor-sum series: `E₂ = 1 - 24 ∑ σ₁(n) qⁿ` modulo `p`. -/
theorem E₂ModP_eq_one_sub_sigmaSeries :
    E₂ModP (p := p) = 1 - 24 * sigmaSeries (ZMod p) 1 := by
  sorry

/-- Serre's `ψ` as an iterate of `Θ` on `E₂`: `Θ^[p - 2] E₂ = -24 ψ`, the constant term of `E₂`
being killed by the first application of `Θ`. -/
theorem iterate_Θ_E₂ModP (hp : 5 ≤ p) :
    ((Θ (R := ZMod p)))^[p - 2] E₂ModP = -24 * sigmaSeriesPrimeTo (ZMod p) p (p - 2) := by
  sorry

/-- `ψ` is a degree-zero mod-`p` modular form: `Θ^[p - 2] E₂` has a homogeneous representative of
weight `(p - 1)(p + 1)`, which is divisible by `p - 1`, and `-24` is invertible. -/
theorem sigmaSeriesPrimeTo_mem_modPWeightZeroForms (hp : 5 ≤ p) :
    sigmaSeriesPrimeTo (ZMod p) p (p - 2) ∈ modPWeightZeroForms p := by
  sorry

/-- The filtration of `ψ` is exactly `p² - 1`, by `modPFiltration_iterate_Θ_E₂ModP` at
`j = p - 2`. -/
theorem modPFiltration_sigmaSeriesPrimeTo (hp : 5 ≤ p) :
    modPFiltration p (sigmaSeriesPrimeTo (ZMod p) p (p - 2)) = p ^ 2 - 1 := by
  sorry

/-- **The Artin–Schreier identity** with the exponent already reduced: for `h` a positive
multiple of `p - 1`, `φ_h - φ_h ^ p = ψ`. This combines
`PowerSeries.sigmaSeries_sub_pow_prime` with the reduction of the exponent
`h - 1 ≡ p - 2 mod (p - 1)`. -/
theorem sigmaSeries_sub_pow_eq (hp : 5 ≤ p) (hh0 : h ≠ 0) (hhd : p - 1 ∣ h) :
    sigmaSeries (ZMod p) (h - 1) - sigmaSeries (ZMod p) (h - 1) ^ p =
      sigmaSeriesPrimeTo (ZMod p) p (p - 2) := by
  sorry

/-- **The forbidden series**: `φ_h = ∑ σ_{h-1}(n) qⁿ` is not a degree-zero mod-`p` modular form.
Were it one, its filtration `a` would be positive because the coefficient of `q` in `φ_h` is `1`,
so `fil (φ_h ^ p) = p a > a` by the Frobenius formula, `fil (φ_h - φ_h ^ p) = p a` because
unequal filtrations do not cancel, and the Artin–Schreier identity would give `p a = p² - 1`,
which is impossible modulo `p`. -/
theorem sigmaSeries_notMem_modPWeightZeroForms (hp : 5 ≤ p) (hh0 : h ≠ 0) (hhd : p - 1 ∣ h) :
    sigmaSeries (ZMod p) (h - 1) ∉ modPWeightZeroForms p := by
  sorry

end ModularForm
