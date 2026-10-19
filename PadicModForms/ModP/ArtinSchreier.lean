/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.SigmaSeries
public import PadicModForms.ModP.WeightZero
public import PadicModForms.ModP.Filtration
public import PadicModForms.ModP.Ramanujan
import PadicModForms.ModP.Congruences
import PadicModForms.ModP.ThetaFiltration

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
theorem E₂ModP_eq_one_sub_sigmaSeries : E₂ModP = 1 - 24 * sigmaSeries (ZMod p) 1 := by
  ext n
  rw [E₂ModP_def, PowerSeries.coeff_map]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn, map_mul, map_neg, map_ofNat]

/-- Serre's `ψ` as an iterate of `Θ` on `E₂`: `Θ^[p - 2] E₂ = -24 ψ`, the constant term of `E₂`
being killed by the first application of `Θ`. -/
theorem iterate_Θ_E₂ModP (hp : 5 ≤ p) :
    (Θ)^[p - 2] E₂ModP = -24 * sigmaSeriesPrimeTo (ZMod p) p (p - 2) := by
  rw [← iterate_Θ_sigmaSeries_one (by lia), E₂ModP_eq_one_sub_sigmaSeries,
    ← map_ofNat PowerSeries.C]
  ext n
  simp only [coeff_iterate_Θ, map_sub, PowerSeries.coeff_one, neg_mul, map_neg,
    PowerSeries.coeff_C_mul, nsmul_eq_mul, Nat.cast_pow]
  split_ifs with hn
  · simp [hn, zero_pow (show p - 2 ≠ 0 by lia)]
  · ring

/-- `ψ = (-24)⁻¹ • Θ^[p - 2] E₂`: the form of `iterate_Θ_E₂ModP` that transfers membership and
filtration from `Θ^[p - 2] E₂` to `ψ`. -/
theorem sigmaSeriesPrimeTo_eq_smul_iterate_Θ_E₂ModP (hp : 5 ≤ p) :
    sigmaSeriesPrimeTo (ZMod p) p (p - 2) =
      (-24 : ZMod p)⁻¹ • (Θ (R := ZMod p))^[p - 2] E₂ModP := by
  have h24 : (24 : ZMod p) ≠ 0 := ZMod.ne_zero_of_eq_two_pow_mul_three_pow hp 3 1 (by norm_num)
  rw [iterate_Θ_E₂ModP hp, PowerSeries.smul_eq_C_mul, ← mul_assoc,
    show (-24 : (ZMod p)⟦X⟧) = PowerSeries.C (-24) by simp [map_ofNat], ← map_mul,
    inv_mul_cancel₀ (neg_ne_zero.mpr h24), map_one, one_mul]

/-- `ψ` is a degree-zero mod-`p` modular form: `Θ^[p - 2] E₂` has a homogeneous representative of
weight `(p - 1)(p + 1)`, which is divisible by `p - 1`, and `-24` is invertible. -/
theorem sigmaSeriesPrimeTo_mem_modPWeightZeroForms (hp : 5 ≤ p) :
    sigmaSeriesPrimeTo (ZMod p) p (p - 2) ∈ modPWeightZeroForms p := by
  obtain ⟨G, hG, hGE⟩ := exists_isWeightedHomogeneous_iterate_Θ_E₂ModP hp (p - 2)
  rw [sigmaSeriesPrimeTo_eq_smul_iterate_Θ_E₂ModP hp, ← hGE]
  refine (modPWeightZeroForms p).smul_mem (mem_modPWeightZeroForms_of_isWeightedHomogeneous ?_ hG) _
  simp [show p - 2 + 1 = p - 1 by lia]

/-- The filtration of `ψ` is exactly `p² - 1`, by `modPFiltration_iterate_Θ_E₂ModP` at
`j = p - 2`. -/
theorem modPFiltration_sigmaSeriesPrimeTo (hp : 5 ≤ p) :
    modPFiltration p (sigmaSeriesPrimeTo (ZMod p) p (p - 2)) = p ^ 2 - 1 := by
  have h24 : (24 : ZMod p) ≠ 0 := ZMod.ne_zero_of_eq_two_pow_mul_three_pow hp 3 1 (by norm_num)
  rw [sigmaSeriesPrimeTo_eq_smul_iterate_Θ_E₂ModP hp,
    modPFiltration_smul (inv_ne_zero (neg_ne_zero.mpr h24)),
    modPFiltration_iterate_Θ_E₂ModP hp le_rfl]
  zify [Nat.one_le_pow 2 p (by lia), (by lia : 2 ≤ p)]
  ring

/-- **The Artin–Schreier identity** with the exponent already reduced: for `h ≥ 2` a multiple
of `p - 1`, `φ_h - φ_h ^ p = ψ`. This holds for every prime `p`, and combines
`PowerSeries.sigmaSeries_sub_pow_prime` with the reduction of the exponent
`h - 1 ≡ p - 2 mod (p - 1)`. For `p ≥ 3` the hypothesis `2 ≤ h` just says that `h` is a positive
multiple of `p - 1`. -/
theorem sigmaSeries_sub_pow_eq (hh : 2 ≤ h) (hhd : p - 1 ∣ h) :
    sigmaSeries (ZMod p) (h - 1) - sigmaSeries (ZMod p) (h - 1) ^ p =
      sigmaSeriesPrimeTo (ZMod p) p (p - 2) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [sigmaSeries_sub_pow_prime (by lia)]
  refine sigmaSeriesPrimeTo_eq_of_natCast_eq ?_
  rw [show p - 2 = p - 1 - 1 by lia, Nat.cast_sub (by lia), Nat.cast_sub (by lia),
    ZMod.natCast_self, (ZMod.natCast_eq_zero_iff _ _).mpr hhd]

/-- **The forbidden series**: `φ_h = ∑ σ_{h-1}(n) qⁿ` is not a degree-zero mod-`p` modular form.
Were it one, its filtration `a` would be positive because the coefficient of `q` in `φ_h` is `1`
(`modPFiltration_pos_of_coeff_ne_zero`), so `fil (φ_h - φ_h ^ p) = p a` by the Frobenius
difference formula `modPFiltration_sub_pow_prime`, and the Artin–Schreier identity would give
`p a = p² - 1`, which is impossible modulo `p`. -/
theorem sigmaSeries_notMem_modPWeightZeroForms (hp : 5 ≤ p) (hh0 : h ≠ 0) (hhd : p - 1 ∣ h) :
    sigmaSeries (ZMod p) (h - 1) ∉ modPWeightZeroForms p := fun hmem ↦ by
  obtain ⟨n, F, -, hF, hFφ⟩ := exists_isWeightedHomogeneous_of_mem_modPWeightZeroForms hp hmem
  have ha : 0 < modPFiltration p (evalE₄E₆ModP F) := modPFiltration_pos_of_coeff_ne_zero hF
    one_ne_zero (by simp [hFφ, isMultiplicative_sigma.map_one])
  have key := modPFiltration_sub_pow_prime hp hF ha
  rw [hFφ, sigmaSeries_sub_pow_eq (by grind [Nat.le_of_dvd (Nat.pos_of_ne_zero hh0) hhd]) hhd,
    modPFiltration_sigmaSeriesPrimeTo hp] at key
  have h1 : p ∣ 1 := (Nat.dvd_add_right (show p ∣ p ^ 2 - 1 by rw [key]; exact dvd_mul_right _ _)).1
    (by rw [Nat.sub_add_cancel (Nat.one_le_pow 2 p (by lia))]; exact dvd_pow_self p two_ne_zero)
  exact absurd (Nat.le_of_dvd one_pos h1) (by lia)

end ModularForm
