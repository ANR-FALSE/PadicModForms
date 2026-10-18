/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.SigmaSeries
public import PadicModForms.PAdic.Basic
public import PadicModForms.pLocalInt.Basic
import PadicModForms.ForMathlib.PowerSeries
import PadicModForms.ModP.Congruences
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.NormNum.Parity

/-!
# Serre's theorem on congruences of weights modulo `p ^ m`

Let `p ≥ 5` and `m ≥ 1`. If two `p`-integral level-one modular forms of weights `k` and `k'` are
congruent modulo `p ^ m` and their common reduction modulo `p` is nonzero, then

  `k' ≡ k mod (p - 1) p ^ (m - 1)`.

This is Serre's **Théorème 1** for `p ≥ 5`; the case `m = 1` is
`ModularForm.natCast_eq_of_map_toZMod_eq` in `PadicModForms.PAdic.Weights.Congruence`.

The proof is by contradiction. After a harmless multiplication of `f'` by an Eisenstein series
`E_{(p-1)pᴺ} ≡ 1 mod p^m`, the weight difference `h = k' - k` is a positive multiple of `p - 1`.
Set `r = v_p(h) + 1` and suppose `r < m`. The exact Eisenstein congruence
`E_h - 1 = p^r λ Φ_h` (`EisensteinSeries.E_int_sub_one_eq_unit_smul_sigmaSeries`) lets one divide
`f E_h - f' = (f - f') + f (E_h - 1)` by `p^r λ`, producing a `p`-integral form `g` of weight
`k + h` with reduction `ḡ = f̄ φ_h`, where `φ_h = ∑ σ_{h-1}(n) qⁿ`. Thus

* `φ_h` is a quotient of the two degree-zero forms `ḡ f̄ ^ (p - 2)` and `f̄ ^ (p - 1)`;
* `φ_h` is integral over the degree-zero forms, being a root of `T ^ p - T + ψ` by the
  Artin–Schreier identity (`ModularForm.sigmaSeries_sub_pow_eq`);

so normality (`ModularForm.mem_modPWeightZeroForms_of_isIntegral`) puts `φ_h` in the degree-zero
forms, contradicting `ModularForm.sigmaSeries_notMem_modPWeightZeroForms`. Hence `r ≥ m`, that is
`p ^ (m - 1) ∣ h`, and `(p - 1) p ^ (m - 1) ∣ h` since `p - 1` and `p` are coprime.

## Main results

* `ModularForm.pow_dvd_of_map_toZModPow_eq`: the core, for aligned weights `k` and `k + h`.
* `ModularForm.natCast_eq_of_map_toZModPow_eq`: the normalized theorem, for `p`-integral forms.
* `ModularForm.natCast_eq_of_v_sub_le_pow`: **Serre's Théorème 1** for `p ≥ 5`, phrased with the
  valuation `v` and no normalization: `v (f - f') ≥ v f + m` implies
  `k' ≡ k mod (p - 1) p ^ (m - 1)`.
-/

@[expose] public noncomputable section

open EisensteinSeries PowerSeries PowerSeries.Padic pLocalInt

namespace ModularForm

variable {p m : ℕ} [Fact p.Prime]

/-- Division of `f E_h - f'` by `p ^ r λ`: under the contradiction hypothesis `r < m`, with
`r = v_p(h) + 1`, there is a `p`-integral modular form `g` of weight `k + h` whose reduction
modulo `p` is `f̄ φ_h`. Indeed `f E_h - f' = (f - f') + f (E_h - 1)` has all its coefficients
divisible by `p ^ r`, the first summand even by `p ^ (r + 1)`, and dividing the exact Eisenstein
congruence by `p ^ r λ` leaves `f Φ_h` modulo `p`. Note that `h` is automatically even and
at least `4`, being a positive multiple of `p - 1` with `p ≥ 5`. -/
theorem exists_map_toZMod_eq_mul_sigmaSeries (hp : 5 ≤ p) {k h : ℕ}
    (hh0 : h ≠ 0) (hhd : p - 1 ∣ h) (hr : padicValNat p h + 1 < m)
    {f f' : (pLocalInt p)⟦X⟧} (hf : f ∈ pLocalIntModularForms p k)
    (hf' : f' ∈ pLocalIntModularForms p (k + h))
    (hcong : f.map (toZModPow m) = f'.map (toZModPow m)) :
    ∃ g : (pLocalInt p)⟦X⟧, g ∈ pLocalIntModularForms p (k + h) ∧
      g.map toZMod = f.map toZMod * sigmaSeries (ZMod p) (h - 1) := by
  have hh3 : 3 ≤ h := by grind [Nat.le_of_dvd (Nat.pos_of_ne_zero hh0) hhd]
  have hh2 : Even h := even_iff_two_dvd.2
    ((even_iff_two_dvd.1 ((Fact.out : p.Prime).even_sub_one (by lia))).trans hhd)
  obtain ⟨u, hu⟩ := E_int_sub_one_eq_unit_smul_sigmaSeries hp hh3 hh2 hhd
  set r := padicValNat p h + 1 with hr_def
  have hpr : (p : pLocalInt p) ^ r ≠ 0 := pow_ne_zero _ natCast_ne_zero
  set E := E_int hh3 hh2 (inv_bernoulli_mem_pLocalInt hh3 hh2 hhd) with hE_def
  have hE : E ∈ pLocalIntModularForms p h := E_int_mem_pLocalIntModularForms hh3 hh2 _
  -- `f - f' = p ^ (r + 1) R`, since `r + 1 ≤ m`.
  obtain ⟨R, hR⟩ : ∃ R : (pLocalInt p)⟦X⟧, (p : pLocalInt p) ^ (r + 1) • R = f - f' :=
    exists_smul_eq_of_forall_dvd_coeff fun n ↦ (pow_dvd_pow _ hr).trans
      (dvd_of_toZModPow_eq_zero (by rw [← coeff_map, map_sub, hcong, sub_self, map_zero]))
  -- `f Eₕ - f' = p ^ r (p R + u f Φₕ)`.
  have hD : f * E - f' = (p : pLocalInt p) ^ r •
      ((p : pLocalInt p) • R + (u : pLocalInt p) • (f * sigmaSeries (pLocalInt p) (h - 1))) := by
    simp [show f * E - f' = (f - f') + f * (E - 1) by ring, hu, ← hR, pow_succ, mul_smul]
  have hDmem : f * E - f' ∈ pLocalIntModularForms p (k + h) :=
    sub_mem (SetLike.mul_mem_graded hf hE) hf'
  -- Divide by `p ^ r` inside the `p`-integral modular forms.
  obtain ⟨D₀, hD₀mem, hD₀⟩ := IsPLocalIntModularForm.exists_smul_eq_of_forall_dvd_coeff
    (mem_pLocalIntModularForms.1 hDmem) hpr fun n ↦ by rw [hD, coeff_smul]; exact dvd_mul_right _ _
  suffices hD₀' : D₀ = (p : pLocalInt p) • R +
      (u : pLocalInt p) • (f * sigmaSeries (pLocalInt p) (h - 1)) by
    -- `g = u⁻¹ D₀ = u⁻¹ p R + f Φₕ` reduces to `f̄ φₕ`.
    refine ⟨((u⁻¹ : (pLocalInt p)ˣ) : pLocalInt p) • D₀, Submodule.smul_mem _ _ hD₀mem, ?_⟩
    rw [hD₀', smul_add, smul_smul, smul_smul]
    simp [smul_eq_C_mul, map_sigmaSeries]
  ext n : 1
  have := congr(coeff n $(hD₀.trans hD))
  rw [coeff_smul, coeff_smul] at this
  exact mul_left_cancel₀ hpr this

/-- **The core of Serre's theorem**: two `p`-integral forms of weights `k` and `k + h`, with `h` a
positive multiple of `p - 1`, congruent modulo `p ^ m` with nonzero common reduction, satisfy
`p ^ (m - 1) ∣ h`. Otherwise `exists_map_toZMod_eq_mul_sigmaSeries` realizes
`φ_h = ḡ f̄ ^ (p - 2) / f̄ ^ (p - 1)` as a quotient of degree-zero forms, integral over them by the
Artin–Schreier identity, hence a degree-zero form by normality — contradicting
`sigmaSeries_notMem_modPWeightZeroForms`. -/
theorem pow_dvd_of_map_toZModPow_eq (hp : 5 ≤ p) {k h : ℕ} (hh0 : h ≠ 0) (hhd : p - 1 ∣ h)
    {f f' : (pLocalInt p)⟦X⟧} (hf : f ∈ pLocalIntModularForms p k)
    (hf' : f' ∈ pLocalIntModularForms p (k + h)) (h0 : f.map toZMod ≠ 0)
    (hcong : f.map (toZModPow m) = f'.map (toZModPow m)) : p ^ (m - 1) ∣ h := by
  sorry

/-- **Serre's theorem on congruences of weights, normalized form**: two `p`-integral level-one
modular forms of weights `k` and `k'`, congruent modulo `p ^ m`, whose common reduction modulo
`p` is nonzero, have weights congruent modulo `(p - 1) p ^ (m - 1)`. The `m = 1` theorem gives
`p - 1 ∣ k' - k`; multiplying the form of smaller weight by `E_{(p-1)pᴺ} ≡ 1 mod p^m` for `N`
large aligns the weights as in `pow_dvd_of_map_toZModPow_eq` without changing the congruence
class of the weight difference modulo `(p - 1) p ^ (m - 1)`. -/
theorem natCast_eq_of_map_toZModPow_eq (hp : 5 ≤ p) (hm : 1 ≤ m) {k k' : ℕ}
    {f f' : (pLocalInt p)⟦X⟧} (hf : f ∈ pLocalIntModularForms p k)
    (hf' : f' ∈ pLocalIntModularForms p k') (h0 : f.map toZMod ≠ 0)
    (hcong : f.map (toZModPow m) = f'.map (toZModPow m)) :
    (k : ZMod ((p - 1) * p ^ (m - 1))) = (k' : ZMod ((p - 1) * p ^ (m - 1))) := by
  sorry

/-- **Serre's theorem on congruences of weights, in Serre's normalized form**: if `f` has
valuation `0` and `v (f - f') ≥ m`, then the weights of `f` and `f'` are congruent modulo
`(p - 1) p ^ (m - 1)`. The valuation hypotheses produce `p`-integral lifts
(`PowerSeries.Padic.v_nonneg_iff_rat`, `PowerSeries.Padic.map_toZModPow_eq_iff`), and the weights
are natural numbers because the forms are nonzero. -/
theorem natCast_eq_of_v_eq_zero_pow (hp : 5 ≤ p) (hm : 1 ≤ m) {k k' : ℤ}
    (f : rationalModularForms k) (f' : rationalModularForms k')
    (hv : v ((f : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])) = 0)
    (h : ((m : ℤ) : EInt) ≤ v ((f : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p]) -
      (f' : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p]))) :
    (k : ZMod ((p - 1) * p ^ (m - 1))) = (k' : ZMod ((p - 1) * p ^ (m - 1))) := by
  sorry

/-- **Serre's Théorème 1**, for `p ≥ 5`: if `f ≠ 0` and `f'` are level-one rational modular forms
of weights `k` and `k'` with `v (f - f') ≥ v f + m`, then `k' ≡ k mod (p - 1) p ^ (m - 1)`. The
scale-invariant hypothesis reduces to the normalized one by multiplying both forms by a power of
`p` with `v (c f) = 0` (`PowerSeries.rationalQExpansion_exists_zpow_smul_v_eq_zero`). The case
`m = 1` is `ModularForm.natCast_eq_of_v_sub_le`. -/
theorem natCast_eq_of_v_sub_le_pow (hp : 5 ≤ p) (hm : 1 ≤ m) {k k' : ℤ}
    (f : rationalModularForms k) (f' : rationalModularForms k') (hf : (f : ℚ⟦X⟧) ≠ 0)
    (h : v ((f : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])) + ((m : ℤ) : EInt) ≤
      v ((f : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p]) - (f' : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p]))) :
    (k : ZMod ((p - 1) * p ^ (m - 1))) = (k' : ZMod ((p - 1) * p ^ (m - 1))) := by
  sorry

end ModularForm
