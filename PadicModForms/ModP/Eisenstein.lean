/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.Bernoulli
public import PadicModForms.ModP.Defs
public import PadicModForms.Rational.Eisenstein

/-!
# Integral and mod-`p` Eisenstein series

This file defines the integral model of `E_rat` at `p` and the Eisenstein series of weight
`p - 1` used in the mod-`p` theory.
-/

@[expose] public noncomputable section

open PowerSeries ArithmeticFunction sigma

variable {p k : ℕ} [Fact p.Prime]

namespace EisensteinSeries

variable (hk : 3 ≤ k) (hk2 : Even k)

include hk hk2 in
/-- The coefficients of `E_rat k` are `p`-integral if `p - 1 ∣ k`. -/
theorem coeff_E_rat_mem_pLocalInt (hpk : p - 1 ∣ k) (n : ℕ) :
    coeff n (E_rat k) ∈ pLocalInt p := by
  by_cases hn : n = 0
  · simp [E_rat, hn]
  · have hk_mem : (k : ℚ) ∈ pLocalInt p := by simp
    have htwo_mem : (2 : ℚ) ∈ pLocalInt p := by simp
    have hsigma_mem : (σ (k - 1) n : ℚ) ∈ pLocalInt p := by simp
    grind [E_rat, coeff_mk, div_eq_mul_inv, inv_bernoulli_mem_pLocalInt, mul_mem, neg_mem]

/-- The normalized Eisenstein series `E_k` over the localization of `ℤ` at `p`. -/
noncomputable def E_int (hpk : p - 1 ∣ k) : (pLocalInt p)⟦X⟧ :=
  (E_rat k).toSubring (pLocalInt p).toSubring (coeff_E_rat_mem_pLocalInt hk hk2 hpk)

namespace ModP

/-- The normalized Eisenstein series of weight `p - 1` over the localization of `ℤ` at `p`. -/
noncomputable abbrev E (hp : 5 ≤ p) : (pLocalInt p)⟦X⟧ :=
  E_int (k := p - 1) (by lia) ((Fact.out : p.Prime).even_sub_one (by lia)) dvd_rfl

end ModP

end EisensteinSeries
