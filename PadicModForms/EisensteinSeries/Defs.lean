/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import PadicModForms.Defs.Modular
public import PadicModForms.ForMathlib.E2
public import PadicModForms.ForMathlib.IntLocalization
import PadicModForms.ForMathlib.Bernoulli

/-!
# Eisenstein series

This file defines Serre's series `P`, `Q`, and `R` as power series over `Q_p`.
-/

@[expose] public section

open UpperHalfPlane PowerSeries ArithmeticFunction sigma ModularForm

variable {p : ℕ} [Fact p.Prime] (n : ℕ)

namespace EisensteinSeries

/-- The rational `q`-expansion of the normalized Eisenstein series
of weight `k`. -/
noncomputable def E_rat (k : ℕ) : ℚ⟦X⟧ :=
  mk fun n ↦ if n = 0 then 1 else -(2 * k / bernoulli k : ℚ) * σ (k - 1) n

/-- The rational `q`-expansion Serre's Eisenstein series `G_k`, normalized so that its coefficient
of `q` is one. -/
noncomputable def G_rat (k : ℕ) : ℚ⟦X⟧ :=
  mk fun n ↦ if n = 0 then -(bernoulli k / (2 * k) : ℚ) else σ (k - 1) n

/-- `P = E_2, regarded as a power series over `Q_p`. -/
noncomputable def P : ℚ_[p]⟦X⟧ := (E_rat 2).map (algebraMap ℚ ℚ_[p])

/-- `Q = E_4, regarded as a power series over `Q_p`. -/
noncomputable def Q : ℚ_[p]⟦X⟧ := (E_rat 4).map (algebraMap ℚ ℚ_[p])

/-- `R = E_6 , regarded as a power series over `Q_p`. -/
noncomputable def R : ℚ_[p]⟦X⟧ := (E_rat 6).map (algebraMap ℚ ℚ_[p])

variable {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k)

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
  E_int (k := p - 1) (by lia) ((Fact.out : p.Prime).even_sub_one (by lia)) (dvd_refl (p - 1))

end ModP

end EisensteinSeries
