/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.EisensteinSeries.Basic
import PadicModForms.ForMathlib.Bernoulli

/-!
# Congruences for Eisenstein series

This file proves that a normalized Eisenstein series whose weight is divisible by `p - 1` is
congruent to one modulo `p`.
-/

@[expose] public section

open PowerSeries ArithmeticFunction sigma

variable {p : ℕ} [Hp : Fact p.Prime]

namespace EisensteinSeries

open ModP

/-- If `p - 1 ∣ k`, then the normalized Eisenstein series of weight `k` is congruent to `1`
modulo `p`. -/
theorem E_int_mod_p {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (hpk : p - 1 ∣ k) :
    (E_int hk hk2 hpk).map pLocalInt.toZMod = 1 := by
  let B_i : pLocalInt p := ⟨(bernoulli k)⁻¹, inv_bernoulli_mem_pLocalInt hk hk2 hpk⟩
  have hB_inv : pLocalInt.toZMod B_i = 0 := toZMod_inv_bernoulli_eq_zero hk hk2 hpk
  ext n
  by_cases hn : n = 0
  · simp [hn, coeff_E_int_zero hk hk2 hpk]
  have hcoeff : coeff n (E_int hk hk2 hpk) = -(2 * k) * B_i * σ (k - 1) n := by
    simpa [B_i] using coeff_E_int_of_ne_zero hk hk2 hpk hn
  simp [hn, hcoeff, map_mul, map_mul, map_neg, hB_inv]

/-- The normalized Eisenstein series of weight `p - 1` is congruent to `1` modulo `p`. -/
theorem E_p_sub_one_mod_p (hp : 5 ≤ p) : (E hp).map pLocalInt.toZMod = 1 := by
  exact E_int_mod_p (by lia) (Hp.out.even_sub_one (by lia)) dvd_rfl

end EisensteinSeries
