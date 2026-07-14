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

This file proves that the normalized Eisenstein series of weight `p - 1` is congruent to one
modulo `p`.
-/

@[expose] public section

open PowerSeries ArithmeticFunction sigma

variable {p : ℕ} [Hp : Fact p.Prime]

namespace EisensteinSeries

open ModP

/-- The normalized Eisenstein series of weight `p - 1` is congruent to `1` modulo `p`. -/
theorem E_p_sub_one_mod_p (hp : 5 ≤ p) : (E hp).map pLocalInt.toZMod = 1 := by
  let hk : 3 ≤ p - 1 := by lia
  let hk2 : Even (p - 1) := Hp.out.even_sub_one (by lia)
  let B_i : pLocalInt p := ⟨(bernoulli _)⁻¹, inv_bernoulli_mem_pLocalInt hk hk2 dvd_rfl⟩
  have hB_inv : pLocalInt.toZMod B_i = 0 := toZMod_inv_bernoulli_eq_zero hk hk2 dvd_rfl
  ext n
  by_cases hn : n = 0
  · simp [hn, coeff_E_int_zero hk hk2 dvd_rfl]
  have hcoeff : coeff n (E hp) = -(2 * (p - 1)) * B_i * σ (p - 2) n := by
      convert coeff_E_int_of_ne_zero hk hk2 dvd_rfl hn using 1
      simp [show 1 ≤ p by lia, show p - 1 - 1 = p - 2 by lia, B_i]
  simp [hn, hcoeff, map_mul, map_mul, map_neg, hB_inv]

end EisensteinSeries
