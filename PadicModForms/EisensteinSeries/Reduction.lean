module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

@[expose] public section

open ModularFormClass PowerSeries ArithmeticFunction sigma

namespace EisensteinSeries

variable {k : ℕ} (hk : 3 ≤ k)

theorem qExpansion_coeff (n : ℕ) (hk2 : Even k) : coeff n (qExpansion 1 (ModularForm.E hk)) =
    if n = 0 then 1 else  2 * k / (bernoulli k) * (σ (k - 1)) n := by
  let c : ℕ → ℂ := fun m ↦ ((if m = 0 then 1 else  2 * k / (bernoulli k) * (σ (k - 1)) m) : ℚ)
  change _ = c n
  refine (qExpansion_coeff_unique zero_lt_one (by simp) (fun z ↦ ?_) _).symm
  rw [EisensteinSeries.q_expansion_bernoulli _ hk2]

  sorry

end EisensteinSeries
