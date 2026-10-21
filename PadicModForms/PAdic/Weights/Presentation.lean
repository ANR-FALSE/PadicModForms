/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.PAdic.Basic
import PadicModForms.ForMathlib.EInt
import PadicModForms.PAdic.Weights.CongruencePow

/-!
# The weights of a presentation of a `p`-adic modular form

Let `f ≠ 0` be a `p`-adic modular form with presentation `S`: classical forms `S.F i` of weights
`S.w i` whose `q`-expansions converge uniformly to `f`. This file turns that convergence into
congruences between the weights, through Serre's Théorème 1
(`ModularForm.natCast_eq_of_v_sub_le_pow`): for every `m`, the weights `S.w i` are eventually
congruent modulo `(p - 1) p ^ (m - 1)`, and so are the weights of two presentations of the same
form.

The steps: `f` has finite valuation `v f`, the valuations `v (F i)` are eventually equal to it,
and `v (F i - F j) ≥ v f + m` for `i, j` large, which is exactly the hypothesis of Théorème 1.
The first part, about limits of sequences of `p`-adic power series, is stated in general.

## Main results

* `pAdicModularFormStruct.exists_forall_dvd_sub`: the weights of a presentation are Cauchy for
  the moduli `(p - 1) p ^ (m - 1)`.
* `pAdicModularFormStruct.eventually_dvd_sub`: two presentations of the same nonzero form have
  eventually congruent weights.
-/

@[expose] public noncomputable section

open Filter Topology PowerSeries PowerSeries.Padic ModularForm WithUniformConvergence

open scoped PowerSeriesUniformConvergence

variable {p : ℕ} [Fact p.Prime] {f : ℚ_[p]⟦X⟧}

namespace PowerSeries.Padic

/-! ### Limits of sequences of power series -/

variable {F G : ℕ → ℚ_[p]⟦X⟧}

/-- The limit of a sequence of series of finite valuation has finite valuation: for `i` large,
`v (F i - f) ≥ 0`, and `f = F i - (F i - f)` (`v_ne_bot_add`). -/
theorem v_ne_bot_of_tendsto (hF : Tendsto F atTop (𝓝 f)) (h : ∀ i, v (F i) ≠ ⊥) : v f ≠ ⊥ := by
  obtain ⟨i, hi⟩ :=
    (tendsto_eint_nhds_top_iff.1 (tendsto_iff_v_sub_tendsto_nhds_top.1 hF) 0).exists
  have := v_ne_bot_add (h i) (g := -(F i - f)) (by rw [v_neg]; exact v_ne_bot_of_nonneg hi)
  rwa [← sub_eq_add_neg, sub_sub_cancel] at this

/-- A sequence converging to a series of finite valuation eventually has the same valuation, by
the ultrametric inequality (`v_add_eq_left_of_lt`). -/
theorem eventually_v_eq_of_tendsto (hF : Tendsto F atTop (𝓝 f))
    (hbot : v f ≠ ⊥) (htop : v f ≠ ⊤) : ∀ᶠ i in atTop, v (F i) = v f := by
  obtain ⟨c, hc⟩ := exists_intCast_eq hbot htop
  filter_upwards [tendsto_eint_nhds_top_iff.1 (tendsto_iff_v_sub_tendsto_nhds_top.1 hF) (c + 1)]
    with i hi
  rw [← add_sub_cancel f (F i), v_add_eq_left_of_lt]
  rw [hc]
  exact (WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.2 (lt_add_one c))).trans_le hi

/-- Two sequences with the same limit become arbitrarily close to each other
(`tendsto_iff_v_sub_tendsto_nhds_top`, `le_v_add`). -/
theorem exists_forall_le_v_sub_of_tendsto (hF : Tendsto F atTop (𝓝 f))
    (hG : Tendsto G atTop (𝓝 f)) (c : ℤ) :
    ∃ N, ∀ i ≥ N, ∀ j ≥ N, (c : EInt) ≤ v (F i - G j) := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (tendsto_eint_nhds_top_iff.1 (tendsto_iff_v_sub_tendsto_nhds_top.1 hF) c)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
    (tendsto_eint_nhds_top_iff.1 (tendsto_iff_v_sub_tendsto_nhds_top.1 hG) c)
  refine ⟨max N₁ N₂, fun i hi j hj ↦ ?_⟩
  rw [← sub_add_sub_cancel (F i) f (G j)]
  exact le_v_add (hN₁ i (le_of_max_le_left hi))
    (by rw [v_sub_comm]; exact hN₂ j (le_of_max_le_right hj))

end PowerSeries.Padic

namespace pAdicModularFormStruct

variable (S : pAdicModularFormStruct f)

/-! ### Presentations -/

/-- The `q`-expansions of a presentation converge to `f` for the topology of uniform convergence
of the coefficients: this restates the field `tendsTo` through
`PowerSeries.tendsto_iff_tendstoUniformly`. -/
theorem tendsto_map :
    Tendsto (fun i ↦ (S.F i : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])) atTop (𝓝 f) := by
  simpa [tendsto_iff_tendstoUniformly, rationalQExpansion_apply] using S.tendsTo

include S in
/-- A `p`-adic modular form has finite valuation: it is a limit of classical forms, whose
coefficients have bounded valuations (`PowerSeries.rationalQExpansion_v_ne_bot`). -/
theorem v_ne_bot : v f ≠ ⊥ :=
  v_ne_bot_of_tendsto S.tendsto_map fun i ↦ by
    simpa [ModularForm.rationalQExpansion_apply] using rationalQExpansion_v_ne_bot (S.F i)

include S in
/-- The valuation of a nonzero `p`-adic modular form is an integer. -/
theorem exists_v_eq_intCast (hf : f ≠ 0) : ∃ c : ℤ, v f = c :=
  exists_intCast_eq S.v_ne_bot (v_eq_top_iff.not.2 hf)

/-- The forms of a presentation of a nonzero form eventually have its valuation. -/
theorem eventually_v_eq (hf : f ≠ 0) :
    ∀ᶠ i in atTop, v ((S.F i : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])) = v f :=
  eventually_v_eq_of_tendsto S.tendsto_map S.v_ne_bot (v_eq_top_iff.not.2 hf)

/-- The forms of a presentation of a nonzero form are eventually nonzero. -/
theorem eventually_ne_zero (hf : f ≠ 0) : ∀ᶠ i in atTop, (S.F i : ℚ⟦X⟧) ≠ 0 := by
  filter_upwards [S.eventually_v_eq hf] with i hi hzero
  exact v_eq_top_iff.not.2 hf (hi ▸ v_eq_top_iff.2 (by rw [hzero, _root_.map_zero]))

end pAdicModularFormStruct

namespace ModularForm

/-! ### Théorème 1 for presentations -/

variable {a b : ℕ → ℤ} {F : (i : ℕ) → rationalModularForms (a i)}
  {G : (i : ℕ) → rationalModularForms (b i)}

/-- Along two sequences of classical forms converging to the same nonzero `f`, the hypothesis of
Serre's Théorème 1 holds for `i, j` large: `F i ≠ 0` and `v (F i) + m ≤ v (F i - G j)`, since
`v (F i) = v f` eventually (`eventually_v_eq_of_tendsto`) and `v (F i - G j) ≥ v f + m`
eventually (`exists_forall_le_v_sub_of_tendsto`). -/
theorem exists_forall_v_add_le_v_sub_of_tendsto (hf : f ≠ 0)
    (hF : Tendsto (fun i ↦ (F i : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])) atTop (𝓝 f))
    (hG : Tendsto (fun i ↦ (G i : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])) atTop (𝓝 f)) (m : ℕ) :
    ∃ N, ∀ i ≥ N, ∀ j ≥ N, (F i : ℚ⟦X⟧) ≠ 0 ∧
      v ((F i : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])) + ((m : ℤ) : EInt) ≤
        v ((F i : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p]) - (G j : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])) := by
  have hbot : v f ≠ ⊥ := v_ne_bot_of_tendsto hF fun i ↦ by
    simpa [ModularForm.rationalQExpansion_apply] using rationalQExpansion_v_ne_bot (F i)
  have htop : v f ≠ ⊤ := v_eq_top_iff.not.2 hf
  obtain ⟨c, hc⟩ := exists_intCast_eq hbot htop
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (eventually_v_eq_of_tendsto hF hbot htop)
  obtain ⟨N₂, hN₂⟩ := exists_forall_le_v_sub_of_tendsto hF hG (c + m)
  refine ⟨max N₁ N₂, fun i hi j hj ↦ ?_⟩
  have hvi := hN₁ i (le_of_max_le_left hi)
  refine ⟨fun hzero ↦ htop (hvi ▸ v_eq_top_iff.2 (by rw [hzero, _root_.map_zero])), ?_⟩
  rw [hvi, hc, ← WithBotTop.coe_add]
  exact hN₂ i (le_of_max_le_right hi) j (le_of_max_le_right hj)

/-- **Théorème 1 for presentations**, for `p ≥ 5`: the weights of two sequences of classical
forms converging to the same nonzero `f` are eventually congruent modulo `(p - 1) p ^ (m - 1)`.
This is `natCast_eq_of_v_sub_le_pow` applied to `F i` and `G j` with the hypothesis provided by
`exists_forall_v_add_le_v_sub_of_tendsto`, the equality in `ZMod` being turned into a
divisibility by `ZMod.intCast_eq_intCast_iff_dvd_sub`. -/
theorem exists_forall_dvd_sub_of_tendsto (hp : 5 ≤ p) (hf : f ≠ 0)
    (hF : Tendsto (fun i ↦ (F i : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])) atTop (𝓝 f))
    (hG : Tendsto (fun i ↦ (G i : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])) atTop (𝓝 f)) (m : ℕ) :
    ∃ N, ∀ i ≥ N, ∀ j ≥ N, (((p - 1) * p ^ (m - 1) : ℕ) : ℤ) ∣ a i - b j := by
  obtain ⟨N, hN⟩ := exists_forall_v_add_le_v_sub_of_tendsto hf hF hG (max m 1)
  refine ⟨N, fun i hi j hj ↦ ?_⟩
  obtain ⟨hFi, hv⟩ := hN i hi j hj
  have := dvd_sub_comm.1 ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1
    (natCast_eq_of_v_sub_le_pow hp (le_max_right m 1) (F i) (G j) hFi hv))
  rwa [show max m 1 - 1 = m - 1 by lia] at this

end ModularForm

namespace pAdicModularFormStruct

variable (S : pAdicModularFormStruct f)

/-! ### The weights of a presentation -/

/-- **The weights of a presentation are Cauchy** for the moduli `(p - 1) p ^ (m - 1)`. For
`p ≥ 5` this is Théorème 1 for the presentation (`ModularForm.exists_forall_dvd_sub_of_tendsto`).
For `p = 2, 3` it follows from Serre's form of Théorème 1 for the small primes, whose moduli
`2 ^ (m - 2)` and `2 · 3 ^ (m - 1)` are cofinal with these; that case is not formalized. -/
theorem exists_forall_dvd_sub (hf : f ≠ 0) (m : ℕ) :
    ∃ N, ∀ i ≥ N, ∀ j ≥ N, (((p - 1) * p ^ (m - 1) : ℕ) : ℤ) ∣ S.w i - S.w j := by
  by_cases hp : 5 ≤ p
  · exact ModularForm.exists_forall_dvd_sub_of_tendsto hp hf S.tendsto_map S.tendsto_map m
  · sorry

/-- **Two presentations of the same nonzero form have eventually congruent weights**, modulo
every `(p - 1) p ^ (m - 1)`. Same proof as `exists_forall_dvd_sub`, for the two
presentations. -/
theorem eventually_dvd_sub (S' : pAdicModularFormStruct f) (hf : f ≠ 0) (m : ℕ) :
    ∀ᶠ i in atTop, (((p - 1) * p ^ (m - 1) : ℕ) : ℤ) ∣ S.w i - S'.w i := by
  by_cases hp : 5 ≤ p
  · obtain ⟨N, hN⟩ :=
      ModularForm.exists_forall_dvd_sub_of_tendsto hp hf S.tendsto_map S'.tendsto_map m
    exact eventually_atTop.2 ⟨N, fun i hi ↦ hN i hi i hi⟩
  · sorry

end pAdicModularFormStruct
