/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.PowerSeries.Topology
public import Mathlib

/-!
# Valuation on p-adic power series

-/

@[expose] public section

variable {p : ℕ} [Fact p.Prime]

open scoped PowerSeriesUniformConvergence

open Filter Topology PowerSeries Padic

namespace PowerSeries.Padic

noncomputable local instance : UniformSpace (ℚ_[p]⟦X⟧) :=
  PowerSeries.WithUniformConvergence.uniformSpace

/-- The additive `p`-adic valuation of the `n`-th coefficient of a power series, viewed in the
extended integers `[-∞, ∞]`. -/
noncomputable abbrev coeffPadicValuation (n : ℕ) (f : ℚ_[p]⟦X⟧) : EInt :=
  Padic.addValuation (coeff n f)

/-- The valuation on `ℚ_[p]⟦X⟧`: for `f = ∑ aₙ Xⁿ` we set `v(f) = infₙ v_p(aₙ)`. -/
noncomputable def v (f : ℚ_[p]⟦X⟧) : EInt :=
  ⨅ n, coeffPadicValuation n f

theorem v_def (f : ℚ_[p]⟦X⟧) : v f = ⨅ n, (addValuation (coeff n f) : EInt) :=
  rfl

theorem v_le_coeffPadicValuation (f : ℚ_[p]⟦X⟧) (n : ℕ) : v f ≤ coeffPadicValuation n f :=
  iInf_le ..

theorem le_v_iff {m : EInt} {f : ℚ_[p]⟦X⟧} : m ≤ v f ↔ ∀ n : ℕ, m ≤ coeffPadicValuation n f :=
  le_iInf_iff

private theorem tendsto_eint_nhds_top_iff {α : Type*} {l : Filter α} {u : α → EInt} :
    Tendsto u l (𝓝 (⊤ : EInt)) ↔ ∀ k : ℤ, ∀ᶠ a in l, (k : EInt) ≤ u a := by
  refine ⟨fun hu k ↦ hu.eventually (Ici_mem_nhds (WithBotTop.coe_ne_top k).lt_top), fun h ↦ ?_⟩
  rw [nhds_top_basis.tendsto_right_iff]
  intro a ha
  induction a using WithBotTop.rec with
  | bot => exact (h 0).mono fun x hx ↦ lt_of_lt_of_le (by simp [bot_lt_iff_ne_bot]) hx
  | coe k => exact (h (k + 1)).mono fun x hx ↦ lt_of_lt_of_le (by simp) hx
  | top => exact (lt_irrefl _ ha).elim

private theorem intCast_le_addValuation_iff_norm_le_pow (k : ℤ) (x : ℚ_[p]) :
    (k : EInt) ≤ (Padic.addValuation x : EInt) ↔ ‖x‖ ≤ (p : ℝ) ^ (-k) := by
  by_cases hx : x = 0
  · simp [hx, Padic.addValuation, zpow_nonneg (p.cast_nonneg : (0 : ℝ) ≤ p)]
  · have hp : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
    rw [Padic.addValuation.apply hx, Padic.norm_eq_zpow_neg_valuation hx,
      zpow_le_zpow_iff_right₀ hp, WithBotTop.coe, Function.comp_apply, WithBot.coe_le_coe,
      WithTop.coe_le_coe]
    omega

variable (p) in
private theorem exists_int_zpow_neg_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℤ, (p : ℝ) ^ (-k) < ε := by
  have hp : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp)
  exact ⟨n, by rwa [zpow_neg, zpow_natCast, ← inv_pow]⟩

/-- A sequence of `p`-adic power series converges for the topology of uniform convergence of
coefficients iff the valuations of its differences from the limit tend to `∞`. -/
theorem tendsto_iff_v_sub_tendsto_nhds_top {F : ℕ → ℚ_[p]⟦X⟧} {f : ℚ_[p]⟦X⟧} :
    Tendsto F atTop (𝓝 f) ↔ Tendsto (fun n ↦ v (F n - f)) atTop (𝓝 (⊤ : EInt)) := by
  rw [WithUniformConvergence.tendsto_iff_tendstoUniformly,
    Metric.tendstoUniformly_iff, tendsto_eint_nhds_top_iff]
  refine ⟨fun h k ↦ ?_, fun h ε hε ↦ ?_⟩
  · have hp : (0 : ℝ) < p := mod_cast (Fact.out : p.Prime).pos
    filter_upwards [h _ (zpow_pos hp (-k))] with i hi
    exact le_v_iff.2 fun n ↦ (intCast_le_addValuation_iff_norm_le_pow k _).2
      (le_of_lt (by simpa [dist_eq_norm'] using hi n))
  · obtain ⟨k, hk⟩ := exists_int_zpow_neg_lt p ε hε
    filter_upwards [h k] with i hi n
    rw [dist_eq_norm', ← map_sub]
    exact ((intCast_le_addValuation_iff_norm_le_pow k _).1 (le_v_iff.1 hi n)).trans_lt hk

private theorem zero_le_addValuation_iff_norm_le_one (x : ℚ_[p]) :
    0 ≤ (Padic.addValuation x : EInt) ↔ ‖x‖ ≤ 1 := by
  by_cases hx : x = 0 <;>
  simp_all [Padic.addValuation.apply, Padic.norm_le_one_iff_val_nonneg]

theorem v_nonneg_iff {f : ℚ_[p]⟦X⟧} : 0 ≤ v f ↔ ∃ g : ℤ_[p]⟦X⟧, g.map (algebraMap _ _) = f := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · exact ⟨.mk fun n ↦ ⟨coeff n f, (zero_le_addValuation_iff_norm_le_one _).1 (le_v_iff.1 hf n)⟩,
      ext fun n ↦ by simp [PadicInt.algebraMap_apply]⟩
  · rintro ⟨g, rfl⟩
    exact le_v_iff.2 fun n ↦ (zero_le_addValuation_iff_norm_le_one _).2
      (by simpa [PadicInt.algebraMap_apply] using (coeff n g).2)

end PowerSeries.Padic
