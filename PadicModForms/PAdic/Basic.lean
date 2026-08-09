/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib

public import PadicModForms.ForMathlib.IntLocalization
public import PadicModForms.ForMathlib.PowerSeriesTopology
public import PadicModForms.PAdic.Defs
public import PadicModForms.Rational.Basic
public import PadicModForms.Rational.Graded
import PadicModForms.ForMathlib.EInt
import PadicModForms.ForMathlib.Padic
import PadicModForms.ForMathlib.SpecificLimits

/-!
# Basic results about p-adic modular forms and power series

This file develops the coefficientwise p-adic valuation on power series and records the basic
way in which a classical rational modular form gives a p-adic modular form.
-/

@[expose] public section

open Filter Topology PowerSeries Padic ModularForm ArithmeticFunction sigma

open scoped PowerSeriesUniformConvergence

variable {p : ℕ} [hp : Fact p.Prime] (n : ℕ) (f : ℚ_[p]⟦X⟧)

/-- A classical rational modular form gives a p-adic modular form after extending scalars. -/
theorem rationalQExpansion_isPAdicModularForm {k : ℤ} (F : rationalModularForms k) :
    (rationalQExpansion F).map (algebraMap ℚ ℚ_[p]) |>.isPAdicModularForm p := by
  refine ⟨⟨fun _ ↦ k, fun _ ↦ F, fun u hu ↦ ?_⟩⟩
  filter_upwards with i n
  simpa using refl_mem_uniformity hu

/-! ### The valuation of a `p`-adic power series -/

namespace PowerSeries.Padic

noncomputable local instance : UniformSpace (ℚ_[p]⟦X⟧) := WithUniformConvergence.uniformSpace

/-- The additive `p`-adic valuation of the `n`-th coefficient of a power series, viewed in the
extended integers `[-∞, ∞]`. -/
noncomputable abbrev coeffPadicValuation : EInt := Padic.addValuation (coeff n f)

/-- The valuation on `ℚ_[p]⟦X⟧`: for `f = ∑ aₙ Xⁿ` we set `v(f) = infₙ v_p(aₙ)`. -/
noncomputable def v : EInt := ⨅ n, coeffPadicValuation n f

theorem v_def : v f = ⨅ n, (addValuation (coeff n f) : EInt) := rfl

theorem v_le_coeffPadicValuation : v f ≤ coeffPadicValuation n f :=
  iInf_le ..

variable {m : EInt} {f}

theorem le_v_iff : m ≤ v f ↔ ∀ n : ℕ, m ≤ coeffPadicValuation n f :=
  le_iInf_iff

/-- A sequence of `p`-adic power series converges for the topology of uniform convergence of
coefficients iff the valuations of its differences from the limit tend to `∞`. -/
theorem tendsto_iff_v_sub_tendsto_nhds_top {F : ℕ → ℚ_[p]⟦X⟧} :
    Tendsto F atTop (𝓝 f) ↔ Tendsto (fun n ↦ v (F n - f)) atTop (𝓝 (⊤ : EInt)) := by
  rw [WithUniformConvergence.tendsto_iff_tendstoUniformly,
    Metric.tendstoUniformly_iff, tendsto_eint_nhds_top_iff]
  refine ⟨fun h k ↦ ?_, fun h ε hε ↦ ?_⟩
  · have hp : (0 : ℝ) < p := mod_cast hp.1.pos
    filter_upwards [h _ (zpow_pos hp (-k))] with i hi
    exact le_v_iff.2 fun n ↦ (intCast_le_addValuation_iff_norm_le_pow k _).2
      (le_of_lt (by simpa [dist_eq_norm'] using hi n))
  · obtain ⟨k, hk⟩ := exists_zpow_neg_lt (b := (p : ℝ)) (mod_cast hp.1.one_lt) hε
    filter_upwards [h k] with i hi n
    rw [dist_eq_norm', ← map_sub]
    exact ((intCast_le_addValuation_iff_norm_le_pow k _).1 (le_v_iff.1 hi n)).trans_lt hk

theorem v_nonneg_iff : 0 ≤ v f ↔ ∃ g : ℤ_[p]⟦X⟧, g.map (algebraMap _ _) = f := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · let a : ℕ → ℤ_[p] := fun n ↦ ⟨_, (zero_le_addValuation_iff_norm_le_one _).1 (le_v_iff.1 hf n)⟩
    exact ⟨.mk a, ext fun n ↦ by rw [coeff_map, coeff_mk, PadicInt.algebraMap_apply]⟩
  · rintro ⟨g, rfl⟩
    exact le_v_iff.2 fun n ↦ (zero_le_addValuation_iff_norm_le_one _).2
      (by simpa using (coeff n g).2)

theorem v_ne_bot_iff : v f ≠ ⊥ ↔ ∃ m : ℤ, ∀ n, m ≤ coeffPadicValuation n f :=
  eint_ne_bot_iff.trans (exists_congr fun _ ↦ le_v_iff)

theorem v_ne_bot_of_nonneg (hf : 0 ≤ v f) : v f ≠ ⊥ :=
  eint_ne_bot_of_nonneg hf

theorem v_ne_bot_iff_norm : v f ≠ ⊥ ↔ ∃ m : ℤ, ∀ n, ‖coeff n f‖ ≤ p ^ (-m) :=
  v_ne_bot_iff.trans
    (exists_congr fun m ↦ forall_congr' fun _ ↦ intCast_le_addValuation_iff_norm_le_pow m _)

theorem coeffPadicValuation_ne_bot (n) (f : ℚ_[p]⟦X⟧) : coeffPadicValuation n f ≠ ⊥ := by
  simp [coeffPadicValuation]

/-- A constant power series has finite valuation. -/
theorem v_C_ne_bot (c : ℚ_[p]) : v (C c) ≠ ⊥ := by
  obtain ⟨m, hm⟩ := eint_ne_bot_iff.1 (coeffPadicValuation_ne_bot 0 (C c))
  refine v_ne_bot_iff.2 ⟨m, fun n ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn <;> simp_all [coeffPadicValuation, coeff_C]

theorem v_ne_bot_add {f g : ℚ_[p]⟦X⟧} (hf : v f ≠ ⊥) (hg : v g ≠ ⊥) : v (f + g) ≠ ⊥ := by
  obtain ⟨m, hm⟩ := v_ne_bot_iff_norm.1 hf
  obtain ⟨m', hm'⟩ := v_ne_bot_iff_norm.1 hg
  have hp1 : (1 : ℝ) ≤ p := mod_cast hp.1.one_lt.le
  refine v_ne_bot_iff_norm.2 ⟨min m m', fun n ↦ (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le ((hm n).trans ?_) ((hm' n).trans ?_))⟩ <;>
  exact (zpow_le_zpow_right₀ hp1 (by lia))

/-- Multiplying by a series with integral coefficients keeps the valuation finite. -/
theorem v_ne_bot_mul_of_nonneg {f g : ℚ_[p]⟦X⟧} (hf : v f ≠ ⊥) (hg : 0 ≤ v g) : v (f * g) ≠ ⊥ := by
  obtain ⟨m, hm⟩ := v_ne_bot_iff_norm.1 hf
  have hg' (n : ℕ) : ‖coeff n g‖ ≤ 1 := (zero_le_addValuation_iff_norm_le_one _).1 (le_v_iff.1 hg n)
  have hppos : (0 : ℝ) < (p : ℝ) ^ (-m) := by
    have : (0 : ℝ) < p := mod_cast hp.1.pos
    positivity
  refine v_ne_bot_iff_norm.2 ⟨m, fun n ↦ ?_⟩
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hppos.le (fun ⟨i, j⟩ _  ↦ ?_)
  simpa using mul_le_mul (hm i) (hg' j) (norm_nonneg _) hppos.le

/-! ### Scaling by a constant -/

/-- Multiplying a power series by a nonzero constant shifts its valuation by the valuation of the
constant. -/
theorem v_C_mul {c : ℚ_[p]} (hc : c ≠ 0) : v (C c * f) = (addValuation c) + v f := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, addValuation c = m := ⟨_, addValuation.apply hc⟩
  have hcoe : addValuation c = (m : EInt) := by rw [hm]; simp [WithBotTop.coe]
  rw [v_def, v_def, hcoe, intCast_add_iInf]
  exact iInf_congr fun n ↦ by simp [coeff_C_mul, AddValuation.map_mul, ← hcoe, hm]

/-! ### Integrality criteria -/

/-- A rational power series has nonnegative `p`-adic valuation iff its coefficients come from the
localization of `ℤ` at the prime ideal generated by `p`. -/
theorem v_nonneg_iff_rat {f : ℚ⟦X⟧} :
    0 ≤ v (f.map (algebraMap ℚ ℚ_[p])) ↔ ∃ g : (pLocalInt p)⟦X⟧, g.map (algebraMap _ _) = f := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · have hcoeff n : coeff n f ∈ pLocalInt p :=
      (mem_pLocalInt_iff _).2 <| (zero_le_addValuation_ratCast_iff p (coeff n f)).1 <|
        by simpa using le_v_iff.1 hf n
    exact ⟨.mk fun n ↦ ⟨coeff n f, hcoeff n⟩, ext fun n ↦ by simp⟩
  · rintro ⟨g, rfl⟩
    exact le_v_iff.2 fun n ↦ (zero_le_addValuation_ratCast_iff _ _).2 <|
      (mem_pLocalInt_iff _).1 (coeff n g).2

theorem intCast_mem_pLocalInt (m : ℤ) : (m : ℚ) ∈ pLocalInt p := by
  simp

/-! ### Reduction modulo `p` -/

/-- A `p`-integral rational power series reduces to zero modulo `p` exactly when its valuation is
at least `1`. See `map_toZMod_eq_iff` for the version comparing two series. -/
theorem map_toZMod_eq_zero_iff {f : ℚ⟦X⟧} {g : (pLocalInt p)⟦X⟧} (hg : g.map (algebraMap _ ℚ) = f) :
    g.map pLocalInt.toZMod = 0 ↔ 1 ≤ v (f.map (algebraMap ℚ ℚ_[p])) := by
  rw [le_v_iff, PowerSeries.ext_iff]
  refine forall_congr' fun n ↦ ?_
  simpa [← hg] using (pLocalInt.one_le_addValuation_iff (coeff n g)).symm

/-- Two `p`-integral rational power series are congruent modulo `p` exactly when the valuation of
their difference is at least `1`. -/
theorem map_toZMod_eq_iff {f f' : ℚ⟦X⟧} {g g' : (pLocalInt p)⟦X⟧}
    (hg : g.map (algebraMap _ ℚ) = f) (hg' : g'.map (algebraMap _ ℚ) = f') :
    g.map pLocalInt.toZMod = g'.map pLocalInt.toZMod ↔
      1 ≤ v (f.map (algebraMap ℚ ℚ_[p]) - f'.map (algebraMap ℚ ℚ_[p])) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  exact map_toZMod_eq_zero_iff (by rw [map_sub, hg, hg'])

/-- A rational power series with `p`-integral coefficients has nonnegative valuation. -/
theorem v_map_nonneg_of_forall_mem {f : ℚ⟦X⟧} (h : ∀ n, coeff n f ∈ pLocalInt p) :
    0 ≤ v (f.map (algebraMap ℚ ℚ_[p])) :=
  v_nonneg_iff_rat.2 ⟨.mk fun n ↦ ⟨coeff n f, h n⟩, ext fun n ↦ by simp⟩

/-- `E₄` has integral `q`-expansion, so its valuation is nonnegative. -/
theorem v_E₄Rat_nonneg : 0 ≤ v (((E₄Rat : ℚ⟦X⟧)).map (algebraMap ℚ ℚ_[p])) := by
  refine v_map_nonneg_of_forall_mem fun n ↦ ?_
  rw [coeff_E₄Rat]
  split_ifs
  · exact one_mem _
  · rw [show (240 : ℚ) * (σ 3 n : ℚ) = ((240 * (σ 3 n : ℤ) : ℤ) : ℚ) by push_cast; ring]
    exact intCast_mem_pLocalInt _

/-- `E₆` has integral `q`-expansion, so its valuation is nonnegative. -/
theorem v_E₆Rat_nonneg : 0 ≤ v (((E₆Rat : ℚ⟦X⟧)).map (algebraMap ℚ ℚ_[p])) := by
  refine v_map_nonneg_of_forall_mem fun n ↦ ?_
  rw [coeff_E₆Rat]
  split_ifs
  · exact one_mem _
  · rw [show -(504 : ℚ) * (σ 5 n : ℚ) = ((-504 * (σ 5 n : ℤ) : ℤ) : ℚ) by push_cast; ring]
    exact intCast_mem_pLocalInt _

/-! ### Normalizing the valuation -/

/-- A power series with a nonzero coefficient has valuation `≠ ⊤`. -/
theorem v_ne_top_of_coeff_ne_zero {n : ℕ} (h : coeff n f ≠ 0) : v f ≠ ⊤ := fun htop ↦ by
  have h1 : (⊤ : EInt) ≤ coeffPadicValuation n f := htop ▸ v_le_coeffPadicValuation n f
  simp [coeffPadicValuation, addValuation.apply h] at h1

/-- A nonzero rational power series whose valuation is finite becomes of valuation exactly `0`
after scaling by a suitable power of `p`. -/
theorem exists_zpow_smul_v_eq_zero {f : ℚ⟦X⟧} (hf : f ≠ 0)
    (hbot : v (f.map (algebraMap ℚ ℚ_[p])) ≠ ⊥) :
    ∃ m : ℤ, v (((p : ℚ) ^ m • f).map (algebraMap ℚ ℚ_[p])) = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, coeff n f ≠ 0 := by
    by_contra! hc
    exact hf (ext fun n ↦ by simpa using (hc n))
  obtain ⟨m, hm⟩ := exists_intCast_eq hbot
    (v_ne_top_of_coeff_ne_zero (n := n) (by simpa using hn))
  have hc : ((p : ℚ_[p]) ^ (-m)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 hp.1.ne_zero)
  refine ⟨-m, ?_⟩
  rw [show ((p : ℚ) ^ (-m) • f).map (algebraMap ℚ ℚ_[p])
      = C ((p : ℚ_[p]) ^ (-m)) * f.map (algebraMap ℚ ℚ_[p]) by simp [smul_eq_C_mul]]
  rw [v_C_mul hc, addValuation.apply hc, valuation_zpow, valuation_p, mul_one, hm,
    show (WithBotTop.coe m) = ((m : WithTop ℤ) : EInt) from rfl, ← WithBot.coe_add,
    ← WithTop.coe_add]
  simp

end PowerSeries.Padic

namespace PowerSeries

open MvPolynomial in
/-- The p-adic valuations of the coefficients of a rational modular form are bounded below. -/
theorem rationalQExpansion_v_ne_bot {k : ℤ} (F : rationalModularForms k) :
    Padic.v ((rationalQExpansion F).map (algebraMap ℚ ℚ_[p])) ≠ ⊥ := by
  obtain ⟨P, hP⟩ := exists_qExpansion_eq_aeval F
  rw [rationalQExpansion_apply, hP]
  clear hP
  induction P using MvPolynomial.induction_on with
  | C a => simpa using Padic.v_C_ne_bot ((algebraMap ℚ ℚ_[p]) a)
  | add P Q hP hQ => simpa [map_add] using Padic.v_ne_bot_add hP hQ
  | mul_X P i hP =>
      rw [map_mul, map_mul]
      refine Padic.v_ne_bot_mul_of_nonneg hP ?_
      fin_cases i
      · simpa using Padic.v_E₄Rat_nonneg
      · simpa using Padic.v_E₆Rat_nonneg

/-- A nonzero rational modular form becomes of valuation exactly `0` after scaling by a suitable
power of `p`. This is the normalization used in Serre's theorem on congruences. -/
theorem rationalQExpansion_exists_zpow_smul_v_eq_zero {k : ℤ} (F : rationalModularForms k)
    (hF : (F : ℚ⟦X⟧) ≠ 0) :
    ∃ m : ℤ, Padic.v (((p : ℚ) ^ m • (F : ℚ⟦X⟧)).map (algebraMap ℚ ℚ_[p])) = 0 :=
  Padic.exists_zpow_smul_v_eq_zero hF (by simpa using rationalQExpansion_v_ne_bot F)

end PowerSeries
