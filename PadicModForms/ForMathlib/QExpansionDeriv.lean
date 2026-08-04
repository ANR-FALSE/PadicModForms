/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ModularForms.Derivative
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import PadicModForms.ForMathlib.Theta

/-!
# The normalized derivative acts as `Θ` on `q`-expansions

For a function `f` on the upper half plane that is holomorphic, periodic of period `h` and
bounded at `i∞`, the normalized derivative `D = (2πi)⁻¹ d/dz` acts on the `q`-expansion of `f`
by multiplying the `n`-th coefficient by `n / h`. In other words `D` is the analytic incarnation
of the algebraic operator `PowerSeries.Θ`.

## Main results

* `UpperHalfPlane.cuspFunction_normalizedDeriv`: the cusp function of `D f` is
  `q ↦ h⁻¹ * q * (cusp function of f)' q`.
* `UpperHalfPlane.qExpansion_normalizedDeriv`: `qExpansion h (D f) = h⁻¹ • Θ (qExpansion h f)`.
* `UpperHalfPlane.qExpansion_normalizedDeriv_one`: the case `h = 1`, where `D` is exactly `Θ`.
* `UpperHalfPlane.qExpansion_normalizedDeriv_levelOne`: the same for a level-one modular form,
  whose hypotheses come from its `ModularFormClass` instance.
-/

@[expose] public noncomputable section

open UpperHalfPlane hiding I
open Complex Filter Function Derivative PowerSeries Periodic
open scoped Real Topology ModularForm Manifold

/-! ### Two general lemmas -/

/-- The `q`-parameter `z ↦ exp (2πiz/h)` has derivative `(2πi/h) q`. -/
theorem Function.Periodic.hasDerivAt_qParam (h : ℝ) (z : ℂ) :
    HasDerivAt (qParam h) (2 * π * I / h * qParam h z) z :=
  (((hasDerivAt_id z).const_mul _).div_const h).cexp.congr_deriv (by grind [qParam])

/-- Multiplying by the identity shifts Taylor coefficients: the `n`-th derivative of
`w ↦ w * g w` at `0` is `n` times the `n-1`-th derivative of `g`. -/
theorem iteratedDeriv_id_mul_zero {n : ℕ} {g : ℂ → ℂ} (hg : ContDiffAt ℂ n g 0) :
    iteratedDeriv n (fun w ↦ w * g w) 0 = n * iteratedDeriv (n - 1) g 0 := by
  rw [show (fun w : ℂ ↦ w * g w) = id * g from rfl,
    iteratedDeriv_mul contDiffAt_id hg, Finset.sum_eq_single 1]
  · simp [iteratedDeriv_id]
  · intro i _ hi
    simp [iteratedDeriv_id, hi]
  · intro hn
    simp [show n = 0 by grind [not_lt], iteratedDeriv_id]

namespace UpperHalfPlane

variable {h : ℝ} {f : ℍ → ℂ} {k : ℤ}

/-! ### The cusp function of `D f` -/

/-- A periodic function on the upper half plane factors through the `q`-parameter. -/
theorem comp_ofComplex_eq_cuspFunction_comp (hh : h ≠ 0) (hfper : Periodic (f ∘ ofComplex) h) :
    (f ∘ ofComplex) = cuspFunction h f ∘ qParam h :=
  funext fun z ↦ (Periodic.eq_cuspFunction hh hfper z).symm

section

variable (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f)
  (hfbdd : IsBoundedAtImInfty f)

include hh hfper hfhol hfbdd

/-- The normalized derivative in terms of the cusp function. -/
theorem normalizedDerivOfComplex_eq (τ : ℍ) : D f τ =
    (h : ℂ)⁻¹ * (qParam h τ * deriv (cuspFunction h f) (qParam h τ)) := by
  rw [normalizedDerivOfComplex, comp_ofComplex_eq_cuspFunction_comp hh.ne' hfper,
    ((differentiableAt_cuspFunction hh hfper hfhol hfbdd
    (Periodic.norm_qParam_lt_one hh τ.im_pos)).hasDerivAt.comp _ (hasDerivAt_qParam h τ)).deriv]
  field_simp

/-- `deriv` of the cusp function is analytic at `0`. -/
theorem analyticAt_deriv_cuspFunction : AnalyticAt ℂ (deriv (cuspFunction h f)) 0 :=
  (analyticAt_cuspFunction_zero hh hfper hfhol hfbdd).deriv

/-- Away from `q = 0`, the cusp function of `D f` is `h⁻¹ q F'(q)`. -/
theorem cuspFunction_normalizedDeriv_of_ne_zero {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    cuspFunction h (D f) w = (h : ℂ)⁻¹ * (w * deriv (cuspFunction h f) w) := by
  have him := im_invQParam_pos_of_norm_lt_one hh hw hw0
  rw [cuspFunction, cuspFunction_eq_of_nonzero _ _ hw0, comp_apply, ofComplex_apply_of_im_pos him]
  simpa [qParam_right_inv hh.ne' hw0]
    using normalizedDerivOfComplex_eq hh hfper hfhol hfbdd ⟨_, him⟩

/-- At `q = 0` the cusp function of `D f` vanishes: `D f` tends to `0` at `i∞`. -/
theorem cuspFunction_normalizedDeriv_zero : cuspFunction h (D f) 0 = 0 := by
  have hev : cuspFunction h (D f) =ᶠ[𝓝[≠] 0]
      fun w ↦ (h : ℂ)⁻¹ * (w * deriv (cuspFunction h f) w) := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Metric.ball_mem_nhds 0 one_pos), self_mem_nhdsWithin] with w hw hw0
    exact cuspFunction_normalizedDeriv_of_ne_zero hh hfper hfhol hfbdd (mem_ball_zero_iff.mp hw) hw0
  rw [cuspFunction, cuspFunction_zero_eq_limUnder_nhds_ne, ← cuspFunction]
  refine Tendsto.limUnder_eq ?_
  suffices hc : ContinuousAt (fun w ↦ (h : ℂ)⁻¹ * (w * deriv (cuspFunction h f) w)) 0 by
    suffices Tendsto (fun w ↦ h⁻¹ * (w * deriv (cuspFunction h f) w)) (𝓝 0) (𝓝 0) by
      simpa [tendsto_congr' hev] using this.mono_left nhdsWithin_le_nhds
    simpa using hc.tendsto
  exact continuousAt_const.mul <|
    continuousAt_id.mul (analyticAt_deriv_cuspFunction hh hfper hfhol hfbdd).continuousAt

/-- The cusp function of `D f`. -/
theorem cuspFunction_normalizedDeriv {w : ℂ} (hw : ‖w‖ < 1) :
    cuspFunction h (D f) w = (h : ℂ)⁻¹ * (w * deriv (cuspFunction h f) w) := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simpa using cuspFunction_normalizedDeriv_zero hh hfper hfhol hfbdd
  · exact cuspFunction_normalizedDeriv_of_ne_zero hh hfper hfhol hfbdd hw hw0

/-! ### The `q`-expansion of `D f` -/

/-- The normalized derivative multiplies the `n`-th `q`-expansion coefficient by `n / h`. -/
theorem qExpansion_normalizedDeriv : qExpansion h (D f) = (h : ℂ)⁻¹ • Θ ℂ (qExpansion h f) := by
  ext n
  have heq : cuspFunction h (D f) =ᶠ[𝓝 0]
      fun w ↦ (h : ℂ)⁻¹ * (w * deriv (cuspFunction h f) w) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with w hw
    exact cuspFunction_normalizedDeriv hh hfper hfhol hfbdd (mem_ball_zero_iff.mp hw)
  rw [qExpansion_coeff, heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field,
    iteratedDeriv_id_mul_zero (analyticAt_deriv_cuspFunction hh hfper hfhol hfbdd).contDiffAt]
  rcases n with _ | m
  · simp [qExpansion_coeff]
  · rw [Nat.add_sub_cancel, ← iteratedDeriv_succ']
    grind [coeff_smul, coeff_Θ, qExpansion_coeff, smul_eq_mul, nsmul_eq_mul]

end

/-- For period `1`, the normalized derivative is exactly `Θ` on `q`-expansions. -/
theorem qExpansion_normalizedDeriv_one (hfper : Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) : qExpansion 1 (D f) = Θ ℂ (qExpansion 1 f) := by
  simpa using qExpansion_normalizedDeriv one_pos hfper hfhol hfbdd

section LevelOne

open scoped MatrixGroups

/-- For a level-one modular form, `D` acts on `q`-expansions as `Θ`. -/
theorem qExpansion_normalizedDeriv_levelOne {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F 𝒮ℒ k]
    (g : F) : qExpansion 1 (D (g : ℍ → ℂ)) = Θ ℂ (qExpansion 1 (g : ℍ → ℂ)) :=
  qExpansion_normalizedDeriv_one (SlashInvariantFormClass.periodic_comp_ofComplex g
    one_mem_strictPeriods_SL) (ModularFormClass.holo g) (ModularFormClass.bdd_at_infty g)

end LevelOne

end UpperHalfPlane
