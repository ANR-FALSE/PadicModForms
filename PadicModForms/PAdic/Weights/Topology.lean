/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import PadicModForms.ForMathlib.PadicUnits
public import PadicModForms.PAdic.Defs
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Convergence in `p`-adic weight space

The weight space `X_[p] = Hom_cont(ℤ_[p]ˣ, ℤ_[p]ˣ)` carries the compact-open topology, induced
from `C(ℤ_[p]ˣ, ℤ_[p]ˣ)`. Since `ℤ_[p]ˣ` is compact, convergence in `X_[p]` is uniform convergence
of the underlying functions, viewed in `ℤ_[p]` (`WeightSpace.tendsto_iff_tendstoUniformly`). As
`ℤ_[p]` is complete, a sequence of weights that is uniformly Cauchy converges
(`WeightSpace.exists_tendsto_of_forall_exists_norm_sub_le`): the limit is built pointwise, it is
a continuous homomorphism with unit values, and the convergence to it is uniform.

Applied to the classical weights `ι k : u ↦ u ^ k`, together with the uniform estimate
`PadicInt.norm_zpow_sub_zpow_le`, this gives the two statements used for Serre's theorem on the
weights of `p`-adic modular forms.

## Main results

* `WeightSpace.exists_tendsto_ι_of_forall_exists_dvd`: a sequence of integers that is Cauchy for
  the moduli `(p - 1) p ^ (m - 1)` has convergent image in `X_[p]`.
* `WeightSpace.eq_of_tendsto_ι_of_forall_eventually_dvd`: two such sequences that are eventually
  congruent modulo every `(p - 1) p ^ (m - 1)` have the same limit.
-/

noncomputable section

open Filter Topology

variable {p : ℕ} [Fact p.Prime]

namespace WeightSpace

variable {ι' : Type*} {l : Filter ι'} {χ : ι' → X_[p]} {χ₀ : X_[p]}

/-! ### Convergence is uniform convergence -/

/-- A net `χ i` in `X_[p]` converges to `χ₀` exactly when the functions `u ↦ χ i u`, viewed in
`ℤ_[p]`, converge uniformly to `u ↦ χ₀ u`. The topology of `X_[p]` is induced from the
compact-open topology on `C(ℤ_[p]ˣ, ℤ_[p]ˣ)` (`ContinuousMonoidHom.isInducing_toContinuousMap`),
postcomposition with the embedding `ℤ_[p]ˣ → ℤ_[p]` is inducing
(`ContinuousMap.isInducing_postcomp`, `Units.isOpenEmbedding_val`), and on the compact space
`ℤ_[p]ˣ` compact convergence is uniform convergence
(`ContinuousMap.tendsto_iff_tendstoLocallyUniformly`). -/
public theorem tendsto_iff_tendstoUniformly : Tendsto χ l (𝓝 χ₀) ↔
    TendstoUniformly (fun i u ↦ (χ i u : ℤ_[p])) (fun u ↦ (χ₀ u : ℤ_[p])) l := by
  rw [(ContinuousMonoidHom.isInducing_toContinuousMap (A := ℤ_[p]ˣ) (B := ℤ_[p]ˣ)).tendsto_nhds_iff,
    (ContinuousMap.isInducing_postcomp (X := ℤ_[p]ˣ) ⟨Units.val, Units.continuous_val⟩
      Units.isOpenEmbedding_val.isInducing).tendsto_nhds_iff,
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace]
  rfl

/-- Evaluation at a unit is continuous: a convergent net of weights converges pointwise, in
`ℤ_[p]`. -/
theorem tendsto_apply (h : Tendsto χ l (𝓝 χ₀)) (u : ℤ_[p]ˣ) :
    Tendsto (fun i ↦ (χ i u : ℤ_[p])) l (𝓝 (χ₀ u : ℤ_[p])) :=
  (Units.continuous_val.tendsto _).comp (((continuous_eval_const u).tendsto χ₀).comp h)

/-! ### Completeness -/

/-- A uniform limit of weights is a weight: if the functions `u ↦ χ i u` converge uniformly to
`g : ℤ_[p]ˣ → ℤ_[p]`, then `g` takes unit values (`PadicInt.isUnit_of_tendsto`), is
multiplicative, and is continuous (`TendstoUniformly.continuous`), so it comes from an element
of `X_[p]`. -/
theorem exists_eq_of_tendstoUniformly [l.NeBot] {g : ℤ_[p]ˣ → ℤ_[p]}
    (hg : TendstoUniformly (fun i u ↦ (χ i u : ℤ_[p])) g l) :
    ∃ χ₀ : X_[p], ∀ u, (χ₀ u : ℤ_[p]) = g u := by
  have hpt (u : ℤ_[p]ˣ) : Tendsto (fun i ↦ (χ i u : ℤ_[p])) l (𝓝 (g u)) := hg.tendsto_at u
  -- The values of `g` are units, and `g` is multiplicative and continuous.
  obtain ⟨g', hg'⟩ : ∃ g' : ℤ_[p]ˣ → ℤ_[p]ˣ, ∀ u, (g' u : ℤ_[p]) = g u :=
    ⟨fun u ↦ (PadicInt.isUnit_of_tendsto (hpt u)).unit, fun u ↦ IsUnit.unit_spec _⟩
  have hmul (u v : ℤ_[p]ˣ) : g' (u * v) = g' u * g' v := Units.ext <| by
    rw [Units.val_mul, hg', hg', hg']
    exact tendsto_nhds_unique (hpt (u * v)) (by simpa [map_mul] using (hpt u).mul (hpt v))
  refine ⟨⟨MonoidHom.mk' g' hmul, ?_⟩, hg'⟩
  exact Units.isOpenEmbedding_val.isInducing.continuous_iff.2 <| by
      simpa [Function.comp_def, hg'] using hg.continuous (Eventually.of_forall fun i ↦
        (Units.continuous_val.comp (map_continuous (χ i)))).frequently

/-- **Weight space is sequentially complete**: a sequence of weights whose values are uniformly
`p ^ (-m)`-close for `i, j` large, for every `m`, converges in `X_[p]`. The limit is constructed
pointwise in the complete space `ℤ_[p]` (`cauchySeq_tendsto_of_complete`), the convergence to it
is uniform (`UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto`), and
`exists_eq_of_tendstoUniformly` and `tendsto_iff_tendstoUniformly` conclude. -/
theorem exists_tendsto_of_forall_exists_norm_sub_le {χ : ℕ → X_[p]}
    (h : ∀ m : ℕ, ∃ N, ∀ i ≥ N, ∀ j ≥ N, ∀ u : ℤ_[p]ˣ,
      ‖(χ i u : ℤ_[p]) - χ j u‖ ≤ (p : ℝ) ^ (-(m : ℤ))) :
    ∃ χ₀ : X_[p], Tendsto χ atTop (𝓝 χ₀) := by
  have hc : UniformCauchySeqOn (fun i u ↦ (χ i u : ℤ_[p])) atTop Set.univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨m, hm⟩ := PadicInt.exists_pow_neg_lt (p := p) hε
    obtain ⟨N, hN⟩ := h m
    exact ⟨N, fun i hi j hj u _ ↦ (dist_eq_norm _ _).trans_lt ((hN i hi j hj u).trans_lt hm)⟩
  choose g hg using fun u ↦ cauchySeq_tendsto_of_complete (hc.cauchySeq (Set.mem_univ u))
  have hu : TendstoUniformly (fun i u ↦ (χ i u : ℤ_[p])) g atTop :=
    tendstoUniformlyOn_univ.1 (hc.tendstoUniformlyOn_of_tendsto fun u _ ↦ hg u)
  obtain ⟨χ₀, hχ₀⟩ := exists_eq_of_tendstoUniformly hu
  rw [show g = fun u ↦ (χ₀ u : ℤ_[p]) from funext fun u ↦ (hχ₀ u).symm] at hu
  exact ⟨χ₀, tendsto_iff_tendstoUniformly.2 hu⟩

/-! ### Sequences of classical weights -/

variable {a b : ℕ → ℤ}

/-- A sequence of integers that is Cauchy for the moduli `(p - 1) p ^ (m - 1)` has convergent
image in `X_[p]`, by `PadicInt.norm_zpow_sub_zpow_le` and
`exists_tendsto_of_forall_exists_norm_sub_le`. -/
public theorem exists_tendsto_ι_of_forall_exists_dvd
    (h : ∀ m : ℕ, ∃ N, ∀ i ≥ N, ∀ j ≥ N, (((p - 1) * p ^ (m - 1) : ℕ) : ℤ) ∣ a i - a j) :
    ∃ x : X_[p], Tendsto (fun i ↦ ι (a i)) atTop (𝓝 x) := by
  refine exists_tendsto_of_forall_exists_norm_sub_le fun m ↦ ?_
  obtain ⟨N, hN⟩ := h m
  exact ⟨N, fun i hi j hj u ↦ by simpa using PadicInt.norm_zpow_sub_zpow_le u m (hN i hi j hj)⟩

/-- Two sequences of integers that are eventually congruent modulo every `(p - 1) p ^ (m - 1)`
have the same limit in `X_[p]`, if any: evaluate at each unit (`tendsto_apply`), where the
sequences `u ^ (a i)` and `u ^ (b i)` are eventually `p ^ (-m)`-close
(`PadicInt.norm_zpow_sub_zpow_le`), hence have the same limit in the Hausdorff space `ℤ_[p]`. -/
public theorem eq_of_tendsto_ι_of_forall_eventually_dvd {x x' : X_[p]}
    (hx : Tendsto (fun i ↦ ι (a i)) atTop (𝓝 x)) (hx' : Tendsto (fun i ↦ ι (b i)) atTop (𝓝 x'))
    (h : ∀ m : ℕ, ∀ᶠ i in atTop, (((p - 1) * p ^ (m - 1) : ℕ) : ℤ) ∣ a i - b i) : x = x' := by
  refine ContinuousMonoidHom.ext fun u ↦ Units.ext ?_
  refine tendsto_nhds_unique (tendsto_apply hx u) ((tendsto_apply hx' u).congr_dist ?_)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := PadicInt.exists_pow_neg_lt (p := p) hε
  filter_upwards [h m] with i hi
  simpa [dist_eq_norm] using (PadicInt.norm_zpow_sub_zpow_le u m (dvd_sub_comm.1 hi)).trans_lt hm

end WeightSpace
