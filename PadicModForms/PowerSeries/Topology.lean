/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib

/-!
# The topology of uniform convergence on power series

For a uniform semiring `R`, we endow `R⟦X⟧` with the *uniform structure of uniform convergence of
coefficients*: a net of power series converges if and only if its sequences of coefficients converge
uniformly.

This is obtained by pulling back, along the coefficient map `f ↦ (n ↦ coeff n f)`, the uniform
structure of uniform convergence on `ℕ →ᵤ R` (`UniformFun`). It is **not** the product / pointwise
topology (`MvPowerSeries.WithPiTopology`), which is strictly coarser.

-/

@[expose] public section

open Filter Topology

namespace PowerSeries

namespace WithUniformConvergence

variable {R : Type*} [Ring R]

variable (R) in
/-- The coefficient map `f ↦ (n ↦ coeff n f)` as an additive monoid homomorphism
`R⟦X⟧ →+ (ℕ →ᵤ R)`. -/
noncomputable def coeffAddMonoidHom : R⟦X⟧ →+ UniformFun ℕ R where
  toFun f := UniformFun.ofFun fun n ↦ coeff n f
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem coeffAddMonoidHom_apply (f : R⟦X⟧) :
    coeffAddMonoidHom _ f = UniformFun.ofFun fun n ↦ coeff n f := rfl

variable [UniformSpace R]

/-- The uniform structure of uniform convergence (in the degree) of the coefficients on `R⟦X⟧`,
pulled back from `ℕ →ᵤ R` along the coefficient map. -/
noncomputable scoped instance : UniformSpace (R⟦X⟧) :=
  .comap (fun f ↦ UniformFun.ofFun fun n ↦ coeff n f) inferInstance

/-- A net `F` of power series converges to `f` in the topology of uniform convergence iff the
coefficient sequences `n ↦ coeff n (F i)` converge to `n ↦ coeff n f` uniformly in `n`. -/
theorem tendsto_iff_tendstoUniformly {ι : Type*} {l : Filter ι} {F : ι → R⟦X⟧} {f : R⟦X⟧} :
    Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i n ↦ coeff n (F i)) (coeff · f) l := by
  rw [(isUniformInducing_iff_uniformSpace.mpr rfl).isInducing.tendsto_nhds_iff]
  exact UniformFun.tendsto_iff_tendstoUniformly

/-- Addition on `R⟦X⟧` is continuous for the topology of uniform convergence of the coefficients.
It is pulled back along the (additive, inducing) coefficient map from `ℕ →ᵤ R`, where addition is
continuous because `R` is a uniform additive group. -/
instance [IsUniformAddGroup R] : ContinuousAdd R⟦X⟧ :=
  (isUniformInducing_iff_uniformSpace.mpr rfl).isInducing.continuousAdd (coeffAddMonoidHom R)

/-- The coefficient map is inducing for the topology of uniform convergence of the coefficients. -/
theorem isInducing_coeffAddMonoidHom : Topology.IsInducing (coeffAddMonoidHom R) :=
  (isUniformInducing_iff_uniformSpace.mpr rfl).isInducing

/-- The neighbourhood filter of `0 : R⟦X⟧` is the comap of the neighbourhood filter at `0` along
the coefficient map. -/
theorem nhds_zero_eq_comap_coeffAddMonoidHom :
    𝓝 (0 : R⟦X⟧) = Filter.comap (coeffAddMonoidHom R) (𝓝 0) := by
  rw [(isInducing_coeffAddMonoidHom (R := R)).nhds_eq_comap 0, map_zero]

/-- A neighbourhood basis of `0` in `R⟦X⟧`: for each neighbourhood `W` of `0` in `R`, the set of
power series all of whose coefficients lie in `W`. -/
theorem hasBasis_nhds_zero :
    (𝓝 (0 : R⟦X⟧)).HasBasis (· ∈ 𝓝 (0 : R)) ({f | ∀ n, coeff n f ∈ ·}) := by
  rw [nhds_zero_eq_comap_coeffAddMonoidHom]
  refine ((UniformFun.hasBasis_nhds ℕ R 0).comap _).to_hasBasis
    (fun V hV ↦ ⟨_, UniformSpace.ball_mem_nhds 0 hV, fun f hf ↦ fun n ↦ hf n⟩) (fun W hW ↦ ?_?_)
  rw [UniformSpace.mem_nhds_iff] at hW
  obtain ⟨V, hV, hVW⟩ := hW
  exact ⟨V, hV, fun f hf n ↦ hVW (hf n)⟩

/-- For each neighbourhood `W` of `0` in `R`, the set of power series with all coefficients in `W`
is a neighbourhood of `0` in `R⟦X⟧`. -/
theorem setOf_forall_coeff_mem_nhds {W : Set R} (hW : W ∈ 𝓝 (0 : R)) :
    {f : R⟦X⟧ | ∀ n, coeff n f ∈ W} ∈ 𝓝 (0 : R⟦X⟧) :=
  hasBasis_nhds_zero.mem_iff.mpr ⟨W, hW, subset_rfl⟩

variable [IsUniformAddGroup R]

/-- `R⟦X⟧` is a uniform additive group for the topology of uniform convergence of coefficients. -/
instance : IsUniformAddGroup R⟦X⟧ :=
  (isUniformInducing_iff_uniformSpace.2 rfl).isUniformAddGroup (coeffAddMonoidHom _)

/-- `R⟦X⟧` is a topological ring for the topology of uniform convergence of coefficients. -/
theorem isTopologicalRing [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] :
    IsTopologicalRing R⟦X⟧ := by
  refine IsTopologicalRing.of_addGroup_of_nhds_zero ?_ (fun x₀ ↦ ?_) (fun x₀ ↦ ?_)
  · rw [hasBasis_nhds_zero.tendsto_right_iff]
    rintro W hW
    obtain ⟨I, hI, hIW⟩ := (IsLinearTopology.hasBasis_submodule R).mem_iff.mp hW
    filter_upwards [Filter.prod_mem_prod (setOf_forall_coeff_mem_nhds hI)
      (setOf_forall_coeff_mem_nhds hI)] with p hp n
    rw [Function.uncurry_apply_pair, PowerSeries.coeff_mul]
    exact hIW (Submodule.sum_mem _ fun q _ ↦ Ideal.mul_mem_left I _ (hp.2 q.2))
  · rw [hasBasis_nhds_zero.tendsto_right_iff]
    rintro W hW
    obtain ⟨I, hI, hIW⟩ := (IsLinearTopology.hasBasis_submodule R).mem_iff.mp hW
    filter_upwards [setOf_forall_coeff_mem_nhds hI] with x hx n
    rw [PowerSeries.coeff_mul]
    exact hIW (Submodule.sum_mem _ fun q _ ↦ Ideal.mul_mem_left I _ (hx q.2))
  · rw [hasBasis_nhds_zero.tendsto_right_iff]
    rintro W hW
    obtain ⟨I, hI, hIW⟩ := IsLinearTopology.hasBasis_right_ideal.mem_iff.mp hW
    filter_upwards [setOf_forall_coeff_mem_nhds hI] with x hx n
    rw [PowerSeries.coeff_mul]
    refine hIW (Submodule.sum_mem _ fun q _ ↦ ?_)
    simpa using I.smul_mem (MulOpposite.op (coeff q.2 x₀)) (hx q.1)

instance [IsLinearTopology R R] [IsLinearTopology Rᵐᵒᵖ R] : IsTopologicalSemiring R⟦X⟧ :=
  haveI := isTopologicalRing (R := R)
  inferInstance

end WithUniformConvergence

end PowerSeries
