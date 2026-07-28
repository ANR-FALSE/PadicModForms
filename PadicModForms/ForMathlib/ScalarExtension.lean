/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Algebra.Module.Lattice

/-!
# Scalar extension of submodules

Let `B` be an algebra over a commutative semiring `A`, let `M` be a `B`-module, and let
`M₀` be an `A`-submodule of `M`.

The class `Submodule.IsScalarExtensionInjective` says that `A`-linearly independent
families in `M₀` remain `B`-linearly independent in `M`. The stronger class
`Submodule.IsScalarExtensionEquiv` additionally says that `M₀` spans all of `M` over `B`.

Given an injective `B`-linear map `f : N →ₗ[B] M`, the comap
`M₀.comap (f.restrictScalars A)` always inherits `IsScalarExtensionInjective`. It satisfies
`IsScalarExtensionEquiv` precisely when it spans `N` over `B`; this extra condition cannot
be omitted for an arbitrary `B`-submodule of `M`.
-/

@[expose] public noncomputable section

open Module Submodule

namespace Submodule

variable {A B M N : Type*} [CommSemiring A] [Semiring B] [Algebra A B] [AddCommMonoid M]
  [Module A M] [Module B M] [IsScalarTower A B M] [AddCommMonoid N] [Module A N] [Module B N]
  [IsScalarTower A B N]

/-- An `A`-submodule `M₀` of a `B`-module `M` has injective scalar extension if every
`A`-linearly independent family in `M₀` remains `B`-linearly independent `M`. -/
class IsScalarExtensionInjective (B : outParam (Type*)) [Semiring B] [Algebra A B]
    [Module B M] [IsScalarTower A B M] (M₀ : Submodule A M) where
  map_linearIndependentOn (s : Set M₀) : LinearIndependent A ((↑) : s → M₀) →
    LinearIndependent B ((↑) : s → M)

/-- An `A`-submodule `M₀` of a `B`-module `M` has scalar extension equivalent to a `B`-module if
scalar extension is injective and its `B`-span is the whole ambient module. -/
class IsScalarExtensionEquiv (B : outParam (Type*)) [Semiring B] [Algebra A B] [Module B M]
    [IsScalarTower A B M] (M₀ : Submodule A M) extends IsScalarExtensionInjective B M₀ where
  span_eq_top : span B (M₀ : Set M) = ⊤

/-- An arbitrary indexed `A`-linearly independent family in `M₀` remains linearly independent
over `B` in `M`. -/
theorem IsScalarExtensionInjective.linearIndependent (M₀ : Submodule A M)
  [IsScalarExtensionInjective B M₀] {ι : Type*} (v : ι → M₀) (hv : LinearIndependent A v) :
    LinearIndependent B fun i ↦ (v i : M) := by
  let w : ι → Set.range v := fun i ↦ ⟨v i, Set.mem_range_self i⟩
  cases subsingleton_or_nontrivial A with
  | inl hA => let := Algebra.subsingleton A B; exact linearIndependent_of_subsingleton
  | inr hA =>
      have hw : Function.Injective w := fun i j hij ↦ hv.injective (congrArg Subtype.val hij)
      have hrange : LinearIndependent B (fun (x : Set.range v) ↦ (x : M)) :=
        IsScalarExtensionInjective.map_linearIndependentOn (Set.range v) hv.linearIndepOn_id
      simpa [Function.comp_def, w] using hrange.comp w hw

/-- The restricted map between a scalar-extension pullback and its target. -/
def scalarExtensionComapMap (M₀ : Submodule A M) (f : N →ₗ[B] M) :
    M₀.comap (f.restrictScalars A) →ₗ[A] M₀ :=
  .codRestrict _ ((f.restrictScalars A).domRestrict (M₀.comap _)) (fun x ↦ x.property)

@[simp]
theorem coe_scalarExtensionComapMap (M₀ : Submodule A M) (f : N →ₗ[B] M)
    (x : M₀.comap (f.restrictScalars A)) : (M₀.scalarExtensionComapMap f x : M) = f x :=
  rfl

theorem scalarExtensionComapMap_injective (M₀ : Submodule A M) {f : N →ₗ[B] M}
    (hf : Function.Injective f) : Function.Injective (M₀.scalarExtensionComapMap f) :=
  fun _ _ h ↦ Subtype.ext (hf <| congrArg Subtype.val h)

/-- Pullback along an injective `B`-linear map preserves injectivity of scalar extension. -/
theorem IsScalarExtensionInjective.comap (M₀ : Submodule A M)
    [IsScalarExtensionInjective B M₀] {f : N →ₗ[B] M} (hf : Function.Injective f) :
    IsScalarExtensionInjective B (M₀.comap (f.restrictScalars A)) where
  map_linearIndependentOn s hv := by
    have hgA := hv.map_injOn _ (M₀.scalarExtensionComapMap_injective hf).injOn
    exact LinearIndependent.of_comp f (by simpa [Function.comp_def] using
      IsScalarExtensionInjective.linearIndependent M₀ _ hgA)

/-- The pullback gives an equivalence when it spans the source after extending scalars. -/
theorem IsScalarExtensionEquiv.comap (M₀ : Submodule A M) [IsScalarExtensionInjective B M₀]
    {f : N →ₗ[B] M} (hf : Function.Injective f)
    (hspan : span B (M₀.comap (f.restrictScalars A) : Set N) = ⊤) :
    IsScalarExtensionEquiv B (M₀.comap (f.restrictScalars A)) where
  toIsScalarExtensionInjective := IsScalarExtensionInjective.comap M₀ hf
  span_eq_top := hspan

end Submodule

namespace Module.Basis

variable {A B M ι : Type*} [CommSemiring A] [Semiring B] [Algebra A B] [AddCommMonoid M]
  [Module A M] [Module B M] [IsScalarTower A B M] {M₀ : Submodule A M}
  [M₀.IsScalarExtensionEquiv B]

/-- Any `A`-basis of `M₀` becomes a `B`-basis of `M`. -/
def extendOfIsScalarExtensionEquiv (b : Basis ι A M₀) : Basis ι B M :=
  .mk (IsScalarExtensionInjective.linearIndependent M₀ b b.linearIndependent)
    (top_le_iff.mpr <| calc
      _ = span B (span A (Set.range fun i ↦ (b i : M))) := by rw [span_span_of_tower A]
      _ = span B (map M₀.subtype (span A (Set.range b))) := by
        rw [show (fun i ↦ (b i : M)) = M₀.subtype ∘ b from rfl, Set.range_comp, ← map_span]
      _ = ⊤ := by simp [b.span_eq, IsScalarExtensionEquiv.span_eq_top])

@[simp]
theorem extendOfIsScalarExtensionEquiv_apply (b : Basis ι A M₀) (i : ι) :
    b.extendOfIsScalarExtensionEquiv (B := B) i = b i := by
  simp [extendOfIsScalarExtensionEquiv]

end Module.Basis
