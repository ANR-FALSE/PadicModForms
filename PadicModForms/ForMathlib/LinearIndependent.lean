/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Linear independence: scalar extension and descent of bases

Let `σ : A →+* B` be a ring homomorphism, let `M` be an `A`-module, let `N` be a `B`-module and
let `f : M →ₛₗ[σ] N` be a `σ`-semilinear map. We study when a family `b : ι → M` whose image
`f ∘ b` is a `B`-basis of `N` is itself an `A`-basis of `M`.

## Main results

* `LinearIndependent.of_comp_semilinear`: if `σ` is injective and `f ∘ b` is `B`-linearly
  independent, then `b` is `A`-linearly independent.
* `top_le_span_range_of_comp_semilinear` and `Basis.ofCompSemilinear`: assuming moreover
  that `A` is a division ring and that `f` takes `A`-linearly independent sets to `B`-linearly
  independent ones, the family `b` is an `A`-basis of `M`.

-/

@[expose] public section

open Function Set Submodule Module LinearMap

open scoped PowerSeries

variable {A B M N ι : Type*}

section Ring

variable [Ring A] [Ring B] {σ : A →+* B}
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]

/-- If the image of a family under a semilinear map `f : M →ₛₗ[σ] N` is `B`-linearly independent
and `σ` is injective, then the family itself is `A`-linearly independent. -/
theorem LinearIndependent.of_comp_semilinear (f : M →ₛₗ[σ] N) (hσ : Injective σ) {b : ι → M}
    (h : LinearIndependent B (f ∘ b)) : LinearIndependent A b := by
  rw [linearIndependent_iff'] at h ⊢
  intro s g hg i hi
  have key : ∑ j ∈ s, σ (g j) • (f ∘ b) j = 0 := by simpa [comp_def] using congrArg f hg
  exact hσ (by simpa using h s _ key i hi)

end Ring

section Algebra

variable [CommRing A] [Ring B] [Algebra A B] [FaithfulSMul A B]
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]

/-- If the image of a family under a semilinear map `f : M →ₛₗ[algebraMap A B] N` is `B`-linearly
independent, then the family itself is `A`-linearly independent, provided `B` has no
`A`-torsion. -/
theorem LinearIndependent.of_comp_algebraMap (f : M →ₛₗ[algebraMap A B] N) {b : ι → M}
    (h : LinearIndependent B (f ∘ b)) : LinearIndependent A b :=
  h.of_comp_semilinear f (FaithfulSMul.algebraMap_injective A B)

end Algebra

section DivisionRing

variable [DivisionRing A] [Ring B] [Nontrivial B] {σ : A →+* B} [AddCommGroup M] [Module A M]
 [AddCommGroup N] [Module B N] (f : M →ₛₗ[σ] N)
 (hf : ∀ s : Set M, LinearIndepOn A id s → LinearIndepOn B f s) (b : ι → M) (c : Basis ι B N)

include hf

/-- If a semilinear map `f : M →ₛₗ[σ] N` takes `A`-linearly independent sets to `B`-linearly
independent ones and the image `f ∘ b` of a family `b : ι → M` is a `B`-basis of `N`, then `b`
spans `M`. -/
theorem top_le_span_range_of_comp_semilinear (hb : LinearIndependent B (f ∘ b))
    (hsp : span B (range (f ∘ b)) = ⊤) : span A (range b) = ⊤ := by
  refine eq_top_iff.2 fun m _ ↦ ?_
  by_contra hm
  have hmb : m ∉ range b := fun h ↦ hm (subset_span h)
  have h : LinearIndepOn B ⇑f (insert m (range b)) :=
    hf _ ((linearIndepOn_id_insert hmb).2
      ⟨(hb.of_comp_semilinear f σ.injective).linearIndepOn_id, hm⟩)
  apply h.linearIndependent.notMem_span_image (s := {x : ↥(insert m (range b)) | (x : M) ∈ range b})
    (x := ⟨m, mem_insert _ _⟩) (by simpa using hmb)
  have himg : (fun x : ↥(insert m (range b)) ↦ f x) '' {x | (x : M) ∈ range b} = range (f ∘ b) := by
    ext y
    refine ⟨?_, ?_⟩
    · rintro ⟨x, ⟨i, hi⟩, rfl⟩
      exact ⟨i, by simp [hi]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨b i, mem_insert_of_mem _ ⟨i, rfl⟩⟩, ⟨i, rfl⟩, rfl⟩
  rw [himg, hsp]
  exact mem_top

/-- Descent of a basis along a semilinear map: if `A` is a division ring, `f : M →ₛₗ[σ] N` takes
`A`-linearly independent sets to `B`-linearly independent ones and the image `f ∘ b` of a family
`b : ι → M` is a `B`-basis of `N`, then `b` is an `A`-basis of `M`. -/
noncomputable def Module.Basis.ofCompSemilinear (hc : c = f ∘ b) : Basis ι A M :=
  have hb : LinearIndependent B (f ∘ b) := hc ▸ c.linearIndependent
  .mk (hb.of_comp_semilinear f σ.injective) <|
    (top_le_span_range_of_comp_semilinear f hf _ hb (by rw [← hc]; exact c.span_eq)).ge

@[simp]
theorem Module.Basis.coe_ofCompSemilinear (hc : c = f ∘ b) :
    Basis.ofCompSemilinear f hf b c hc = b := by
  simp [Basis.ofCompSemilinear]

@[simp]
theorem Module.Basis.ofCompSemilinear_apply (hc : c = f ∘ b) (i : ι) :
    Basis.ofCompSemilinear f hf b c hc i = b i := by
  simp [Basis.ofCompSemilinear]

end DivisionRing

section CoeffPi

variable {R : Type*} [Semiring R]

/-- The `R`-linear map sending a power series to its family of coefficients. -/
noncomputable def PowerSeries.coeffPi : PowerSeries R →ₗ[R] ℕ → R :=
  pi fun n ↦ coeff n

theorem PowerSeries.coeffPi_injective : Injective (coeffPi (R := R)) :=
  fun _ _ hpq ↦ ext fun n ↦ congrFun hpq n

end CoeffPi

section Pi

variable [Field A] [Ring B] [Algebra A B]
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]

/-- A family of `A`-valued functions that is linearly independent over a field `A` stays linearly
independent after extending the scalars to an `A`-algebra `B`. -/
theorem linearIndependent_algebraMap_comp {X κ : Type*} (v : κ → X → A)
    (hv : LinearIndependent A v) : LinearIndependent B (fun k ↦ algebraMap A B ∘ v k) := by
  let e := Basis.ofVectorSpace A B
  have H (z : B) (a : A) (j) : e.repr (z * algebraMap A B a) j = e.repr z j * a := by
    rw [← Basis.coord_apply, ← Algebra.commutes, ← Algebra.smul_def, map_smul]
    simp [Basis.coord_apply, mul_comm]
  refine linearIndependent_iff'.2 fun s g hg k hk ↦ e.repr.injective (Finsupp.ext fun j ↦ ?_)
  have hrel : ∑ k ∈ s, e.repr (g k) j • v k = 0 := funext fun x ↦ by
    simpa [H, mul_comm] using congrArg (fun w : X → B ↦ e.coord j (w x)) hg
  simpa using linearIndependent_iff'.1 hv s _ hrel k hk

/-- A linearly independent family of power series over a field `A` remains linearly independent
after extending the coefficients to an `A`-algebra `B`. -/
theorem PowerSeries.linearIndependent_map {κ : Type*} (v : κ → A⟦X⟧)
    (hv : LinearIndependent A v) : LinearIndependent B (fun i ↦ (v i).map (algebraMap A B)) :=
  .of_comp coeffPi <| linearIndependent_algebraMap_comp _ <|
    hv.map' coeffPi (ker_eq_bot_of_injective coeffPi_injective)

end Pi

section Monomials

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {x : ι → S}

open MvPolynomial

/-- The monomials in an algebraically independent family are linearly independent. -/
theorem AlgebraicIndependent.linearIndependent_monomials (hx : AlgebraicIndependent R x) :
    LinearIndependent R (fun d : ι →₀ ℕ ↦ d.prod fun i n ↦ x i ^ n) := by
  have hli : LinearIndependent R (fun d ↦ aeval x (monomial d 1 : MvPolynomial ι R)) :=
    (basisMonomials ι R).linearIndependent.map' (aeval x).toLinearMap (ker_eq_bot_of_injective hx)
  simpa [aeval_monomial] using hli

end Monomials
