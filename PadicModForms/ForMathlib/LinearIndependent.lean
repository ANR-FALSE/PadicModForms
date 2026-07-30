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
  independent, then `b` is `A`-linearly independent. Nothing else is needed. In the case
  `σ = algebraMap A B`, injectivity of `σ` is `FaithfulSMul A B`, which holds as soon as `B` is an
  `A`-algebra without `A`-torsion, see `Module.IsTorsionFree.to_faithfulSMul`; this specialization
  is `LinearIndependent.of_comp_algebraMap`.
* `top_le_span_range_of_comp_semilinear` and `Module.Basis.ofCompSemilinear`: assuming moreover
  that `A` is a division ring and that `f` takes `A`-linearly independent sets to `B`-linearly
  independent ones, the family `b` is an `A`-basis of `M`.
* `Module.Basis.ofCompSemilinearPi` and `Module.Basis.ofCompSemilinearPowerSeries`: the hypothesis
  that `f` preserves linear independence is automatic when `A` is a field and `M` and `N` sit
  compatibly inside `X → A` and `X → B` with `M → (X → A)` injective, respectively inside
  `PowerSeries A` and `PowerSeries B`. The key point, `linearIndependent_algebraMap_comp`, is that
  linear independence of a family of `A`-valued functions is preserved by extension of scalars,
  since `B` is free as an `A`-module; `PowerSeries.linearIndependent_map` is its power series form.
* `AlgebraicIndependent.linearIndependent_monomials`: the monomials in an algebraically independent
  family are linearly independent. This is independent of the rest of the file.

The hypothesis that `f` preserves linear independence cannot be dropped, even for `A = B` a field
and `f` injective: take `A = B = ℚ`, `M = ℚ²`, `N = ℚ`, `f` the first projection and `b` the single
vector `(1, 0)`; then `f ∘ b` is a basis of `N` but `b` is not a basis of `M`. Taking `A = ℚ`,
`B = ℚ(t)`, `M = ℚ²`, `N = ℚ(t)` and `f (x, y) = x + t * y` gives a counterexample with `f`
injective. When `M` is `A`-free this hypothesis is precisely the injectivity of the induced map
`B ⊗[A] M → N`, which is why the versions for function spaces above ask for compatible embeddings
into `X → A` and `X → B` rather than merely for `f` to be injective.

No finiteness assumption on `M` or `N` is needed, and `ι` is an arbitrary index type.
-/

@[expose] public section

open Function Set Submodule

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

variable [DivisionRing A] [Ring B] [Nontrivial B] {σ : A →+* B}
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
variable (f : M →ₛₗ[σ] N) (hf : ∀ s : Set M, LinearIndepOn A id s → LinearIndepOn B f s)

include hf

/-- If a semilinear map `f : M →ₛₗ[σ] N` takes `A`-linearly independent sets to `B`-linearly
independent ones and the image `f ∘ b` of a family `b : ι → M` is a `B`-basis of `N`, then `b`
spans `M`. -/
theorem top_le_span_range_of_comp_semilinear {b : ι → M} (hb : LinearIndependent B (f ∘ b))
    (hsp : span B (range (f ∘ b)) = ⊤) : span A (range b) = ⊤ := by
  refine eq_top_iff.2 fun m _ ↦ ?_
  by_contra hm
  have hmb : m ∉ range b := fun h ↦ hm (subset_span h)
  have hins : LinearIndepOn B ⇑f (insert m (range b)) :=
    hf _ ((linearIndepOn_id_insert hmb).2
      ⟨(hb.of_comp_semilinear f σ.injective).linearIndepOn_id, hm⟩)
  refine hins.linearIndependent.notMem_span_image
    (s := {x : ↥(insert m (range b)) | (x : M) ∈ range b}) (x := ⟨m, mem_insert _ _⟩)
    (by simpa using hmb) ?_
  have himg : (fun x : ↥(insert m (range b)) ↦ f x) '' {x | (x : M) ∈ range b} =
      range (f ∘ b) := by
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
noncomputable def Module.Basis.ofCompSemilinear (b : ι → M) (c : Module.Basis ι B N)
    (hc : c = f ∘ b) : Module.Basis ι A M :=
  have hb : LinearIndependent B (f ∘ b) := hc ▸ c.linearIndependent
  .mk (hb.of_comp_semilinear f σ.injective) <|
    (top_le_span_range_of_comp_semilinear f hf hb (by rw [← hc]; exact c.span_eq)).ge

@[simp]
theorem Module.Basis.coe_ofCompSemilinear (b : ι → M) (c : Module.Basis ι B N) (hc : c = f ∘ b) :
    ⇑(Module.Basis.ofCompSemilinear f hf b c hc) = b := by
  simp [Module.Basis.ofCompSemilinear]

@[simp]
theorem Module.Basis.ofCompSemilinear_apply (b : ι → M) (c : Module.Basis ι B N) (hc : c = f ∘ b)
    (i : ι) : Module.Basis.ofCompSemilinear f hf b c hc i = b i := by
  simp [Module.Basis.ofCompSemilinear]

end DivisionRing

section CoeffPi

variable {R : Type*} [Semiring R]

/-- The `R`-linear map sending a power series to its family of coefficients. -/
noncomputable def PowerSeries.coeffPi : PowerSeries R →ₗ[R] ℕ → R :=
  LinearMap.pi fun n ↦ PowerSeries.coeff n

@[simp]
theorem PowerSeries.coeffPi_apply (p : PowerSeries R) (n : ℕ) :
    PowerSeries.coeffPi p n = PowerSeries.coeff n p :=
  rfl

theorem PowerSeries.coeffPi_injective : Injective (PowerSeries.coeffPi (R := R)) :=
  fun _ _ hpq ↦ PowerSeries.ext fun n ↦ congrFun hpq n

end CoeffPi

section Pi

variable [Field A] [Ring B] [Algebra A B]
variable [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]

/-- A family of `A`-valued functions that is linearly independent over a field `A` stays linearly
independent after extending the scalars to an `A`-algebra `B`.

This is the concrete form of the injectivity of `(X → A) ⊗[A] B → (X → B)`, which holds because `B`
is free as an `A`-module. -/
theorem linearIndependent_algebraMap_comp {X κ : Type*} (v : κ → X → A)
    (hv : LinearIndependent A v) : LinearIndependent B (fun k ↦ algebraMap A B ∘ v k) := by
  let e := Module.Basis.ofVectorSpace A B
  have H (z : B) (a : A) (j) : e.repr (z * algebraMap A B a) j = e.repr z j * a := by
    rw [← Module.Basis.coord_apply, ← Algebra.commutes, ← Algebra.smul_def, map_smul]
    simp [Module.Basis.coord_apply, mul_comm]
  refine linearIndependent_iff'.2 fun s g hg k hk ↦ e.repr.injective (Finsupp.ext fun j ↦ ?_)
  have hrel : ∑ k ∈ s, e.repr (g k) j • v k = 0 := funext fun x ↦ by
    simpa [H, mul_comm] using congrArg (fun w : X → B ↦ e.coord j (w x)) hg
  simpa using linearIndependent_iff'.1 hv s _ hrel k hk

/-- A linearly independent family of power series over a field `A` remains linearly independent
after extending the coefficients to an `A`-algebra `B`.

This is the power series form of `linearIndependent_algebraMap_comp`. -/
theorem PowerSeries.linearIndependent_map {κ : Type*} (v : κ → A⟦X⟧)
    (hv : LinearIndependent A v) :
    LinearIndependent B (fun i ↦ (v i).map (algebraMap A B)) := by
  refine LinearIndependent.of_comp PowerSeries.coeffPi ?_
  have hfun : (⇑PowerSeries.coeffPi ∘ fun i ↦ (v i).map (algebraMap A B)) =
      fun i ↦ ⇑(algebraMap A B) ∘ PowerSeries.coeffPi (v i) := by
    ext i n; simp
  rw [hfun]
  exact linearIndependent_algebraMap_comp _ (hv.map' PowerSeries.coeffPi
    (LinearMap.ker_eq_bot_of_injective PowerSeries.coeffPi_injective))

/-- If `f : M →ₛₗ[algebraMap A B] N` fits in a commutative square with an injective `A`-linear map
`g : M →ₗ[A] X → A` and a `B`-linear map `h : N →ₗ[B] X → B`, then `f` takes `A`-linearly
independent sets to `B`-linearly independent ones. -/
theorem linearIndepOn_comp_of_pi {X : Type*} (f : M →ₛₗ[algebraMap A B] N) (g : M →ₗ[A] X → A)
    (hg : Injective g) (h : N →ₗ[B] X → B)
    (hgh : ∀ (m : M) (x : X), h (f m) x = algebraMap A B (g m x)) (s : Set M)
    (hs : LinearIndepOn A id s) : LinearIndepOn B ⇑f s := by
  refine LinearIndependent.of_comp h ?_
  have hfun : (⇑h ∘ fun x : s ↦ f x) = fun x : s ↦ ⇑(algebraMap A B) ∘ g x :=
    funext fun x ↦ funext fun y ↦ hgh _ _
  rw [hfun]
  exact linearIndependent_algebraMap_comp (B := B) (fun x : s ↦ g x)
    (hs.linearIndependent.map' g (LinearMap.ker_eq_bot_of_injective hg))

/-- Descent of a basis along a semilinear map between modules of functions: if `A` is a field,
`M` embeds `A`-linearly in `X → A`, the semilinear map `f : M →ₛₗ[algebraMap A B] N` is compatible
with a `B`-linear map `N →ₗ[B] X → B`, and the image `f ∘ b` of a family `b : ι → M` is a
`B`-basis of `N`, then `b` is an `A`-basis of `M`. -/
noncomputable def Module.Basis.ofCompSemilinearPi [Nontrivial B] {X : Type*}
    (f : M →ₛₗ[algebraMap A B] N)
    (g : M →ₗ[A] X → A) (hg : Injective g) (h : N →ₗ[B] X → B)
    (hgh : ∀ (m : M) (x : X), h (f m) x = algebraMap A B (g m x)) (b : ι → M)
    (c : Module.Basis ι B N) (hc : c = f ∘ b) : Module.Basis ι A M :=
  .ofCompSemilinear f (linearIndepOn_comp_of_pi f g hg h hgh) b c hc

@[simp]
theorem Module.Basis.coe_ofCompSemilinearPi [Nontrivial B] {X : Type*}
    (f : M →ₛₗ[algebraMap A B] N)
    (g : M →ₗ[A] X → A) (hg : Injective g) (h : N →ₗ[B] X → B)
    (hgh : ∀ (m : M) (x : X), h (f m) x = algebraMap A B (g m x)) (b : ι → M)
    (c : Module.Basis ι B N) (hc : c = f ∘ b) :
    ⇑(Module.Basis.ofCompSemilinearPi f g hg h hgh b c hc) = b := by
  simp [Module.Basis.ofCompSemilinearPi]

@[simp]
theorem Module.Basis.ofCompSemilinearPi_apply [Nontrivial B] {X : Type*}
    (f : M →ₛₗ[algebraMap A B] N)
    (g : M →ₗ[A] X → A) (hg : Injective g) (h : N →ₗ[B] X → B)
    (hgh : ∀ (m : M) (x : X), h (f m) x = algebraMap A B (g m x)) (b : ι → M)
    (c : Module.Basis ι B N) (hc : c = f ∘ b) (i : ι) :
    Module.Basis.ofCompSemilinearPi f g hg h hgh b c hc i = b i := by
  simp [Module.Basis.ofCompSemilinearPi]

/-- Descent of a basis along a semilinear map compatible with power series expansions: if `A` is a
field, `M` embeds `A`-linearly into `PowerSeries A` via `g`, the semilinear map
`f : M →ₛₗ[algebraMap A B] N` is compatible with a `B`-linear map `h : N →ₗ[B] PowerSeries B` in the
sense that `h (f m)` is obtained from `g m` by applying `algebraMap A B` to all coefficients, and
the image `f ∘ b` of a family `b : ι → M` is a `B`-basis of `N`, then `b` is an `A`-basis of `M`.

This is the situation of `q`-expansions of modular forms: `M` is the space of modular forms of some
weight with rational coefficients, which sits inside `PowerSeries ℚ`, and `N` is the space of
complex modular forms of the same weight, which maps to `PowerSeries ℂ`. -/
noncomputable def Module.Basis.ofCompSemilinearPowerSeries [Nontrivial B]
    (f : M →ₛₗ[algebraMap A B] N) (g : M →ₗ[A] PowerSeries A) (hg : Injective g)
    (h : N →ₗ[B] PowerSeries B) (hgh : ∀ m : M, h (f m) = (g m).map (algebraMap A B)) (b : ι → M)
    (c : Module.Basis ι B N) (hc : c = f ∘ b) : Module.Basis ι A M :=
  have hgh' : ∀ (m : M) (n : ℕ), (PowerSeries.coeffPi.comp h) (f m) n =
      algebraMap A B ((PowerSeries.coeffPi.comp g) m n) := fun m n ↦ by
    simp [PowerSeries.coeffPi, hgh m]
  .ofCompSemilinearPi f (PowerSeries.coeffPi.comp g) (PowerSeries.coeffPi_injective.comp hg)
    (PowerSeries.coeffPi.comp h) hgh' b c hc

@[simp]
theorem Module.Basis.coe_ofCompSemilinearPowerSeries [Nontrivial B] (f : M →ₛₗ[algebraMap A B] N)
    (g : M →ₗ[A] PowerSeries A) (hg : Injective g) (h : N →ₗ[B] PowerSeries B)
    (hgh : ∀ m : M, h (f m) = (g m).map (algebraMap A B)) (b : ι → M) (c : Module.Basis ι B N)
    (hc : c = f ∘ b) : ⇑(Module.Basis.ofCompSemilinearPowerSeries f g hg h hgh b c hc) = b := by
  simp [Module.Basis.ofCompSemilinearPowerSeries]

@[simp]
theorem Module.Basis.ofCompSemilinearPowerSeries_apply [Nontrivial B]
    (f : M →ₛₗ[algebraMap A B] N) (g : M →ₗ[A] PowerSeries A) (hg : Injective g)
    (h : N →ₗ[B] PowerSeries B) (hgh : ∀ m : M, h (f m) = (g m).map (algebraMap A B)) (b : ι → M)
    (c : Module.Basis ι B N) (hc : c = f ∘ b) (i : ι) :
    Module.Basis.ofCompSemilinearPowerSeries f g hg h hgh b c hc i = b i := by
  simp [Module.Basis.ofCompSemilinearPowerSeries]

end Pi

section Monomials

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {x : ι → S}

open MvPolynomial

/-- The monomials in an algebraically independent family are linearly independent. -/
theorem AlgebraicIndependent.linearIndependent_monomials (hx : AlgebraicIndependent R x) :
    LinearIndependent R (fun d : ι →₀ ℕ ↦ d.prod fun i n ↦ x i ^ n) := by
  have hli : LinearIndependent R (fun d ↦ aeval x (monomial d 1 : MvPolynomial ι R)) :=
    (basisMonomials ι R).linearIndependent.map' (aeval x).toLinearMap
      (LinearMap.ker_eq_bot_of_injective hx)
  simpa [aeval_monomial] using hli

end Monomials
