/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.IntLocalization
public import PadicModForms.Rational.Basic
import PadicModForms.ForMathlib.PowerSeries

/-!
# Modular forms over the localization of `ℤ` at `p`

This file defines the `p`-integral rational modular forms of fixed weight. They are power series
over `pLocalInt p` whose scalar extension to `ℚ` is the `q`-expansion of a rational modular form.
-/

@[expose] public section

open PowerSeries ModularForm

variable {p : ℕ} [Fact p.Prime]

namespace PowerSeries

/-- A power series over `pLocalInt p` is a `p`-integral modular form of weight `k` if its scalar
extension to `ℚ` is the `q`-expansion of a rational modular form of weight `k`. -/
public def isPLocalIntModularForm (k : ℤ) (f : (pLocalInt p)⟦X⟧) : Prop :=
  ∃ F : rationalModularForms k, f.map (algebraMap _ ℚ) = rationalQExpansion F

public theorem zero_isPLocalIntModularForm (k : ℤ) :
    isPLocalIntModularForm k (0 : (pLocalInt p)⟦X⟧) :=
  ⟨0, by simp⟩

variable {k l : ℤ} {f g : (pLocalInt p)⟦X⟧} (hf : f.isPLocalIntModularForm k)
  (hg : g.isPLocalIntModularForm k) (a : pLocalInt p)

theorem one_isPLocalIntModularForm : (1 : (pLocalInt p)⟦X⟧).isPLocalIntModularForm 0 :=
  ⟨1, by simp⟩

include hf

theorem IsPLocalIntModularForm.neg : (-f).isPLocalIntModularForm k := by
  obtain ⟨F, hF⟩ := hf
  exact ⟨-F, by simp [hF]⟩

public theorem IsPLocalIntModularForm.smul : (a • f).isPLocalIntModularForm k := by
  obtain ⟨F, hF⟩ := hf
  refine ⟨(a : ℚ) • F, ?_⟩
  ext n
  simpa using congrArg ((a : ℚ) * ·) (congrArg (coeff n) hF)

theorem IsPLocalIntModularForm.mul (hg : g.isPLocalIntModularForm l) :
    (f * g).isPLocalIntModularForm (k + l) := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨GradedMonoid.GMul.mul (A := fun n ↦ rationalModularForms n) F G, by simp [hF, hG]⟩

include hg

public theorem IsPLocalIntModularForm.add : (f + g).isPLocalIntModularForm k := by
  obtain ⟨F, hF⟩ := hf
  obtain ⟨G, hG⟩ := hg
  exact ⟨F + G, by simp [hF, hG]⟩

omit hf hg in
/-- Being a `p`-integral modular form is detected after clearing a nonzero scalar: if `c • f` is
one, so is `f`. In particular `pLocalIntModularForms p k` is saturated in `(pLocalInt p)⟦X⟧`. -/
public theorem IsPLocalIntModularForm.of_smul {c : pLocalInt p} (hc : c ≠ 0)
    (h : (c • f).isPLocalIntModularForm k) : f.isPLocalIntModularForm k := by
  obtain ⟨F, hF⟩ := h
  refine ⟨(c : ℚ)⁻¹ • F, ?_⟩
  ext m
  simp [← hF, ← mul_assoc, inv_mul_cancel₀ (fun h ↦ hc (Subtype.ext h))]

omit hg in
/-- A `p`-integral modular form all of whose coefficients are divisible by a nonzero `c` is `c`
times a `p`-integral modular form of the same weight. -/
public theorem IsPLocalIntModularForm.exists_smul_eq_of_forall_dvd_coeff {c : pLocalInt p}
    (hc : c ≠ 0) (hdvd : ∀ n, c ∣ coeff n f) :
    ∃ g : (pLocalInt p)⟦X⟧, g.isPLocalIntModularForm k ∧ c • g = f := by
  obtain ⟨g, hg⟩ := _root_.PowerSeries.exists_smul_eq_of_forall_dvd_coeff hdvd
  exact ⟨g, IsPLocalIntModularForm.of_smul hc (hg ▸ hf), hg⟩

/-- The `p`-integral rational modular forms of weight `k`, as a submodule of power series over
`pLocalInt p`. -/
public def _root_.pLocalIntModularForms (p : ℕ) [Fact p.Prime] (k : ℤ) :
    Submodule (pLocalInt p) (pLocalInt p)⟦X⟧ where
  carrier := {f | f.isPLocalIntModularForm k}
  zero_mem' := zero_isPLocalIntModularForm k
  add_mem' := IsPLocalIntModularForm.add
  smul_mem' a _ hf := IsPLocalIntModularForm.smul hf a

omit hf hg

@[simp]
theorem mem_pLocalIntModularForms :
    f ∈ pLocalIntModularForms p k ↔ f.isPLocalIntModularForm k :=
  Iff.rfl

omit hf hg in
/-- If there are no nonzero rational modular forms of weight `k`, there are no nonzero `p`-integral
ones either. -/
public theorem _root_.pLocalIntModularForms_eq_bot (h : rationalModularForms k = ⊥) :
    pLocalIntModularForms p k = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun f hf ↦ ?_
  obtain ⟨F, hF⟩ := hf
  refine map_injective _ pLocalInt.algebraMap_injective ?_
  rw [hF, rationalQExpansion_apply, (Submodule.eq_bot_iff _).1 h F F.2, map_zero]

end PowerSeries

/-! ### The graded structure -/

/-- The submodules of `p`-integral rational modular forms form a graded monoid under
multiplication. -/
public instance (p : ℕ) [Fact p.Prime] : SetLike.GradedMonoid (pLocalIntModularForms p) where
  one_mem := PowerSeries.one_isPLocalIntModularForm
  mul_mem _ _ := PowerSeries.IsPLocalIntModularForm.mul

namespace ModularForm

open DirectSum

/-- Forgetting the weight gives the `q`-expansion homomorphism from the graded ring of
`p`-integral modular forms to power series over `pLocalInt p`. -/
public noncomputable def pLocalIntQExpansionAlgHom :
    (⨁ i, pLocalIntModularForms p i) →ₐ[pLocalInt p] (pLocalInt p)⟦X⟧ :=
  coeAlgHom (pLocalIntModularForms p)

/-- Forgetting the weight of a form concentrated in weight `k` gives back its power series. -/
@[simp]
public theorem pLocalIntQExpansionAlgHom_of {k : ℤ} (f : pLocalIntModularForms p k) :
    pLocalIntQExpansionAlgHom (of _ k f) = f :=
  coeAlgHom_of ..

end ModularForm

namespace pLocalIntModularForms

open DirectSum

variable {i j l : ℤ}

/-- Taking a power in the graded ring of `p`-integral modular forms, with the resulting weight
computed. -/
theorem of_pow_eq_of {n : ℕ} (x : pLocalIntModularForms p i) (y : pLocalIntModularForms p j)
    (hij : n • i = j) (hxy : (x : (pLocalInt p)⟦X⟧) ^ n = (y : (pLocalInt p)⟦X⟧)) :
    (of (fun i ↦ pLocalIntModularForms p i) i x) ^ n = of _ j y := by
  subst hij
  simpa [ofPow] using congrArg _ (Subtype.ext hxy)

/-- Multiplying in the graded ring of `p`-integral modular forms, with the resulting weight
computed. -/
theorem of_mul_of_eq_of (x : pLocalIntModularForms p i) (y : pLocalIntModularForms p j)
    (z : pLocalIntModularForms p l) (hij : i + j = l)
    (hxyz : (x : (pLocalInt p)⟦X⟧) * (y : (pLocalInt p)⟦X⟧) = (z : (pLocalInt p)⟦X⟧)) :
    of (fun i ↦ pLocalIntModularForms p i) i x * of (fun i ↦ pLocalIntModularForms p i) j y =
      of (fun i ↦ pLocalIntModularForms p i) l z := by
  subst hij
  simpa [of_mul_of] using congrArg _ (Subtype.ext hxyz)

end pLocalIntModularForms
