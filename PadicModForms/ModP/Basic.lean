/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ForMathlib.IntLocalization
public import PadicModForms.Rational.Basic

/-!
# Modular forms modulo `p`

This file defines modular forms modulo `p` and gives the modular forms of fixed weight their
linear structure.
-/

@[expose] public section

open PowerSeries ModularForm

variable {p : ℕ} [Fact p.Prime]

namespace PowerSeries

/-- A power series with coefficients in `ℤ/pℤ` is a mod-`p` modular form of weight `k` if it is
the reduction of a power series with coefficients in the localization of `ℤ` at `p` whose base
change to `ℚ` is a modular form of weight `k`. -/
public def isModPModularForm (k : ℤ) (f : (ZMod p)⟦X⟧) : Prop :=
  ∃ (g : (pLocalInt p)⟦X⟧) (F : rationalModularForms k),
    g.map (algebraMap _ _) = rationalQExpansion F ∧ g.map pLocalInt.toZMod = f

public theorem zero_isModPModularForm (k : ℤ) :
    isModPModularForm k (0 : (ZMod p)⟦X⟧) :=
  ⟨0, 0, by simp, by simp⟩

variable {k l : ℤ} {f g : (ZMod p)⟦X⟧} (hf : f.isModPModularForm k)
  (hg : g.isModPModularForm k)

theorem one_isModPModularForm : (1 : (ZMod p)⟦X⟧).isModPModularForm 0 :=
  ⟨1, 1, by simp, by simp⟩

include hf

theorem IsModPModularForm.neg : (-f).isModPModularForm k := by
  obtain ⟨f', F, hf'Q, hf'p⟩ := hf
  exact ⟨-f', -F, by simp [hf'Q], by simp [hf'p]⟩

public theorem IsModPModularForm.smul (a : ZMod p) : (a • f).isModPModularForm k := by
  obtain ⟨f', F, hf'Q, hf'p⟩ := hf
  refine ⟨(a.val : pLocalInt p) • f', (a.val : ℚ) • F, ?_, ?_⟩
  · calc _ = a.val • f'.map (algebraMap _ ℚ) := by
          ext n
          exact map_nsmul (algebraMap (pLocalInt p) ℚ) a.val (coeff n f')
      _ = (a.val : ℚ) • rationalQExpansion F := congrArg ((a.val : ℚ) • ·) hf'Q
      _ = rationalQExpansion ((a.val : ℚ) • F) := by rw [map_smul]
  · ext n
    have hn := congrArg (coeff n) hf'p
    rw [coeff_map] at hn
    simp [smul_eq_mul, map_mul, hn]

theorem IsModPModularForm.mul (hg : g.isModPModularForm l) : (f * g).isModPModularForm (k + l) := by
  obtain ⟨f', F, hf'Q, hf'p⟩ := hf
  obtain ⟨g', G, hg'Q, hg'p⟩ := hg
  exact ⟨f' * g', GradedMonoid.GMul.mul (A := fun n ↦ rationalModularForms n) F G,
    by simp [hf'Q, hg'Q], by simp [hf'p, hg'p]⟩

include hg

public theorem IsModPModularForm.add : (f + g).isModPModularForm k := by
  obtain ⟨f', F, hf'Q, hf'p⟩ := hf
  obtain ⟨g', G, hg'Q, hg'p⟩ := hg
  exact ⟨f' + g', F + G, by simp [hf'Q, hg'Q], by simp [hf'p, hg'p]⟩

/-- The mod-`p` modular forms of weight `k`, as a `ℤ/pℤ`-submodule of power series over
`ℤ/pℤ`. -/
public def _root_.modPModularForms (p : ℕ) [Fact p.Prime] (k : ℤ) :
    Submodule (ZMod p) (ZMod p)⟦X⟧ where
  carrier := {f | f.isModPModularForm k}
  zero_mem' := zero_isModPModularForm k
  add_mem' := IsModPModularForm.add
  smul_mem' a _ hf := IsModPModularForm.smul hf a

omit hf hg

@[simp]
theorem mem_modPModularForms : f ∈ modPModularForms p k ↔ f.isModPModularForm k := .rfl

end PowerSeries

/-- The submodules of mod-`p` modular forms form a graded monoid under multiplication. -/
public instance (p : ℕ) [Fact p.Prime] : SetLike.GradedMonoid (modPModularForms p) where
  one_mem := PowerSeries.one_isModPModularForm
  mul_mem _ _ := PowerSeries.IsModPModularForm.mul
