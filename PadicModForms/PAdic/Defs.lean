/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.Padics.PadicIntegers

public import PadicModForms.ForMathlib.ContinuousMonoidHom
public import PadicModForms.Rational.Basic
import PadicModForms.ForMathlib.PadicUnits
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.NormNum.Parity

/-!
# p-adic modular forms

This file defines p-adic weight space and p-adic modular forms as limits of rational classical
modular forms. A *presentation* of a p-adic modular form `f` (`pAdicModularFormStruct f`) is a
sequence of classical rational modular forms whose coefficients converge uniformly to those of
`f`; a `p`-adic power series is a p-adic modular form when it admits a presentation.
-/

public section

open UpperHalfPlane PowerSeries ModularFormClass Filter ModularForm

open scoped MatrixGroups Topology

variable {p : ℕ} [Fact p.Prime]

/-- The p-adic weight space. -/
notation "X_[" p "]" => ContinuousMonoidHom ℤ_[p]ˣ ℤ_[p]ˣ

/-- The classical integral weight `n`, regarded as a p-adic weight: the character `u ↦ u ^ n`
(`ι_apply`). -/
noncomputable def ι : ℤ → X_[p] := fun n ↦ ⟨zpowGroupHom n, by fun_prop⟩

@[simp]
theorem ι_apply (n : ℤ) (u : ℤ_[p]ˣ) : ι n u = u ^ n := by
  rw [ι]
  exact zpowGroupHom_apply n u

@[simp]
theorem ι_zero : ι (p := p) 0 = 1 := ContinuousMonoidHom.ext fun u ↦ by simp

/-- `ι` is a homomorphism from the integers to weight space. -/
@[simp]
theorem ι_add (m n : ℤ) : ι (p := p) (m + n) = ι m * ι n :=
  ContinuousMonoidHom.ext fun u ↦ by simp [zpow_add]

@[simp]
theorem ι_neg (n : ℤ) : ι (p := p) (-n) = (ι n)⁻¹ :=
  ContinuousMonoidHom.ext fun u ↦ by simp [zpow_neg]

@[simp]
theorem ι_sub (m n : ℤ) : ι (p := p) (m - n) = ι m / ι n :=
  ContinuousMonoidHom.ext fun u ↦ by simp [zpow_sub, div_eq_mul_inv]

/-- `ι` is injective: the unit `1 + p` of `ℤ_[p]` has infinite order. -/
theorem ι_injective : Function.Injective (ι (p := p)) := by
  intro m n h
  have h2 : (PadicInt.isUnit_one_add_natCast (p := p)).unit ^ (m - n) = 1 := by
    rw [zpow_sub, mul_inv_eq_one]
    simpa using congr($h (PadicInt.isUnit_one_add_natCast (p := p)).unit)
  have := zpow_eq_one_iff_modEq.1 h2
  rw [PadicInt.orderOf_unit_one_add_natCast, Nat.cast_zero, Int.modEq_iff_dvd, zero_dvd_iff]
    at this
  lia

@[simp]
theorem ι_inj {m n : ℤ} : ι (p := p) m = ι n ↔ m = n := ι_injective.eq_iff

/-- A presentation of a p-adic modular form by classical rational modular forms whose
coefficients converge uniformly. -/
structure pAdicModularFormStruct (f : ℚ_[p]⟦X⟧) where
  /-- The weights of the classical modular forms of the presentation. -/
  w : ℕ → ℤ
  /-- The classical rational modular forms of the presentation, `F i` having weight `w i`. -/
  F : (i : ℕ) → rationalModularForms (w i)
  /-- The coefficients of `F i` converge to those of `f` in `ℚ_[p]`, uniformly in the degree. -/
  tendsTo : TendstoUniformly (fun i n ↦ ↑(coeff n (rationalQExpansion (F i)))) (coeff · f) atTop

variable (p)

/-- A `p`-adic power series is a `p`-adic modular form if it admits a presentation by classical
rational modular forms. -/
@[expose]
def PowerSeries.isPAdicModularForm (f : ℚ_[p]⟦X⟧) := Nonempty (pAdicModularFormStruct f)

/-- The type of p-adic modular forms. -/
@[expose]
def PAdicModularForms := {f // PowerSeries.isPAdicModularForm p f}

namespace PAdicModularForms

variable {p}

/-- The zero power series is a `p`-adic modular form, presented by the zero form of weight `0`. -/
noncomputable instance : Zero (PAdicModularForms p) :=
  ⟨⟨0, ⟨⟨fun _ ↦ 0, fun _ ↦ 0, fun u hu ↦ by
    filter_upwards with i n
    simpa using refl_mem_uniformity hu⟩⟩⟩⟩

@[simp]
theorem val_zero : (0 : PAdicModularForms p).1 = 0 := rfl

theorem val_eq_zero_iff {f : PAdicModularForms p} : f.1 = 0 ↔ f = 0 :=
  ⟨fun h ↦ Subtype.ext (h.trans val_zero.symm), fun h ↦ h ▸ rfl⟩

end PAdicModularForms
