/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The operator `Θ = q d/dq` on power series

For a power series `f = ∑ aₙ qⁿ` over a commutative semiring `R` this file defines
`Θ f = ∑ n aₙ qⁿ`, the operator classically written `q d/dq`.

It is defined as `X` times the formal derivative `PowerSeries.derivative`, and is bundled as a
`Derivation R R⟦X⟧ R⟦X⟧`. Additivity, `R`-linearity and the Leibniz rule are therefore inherited
from the `Derivation` API instead of being reproved coefficientwise.

## Main definitions

* `PowerSeries.Θ`: the operator `q d/dq`, as a `Derivation R R⟦X⟧ R⟦X⟧`.

## Main results

* `PowerSeries.coeff_Θ`: `Θ` multiplies the `n`-th coefficient by `n`.
* `PowerSeries.Θ_eq_mk`: the coefficientwise description of `Θ`.
* `PowerSeries.map_Θ`: `Θ` commutes with coefficientwise ring maps.
-/

@[expose] public noncomputable section

namespace PowerSeries

variable {R : Type*} [CommSemiring R]

-- should go to Mathlib.RingTheory.PowerSeries.Derivative
/-- The operator `Θ = q d/dq` on power series, sending `∑ aₙ qⁿ` to `∑ n aₙ qⁿ`. It is `X` times
the formal derivative, hence a derivation. -/
def Θ : Derivation R R⟦X⟧ R⟦X⟧ := (X : R⟦X⟧) • derivative R

theorem Θ_apply (f : R⟦X⟧) : Θ f = X * derivative R f := by
  rw [Θ, Derivation.smul_apply, smul_eq_mul]

@[simp]
theorem Θ_C (a : R) : Θ (C a) = 0 := by
  simp [Θ_apply]

@[simp]
theorem coeff_Θ (f : R⟦X⟧) (n : ℕ) : coeff n (Θ f) = n • coeff n f := by
  cases n with
  | zero => simp [Θ_apply]
  | succ n => simp [Θ_apply, coeff_succ_X_mul, coeff_derivative, mul_comm]

/-- The coefficientwise description of `Θ`: it sends `∑ aₙ qⁿ` to `∑ n aₙ qⁿ`. -/
theorem Θ_eq_mk (f : R⟦X⟧) : Θ f = mk fun n ↦ n • coeff n f :=
  ext fun n ↦ by simp

@[simp]
theorem constantCoeff_Θ (f : R⟦X⟧) : constantCoeff (Θ f) = 0 := by
  simp [Θ_apply]

/-- `Θ` commutes with extension of the coefficient ring: it only rescales coefficients by natural
numbers. -/
theorem map_Θ {S : Type*} [CommSemiring S] (φ : R →+* S) (f : R⟦X⟧) :
    (Θ f).map φ = Θ (f.map φ) :=
  ext fun n ↦ by simp [nsmul_eq_mul]

/-- The iterates of `Θ` multiply the `n`-th coefficient by `n ^ k`. -/
@[simp]
theorem coeff_iterate_Θ (k n : ℕ) (f : R⟦X⟧) :
    coeff n (((Θ (R := R)))^[k] f) = n ^ k • coeff n f := by
  sorry

end PowerSeries
