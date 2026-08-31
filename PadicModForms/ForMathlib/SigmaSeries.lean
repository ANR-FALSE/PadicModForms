/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import PadicModForms.ForMathlib.Theta
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Divisor-sum power series

For a semiring `R` and `k : ℕ` this file defines the divisor-sum power series
`PowerSeries.sigmaSeries R k = ∑_{n ≥ 1} σ_k(n) qⁿ`, together with its prime-to-`p` part
`PowerSeries.sigmaSeriesPrimeTo R p k = ∑_{p ∤ n} σ_k(n) qⁿ`.

Over `ZMod p` these series satisfy the identities used in the proof of the case `m ≥ 2` of Serre's
theorem on congruences of weights of modular forms:

* the Artin–Schreier identity `sigmaSeries - sigmaSeries ^ p = sigmaSeriesPrimeTo`
  (`sigmaSeries_sub_pow_prime`), Frobenius on `(ZMod p)⟦X⟧` being expansion of the variable by `p`;
* the exponent of the prime-to-`p` part only matters modulo `p - 1`
  (`sigmaSeriesPrimeTo_eq_of_natCast_eq`), by Fermat;
* the prime-to-`p` part of exponent `p - 2` is an iterate of `Θ = q d/dq` on the series of
  exponent `1` (`iterate_Θ_sigmaSeries_one`), by pairing each divisor `d` of `n` with `n / d`.

## Main definitions

* `PowerSeries.sigmaSeries`: the divisor-sum power series `∑_{n ≥ 1} σ_k(n) qⁿ`.
* `PowerSeries.sigmaSeriesPrimeTo`: its prime-to-`p` part `∑_{p ∤ n} σ_k(n) qⁿ`.

## Main results

* `PowerSeries.sigmaSeries_sub_pow_prime`: the Artin–Schreier identity
  `φ - φ ^ p = ψ` over `ZMod p`.
* `PowerSeries.sigmaSeriesPrimeTo_eq_of_natCast_eq`: `ψ` only depends on the exponent
  modulo `p - 1`.
* `PowerSeries.iterate_Θ_sigmaSeries_one`: `Θ^[p - 2] (∑ σ₁(n) qⁿ) = ∑_{p ∤ n} σ_{p-2}(n) qⁿ`.
-/

@[expose] public section

open ArithmeticFunction sigma Finset

/-! ### Divisor sums modulo `p` -/

namespace ArithmeticFunction

variable {p a b k : ℕ} [Fact p.Prime]

-- should go to Mathlib.NumberTheory.ArithmeticFunction.Misc
/-- For `k ≠ 0` and `p` prime, `σ_k(pn) ≡ σ_k(n) mod p`: the divisors of `pn` that do not divide
`n` all carry the full power of `p` dividing `pn`, so their `k`-th powers vanish modulo `p`. -/
theorem natCast_sigma_mul_prime_left (hk : k ≠ 0) (n : ℕ) :
    ((σ k (p * n) : ℕ) : ZMod p) = ((σ k n : ℕ) : ZMod p) := by
  sorry

-- should go to Mathlib.NumberTheory.ArithmeticFunction.Misc
/-- For `n` prime to `p`, the reduction of `σ_a(n)` modulo `p` only depends on the exponent `a`
modulo `p - 1`, every divisor of `n` being a unit modulo `p`. -/
theorem natCast_sigma_eq_of_natCast_eq (hab : (a : ZMod (p - 1)) = b) {n : ℕ} (hn : ¬p ∣ n) :
    ((σ a n : ℕ) : ZMod p) = ((σ b n : ℕ) : ZMod p) := by
  sorry

-- should go to Mathlib.NumberTheory.ArithmeticFunction.Misc
/-- For `n` prime to `p` and `p - 1 ∣ a + 1`, one has `n ^ a σ₁(n) = σ_a(n)` in `ZMod p`: pair
each divisor `d` of `n` with `n / d` and apply Fermat's little theorem. -/
theorem natCast_pow_mul_sigma_one (ha : p - 1 ∣ a + 1) {n : ℕ} (hn : ¬p ∣ n) :
    (n : ZMod p) ^ a * ((σ 1 n : ℕ) : ZMod p) = ((σ a n : ℕ) : ZMod p) := by
  sorry

end ArithmeticFunction

/-! ### The divisor-sum power series -/

namespace PowerSeries

variable (R : Type*) [Semiring R] (p k : ℕ)

-- should go to a new file Mathlib.NumberTheory.SigmaSeries
/-- The divisor-sum power series `∑_{n ≥ 1} σ_k(n) qⁿ`. The constant coefficient vanishes because
`σ k 0 = 0`. -/
def sigmaSeries : R⟦X⟧ := mk fun n ↦ (σ k n : R)

@[simp]
theorem coeff_sigmaSeries (n : ℕ) : coeff n (sigmaSeries R k) = ((σ k n : ℕ) : R) :=
  coeff_mk ..

@[simp]
theorem constantCoeff_sigmaSeries : constantCoeff (sigmaSeries R k) = 0 := by
  sorry

theorem map_sigmaSeries {S : Type*} [Semiring S] (φ : R →+* S) :
    (sigmaSeries R k).map φ = sigmaSeries S k := by
  sorry

/-- The prime-to-`p` part `∑_{p ∤ n} σ_k(n) qⁿ` of the divisor-sum power series. -/
def sigmaSeriesPrimeTo : R⟦X⟧ := mk fun n ↦ if p ∣ n then 0 else (σ k n : R)

@[simp]
theorem coeff_sigmaSeriesPrimeTo (n : ℕ) :
    coeff n (sigmaSeriesPrimeTo R p k) = if p ∣ n then 0 else ((σ k n : ℕ) : R) :=
  coeff_mk ..

/-! ### Identities over `ZMod p` -/

variable {p k} [Fact p.Prime]

/-- **The Artin–Schreier identity** for divisor-sum series: over `ZMod p` and for `k ≠ 0`,
`φ_k - φ_k ^ p = ψ_k`. The `p`-th power is expansion of the variable by `p`
(`PowerSeries.map_frobenius_expand`, Frobenius being the identity on `ZMod p`), and the divisor
sums match by `ArithmeticFunction.natCast_sigma_mul_prime_left`. -/
theorem sigmaSeries_sub_pow_prime (hk : k ≠ 0) :
    sigmaSeries (ZMod p) k - sigmaSeries (ZMod p) k ^ p = sigmaSeriesPrimeTo (ZMod p) p k := by
  sorry

/-- The prime-to-`p` divisor-sum series only depends on its exponent modulo `p - 1`. -/
theorem sigmaSeriesPrimeTo_eq_of_natCast_eq {a b : ℕ} (hab : (a : ZMod (p - 1)) = b) :
    sigmaSeriesPrimeTo (ZMod p) p a = sigmaSeriesPrimeTo (ZMod p) p b := by
  sorry

/-- Serre's series `ψ` as an iterate of `Θ`: for `p ≥ 3`,
`Θ^[p - 2] (∑ σ₁(n) qⁿ) = ∑_{p ∤ n} σ_{p-2}(n) qⁿ`. The coefficients with `p ∣ n` are killed by a
single application of `Θ`, and the others are computed by
`ArithmeticFunction.natCast_pow_mul_sigma_one`. -/
theorem iterate_Θ_sigmaSeries_one (hp : 3 ≤ p) :
    (Θ (R := ZMod p))^[p - 2] (sigmaSeries (ZMod p) 1) =
      sigmaSeriesPrimeTo (ZMod p) p (p - 2) := by
  sorry

end PowerSeries
