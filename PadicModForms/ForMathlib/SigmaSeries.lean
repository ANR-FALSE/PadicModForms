/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import PadicModForms.ForMathlib.Theta
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

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

open ArithmeticFunction sigma Finset Nat

/-! ### Powers in `ZMod p` -/

namespace ZMod

variable {p a b : ℕ} [Fact p.Prime]

-- should go to Mathlib.FieldTheory.Finite.Basic
/-- In `ZMod p` with `p` prime, a power of a nonzero element depends on the exponent only through
its class modulo `p - 1`, by Fermat's little theorem. -/
theorem pow_eq_pow_of_natCast_eq {x : ZMod p} (hx : x ≠ 0) (hab : (a : ZMod (p - 1)) = b) :
    x ^ a = x ^ b :=
  (isOfFinOrder_iff_pow_eq_one.mpr ⟨p - 1, by grind [(Fact.out : p.Prime).two_le],
    pow_card_sub_one_eq_one hx⟩).pow_eq_pow_iff_modEq.mpr
      (((natCast_eq_natCast_iff _ _ _).mp hab).of_dvd (orderOf_dvd_card_sub_one hx))

-- should go to Mathlib.FieldTheory.Finite.Basic
/-- A nonzero element of `ZMod p` satisfies `x ^ e = 1` as soon as `p - 1` divides `e`. -/
theorem pow_eq_one_of_card_sub_one_dvd {x : ZMod p} (hx : x ≠ 0) {e : ℕ} (he : p - 1 ∣ e) :
    x ^ e = 1 := by
  simp [pow_eq_pow_of_natCast_eq (b := 0) hx (by simpa using (natCast_eq_zero_iff _ _).mpr he)]

end ZMod

/-! ### Divisor sums modulo `p` -/

namespace ArithmeticFunction

variable {p a b k : ℕ} [Fact p.Prime]

-- should go to Mathlib.NumberTheory.ArithmeticFunction.Misc
omit [Fact p.Prime] in
/-- Every divisor of an integer prime to `p` is invertible modulo `p`. -/
theorem natCast_ne_zero_of_mem_divisors {n d : ℕ} (hn : ¬p ∣ n) (hd : d ∈ n.divisors) :
    (d : ZMod p) ≠ 0 :=
  fun h ↦ hn (((ZMod.natCast_eq_zero_iff _ _).mp h).trans (mem_divisors.mp hd).1)

-- should go to Mathlib.NumberTheory.ArithmeticFunction.Misc
/-- For `k ≠ 0`, `σ_k(p^j) ≡ 1 mod p`: every divisor of `p ^ j` other than `1` is a multiple of
`p`, so its `k`-th power vanishes modulo `p`. -/
theorem natCast_sigma_prime_pow (hk : k ≠ 0) (j : ℕ) : ((σ k (p ^ j) : ℕ) : ZMod p) = 1 := by
  rw [sigma_apply_prime_pow Fact.out, cast_sum, sum_eq_single 0 _ (by simp)]
  · simp
  · exact fun b _ hb ↦ by simp [cast_pow, zero_pow (mul_ne_zero hb hk)]

-- should go to Mathlib.NumberTheory.ArithmeticFunction.Misc
/-- For `k ≠ 0`, the reduction of `σ_k` modulo `p` ignores the `p`-part of its argument, by
multiplicativity of `σ_k` and `natCast_sigma_prime_pow`. -/
theorem natCast_sigma_prime_pow_mul (hk : k ≠ 0) (e : ℕ) {m : ℕ} (hpm : ¬p ∣ m) :
    ((σ k (p ^ e * m) : ℕ) : ZMod p) = ((σ k m : ℕ) : ZMod p) := by
  simp [isMultiplicative_sigma.map_mul_of_coprime
    (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpm).pow_left e), natCast_sigma_prime_pow hk]

-- should go to Mathlib.NumberTheory.ArithmeticFunction.Misc
/-- For `k ≠ 0` and `p` prime, `σ_k(pn) ≡ σ_k(n) mod p`: the divisors of `pn` that do not divide
`n` all carry the full power of `p` dividing `pn`, so their `k`-th powers vanish modulo `p`. -/
theorem natCast_sigma_mul_prime_left (hk : k ≠ 0) (n : ℕ) :
    ((σ k (p * n) : ℕ) : ZMod p) = ((σ k n : ℕ) : ZMod p) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  obtain ⟨e, m, hpm, rfl⟩ := exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
  rw [← mul_assoc, ← pow_succ', natCast_sigma_prime_pow_mul hk _ hpm,
    natCast_sigma_prime_pow_mul hk _ hpm]

-- should go to Mathlib.NumberTheory.ArithmeticFunction.Misc
/-- For `n` prime to `p`, the reduction of `σ_a(n)` modulo `p` only depends on the exponent `a`
modulo `p - 1`, every divisor of `n` being a unit modulo `p`. -/
theorem natCast_sigma_eq_of_natCast_eq (hab : (a : ZMod (p - 1)) = b) {n : ℕ} (hn : ¬p ∣ n) :
    ((σ a n : ℕ) : ZMod p) = ((σ b n : ℕ) : ZMod p) := by
  simp only [sigma_apply, cast_sum, cast_pow]
  exact sum_congr rfl fun d hd ↦
    ZMod.pow_eq_pow_of_natCast_eq (natCast_ne_zero_of_mem_divisors hn hd) hab

-- should go to Mathlib.NumberTheory.ArithmeticFunction.Misc
/-- For `n` prime to `p` and `p - 1 ∣ a + 1`, one has `n ^ a σ₁(n) = σ_a(n)` in `ZMod p`: pair
each divisor `d` of `n` with `n / d` and apply Fermat's little theorem. -/
theorem natCast_pow_mul_sigma_one (ha : p - 1 ∣ a + 1) {n : ℕ} (hn : ¬p ∣ n) :
    (n : ZMod p) ^ a * ((σ 1 n : ℕ) : ZMod p) = ((σ a n : ℕ) : ZMod p) := by
  simp only [sigma_apply, cast_sum, cast_pow, pow_one]
  rw [mul_sum, ← sum_div_divisors n fun d ↦ (d : ZMod p) ^ a]
  refine sum_congr rfl fun d hd ↦ ?_
  have hd0 : (d : ZMod p) ≠ 0 := natCast_ne_zero_of_mem_divisors hn hd
  obtain ⟨e, rfl⟩ := (mem_divisors.mp hd).1
  rw [Nat.mul_div_cancel_left e (pos_of_mem_divisors hd)]
  push_cast
  calc ((d : ZMod p) * e) ^ a * d = (d : ZMod p) ^ (a + 1) * (e : ZMod p) ^ a := by ring
    _ = (e : ZMod p) ^ a := by rw [ZMod.pow_eq_one_of_card_sub_one_dvd hd0 ha, one_mul]

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
  simp [← coeff_zero_eq_constantCoeff_apply]

theorem map_sigmaSeries {S : Type*} [Semiring S] (f : R →+* S) :
    (sigmaSeries R k).map f = sigmaSeries S k := by
  ext
  simp

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
  ext n
  by_cases hn : p ∣ n <;>
  simp [hn, ArithmeticFunction.natCast_sigma_eq_of_natCast_eq hab]

/-- Serre's series `ψ` as an iterate of `Θ`: for `p ≥ 3`,
`Θ^[p - 2] (∑ σ₁(n) qⁿ) = ∑_{p ∤ n} σ_{p-2}(n) qⁿ`. The coefficients with `p ∣ n` are killed by a
single application of `Θ`, and the others are computed by
`ArithmeticFunction.natCast_pow_mul_sigma_one`. -/
theorem iterate_Θ_sigmaSeries_one (hp : 3 ≤ p) :
    (Θ (R := ZMod p))^[p - 2] (sigmaSeries (ZMod p) 1) =
      sigmaSeriesPrimeTo (ZMod p) p (p - 2) := by
  sorry

end PowerSeries
