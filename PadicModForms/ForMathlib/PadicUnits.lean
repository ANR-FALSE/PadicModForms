/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.FieldTheory.Finite.Basic

/-!
# Units of the `p`-adic integers

Topological and arithmetic facts about `ℤ_[p]ˣ`, the domain and the target of `p`-adic weight
space `Hom_cont(ℤ_[p]ˣ, ℤ_[p]ˣ)`:

* `ℤ_[p]ˣ` is compact, being closed in the compact space `ℤ_[p]`;
* a limit of units is a unit, the unit sphere being closed;
* the Fermat–Euler congruence `u ^ ((p - 1) p ^ (m - 1)) ≡ 1 mod p ^ m`, stated as a norm bound,
  and its consequence that `u ^ a` and `u ^ b` are `p ^ (-m)`-close whenever
  `(p - 1) p ^ (m - 1) ∣ a - b`. This is the uniform estimate behind the continuity of the map
  `k ↦ (u ↦ u ^ k)` from the integers to weight space.
-/

@[expose] public noncomputable section

open Filter Topology

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

-- should go to Mathlib.NumberTheory.Padics.ProperSpace
/-- The units of `ℤ_[p]` form a closed subset of `ℤ_[p]`, namely the unit sphere
(`PadicInt.isUnit_iff`). -/
theorem isClosed_range_units_val : IsClosed (Set.range ((↑) : ℤ_[p]ˣ → ℤ_[p])) := by
  have : Set.range ((↑) : ℤ_[p]ˣ → ℤ_[p]) = {x | ‖x‖ = 1} := Set.ext fun _ ↦ isUnit_iff
  simpa [this] using isClosed_eq continuous_norm continuous_const

-- should go to Mathlib.NumberTheory.Padics.ProperSpace
/-- The group of units of `ℤ_[p]` is compact: it is closed in the compact space `ℤ_[p]`, and its
topology is the subspace topology (`Units.isOpenEmbedding_val`). -/
instance : CompactSpace ℤ_[p]ˣ :=
  isCompact_univ_iff.1 <| Units.isOpenEmbedding_val.isInducing.isCompact_iff.2 <| by
    simpa using isClosed_range_units_val.isCompact

-- should go to Mathlib.NumberTheory.Padics.PadicIntegers
/-- A limit of units of `ℤ_[p]` is a unit: the unit sphere is closed. -/
theorem isUnit_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → ℤ_[p]ˣ} {x : ℤ_[p]}
    (h : Tendsto (fun i ↦ (u i : ℤ_[p])) l (𝓝 x)) : IsUnit x :=
  isUnit_iff.2 <|
    tendsto_nhds_unique h.norm (tendsto_const_nhds.congr fun i ↦ (norm_units (u i)).symm)

-- should go to Mathlib.NumberTheory.Padics.RingHoms
/-- An element of `ℤ_[p]` reducing to `0` modulo `p ^ m` has norm at most `p ^ (-m)`
(`PadicInt.ker_toZModPow`, `PadicInt.norm_le_pow_iff_mem_span_pow`). -/
theorem norm_le_pow_of_toZModPow_eq_zero {x : ℤ_[p]} {m : ℕ} (hx : toZModPow m x = 0) :
    ‖x‖ ≤ (p : ℝ) ^ (-(m : ℤ)) :=
  (norm_le_pow_iff_mem_span_pow x m).2 (by simp [← ker_toZModPow, RingHom.mem_ker.2 hx])

variable (u : ℤ_[p]ˣ) (m : ℕ)

-- should go to Mathlib.NumberTheory.Padics.RingHoms
/-- **Fermat–Euler in `ℤ_[p]`**: a unit raised to the power `φ(p ^ m)` reduces to `1` modulo
`p ^ m`. This is `ZMod.pow_totient` transported along `PadicInt.toZModPow`. -/
theorem toZModPow_pow_totient :
    toZModPow m ((u : ℤ_[p]) ^ Nat.totient (p ^ m)) = 1 := by
  have h : Units.map (toZModPow m).toMonoidHom (u ^ Nat.totient (p ^ m)) = 1 := by simp
  have := congr(Units.val $h)
  rwa [Units.coe_map, Units.val_pow_eq_pow_val, Units.val_one] at this

-- should go to Mathlib.NumberTheory.Padics.RingHoms
/-- An integer power of a unit of `ℤ_[p]` whose exponent is divisible by `(p - 1) p ^ (m - 1)`
reduces to `1` modulo `p ^ m`: for `m ≥ 1` the modulus is `φ(p ^ m)`, so this is Fermat–Euler
(`toZModPow_pow_totient`) through the order of the reduction of `u`. -/
theorem toZModPow_units_zpow_eq_one {n : ℤ} (hn : (((p - 1) * p ^ (m - 1) : ℕ) : ℤ) ∣ n) :
    toZModPow m ((u ^ n : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact (ZMod.subsingleton_iff.2 (pow_zero p)).allEq _ _
  suffices h : Units.map (toZModPow m).toMonoidHom (u ^ n) = 1 by
    have := congr(Units.val $h)
    rwa [Units.coe_map, Units.val_one] at this
  suffices h : (orderOf (Units.map (toZModPow m).toMonoidHom u) : ℤ) ∣ n by
    simpa [map_zpow] using orderOf_dvd_iff_zpow_eq_one.1 h
  suffices h : Units.map (toZModPow m).toMonoidHom u ^ Nat.totient (p ^ m) = 1 from
    (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one h)).trans
      (by rwa [Nat.totient_prime_pow (Fact.out : p.Prime) hm, mul_comm])
  exact ZMod.pow_totient _

-- should go to Mathlib.NumberTheory.Padics.RingHoms
/-- The integer-exponent form of `norm_pow_sub_one_le`: `u ^ n ≡ 1 mod p ^ m` whenever
`(p - 1) p ^ (m - 1) ∣ n`. -/
theorem norm_zpow_sub_one_le {n : ℤ} (hn : (((p - 1) * p ^ (m - 1) : ℕ) : ℤ) ∣ n) :
    ‖((u ^ n : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(m : ℤ)) :=
  norm_le_pow_of_toZModPow_eq_zero (by simp [toZModPow_units_zpow_eq_one u m hn])

-- should go to Mathlib.NumberTheory.Padics.RingHoms
/-- `u ^ ((p - 1) p ^ (m - 1)) ≡ 1 mod p ^ m` for a unit `u` of `ℤ_[p]`, as a norm bound. For
`m ≥ 1` the exponent is `φ(p ^ m)` (`Nat.totient_prime_pow`), and the kernel of `toZModPow m` is
the ideal of elements of norm at most `p ^ (-m)` (`PadicInt.ker_toZModPow`,
`PadicInt.norm_le_pow_iff_mem_span_pow`); for `m = 0` the bound is trivial. -/
theorem norm_pow_sub_one_le :
    ‖(u : ℤ_[p]) ^ ((p - 1) * p ^ (m - 1)) - 1‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  have := norm_zpow_sub_one_le u m (n := (((p - 1) * p ^ (m - 1) : ℕ) : ℤ)) dvd_rfl
  rwa [zpow_natCast, Units.val_pow_eq_pow_val] at this

-- should go to Mathlib.NumberTheory.Padics.RingHoms
/-- Two integer powers of a unit of `ℤ_[p]` whose exponents are congruent modulo
`(p - 1) p ^ (m - 1)` are congruent modulo `p ^ m`: `u ^ a - u ^ b = u ^ b (u ^ (a - b) - 1)` and
`u ^ b` has norm `1` (`PadicInt.norm_units`). -/
theorem norm_zpow_sub_zpow_le {a b : ℤ} (hab : (((p - 1) * p ^ (m - 1) : ℕ) : ℤ) ∣ a - b) :
    ‖((u ^ a : ℤ_[p]ˣ) : ℤ_[p]) - (u ^ b : ℤ_[p]ˣ)‖ ≤ (p : ℝ) ^ (-(m : ℤ)) :=
  calc _ = ‖((u ^ b : ℤ_[p]ˣ) : ℤ_[p]) * (((u ^ (a - b) : ℤ_[p]ˣ) : ℤ_[p]) - 1)‖ := by
        rw [mul_sub, mul_one, ← Units.val_mul, ← zpow_add, add_sub_cancel]
    _ ≤ ‖((u ^ b : ℤ_[p]ˣ) : ℤ_[p])‖ * ‖((u ^ (a - b) : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ := norm_mul_le _ _
    _ = ‖((u ^ (a - b) : ℤ_[p]ˣ) : ℤ_[p]) - 1‖ := by rw [norm_units, one_mul]
    _ ≤ _ := norm_zpow_sub_one_le u m hab

-- should go to Mathlib.NumberTheory.Padics.PadicIntegers
/-- `1 + p` is a unit of `ℤ_[p]`. -/
theorem isUnit_one_add_natCast : IsUnit (1 + p : ℤ_[p]) := by
  suffices (-(p : ℤ_[p])) ∈ nonunits ℤ_[p] by
    simpa [sub_neg_eq_add] using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ this
  rw [mem_nonunits, norm_neg, norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

-- should go to Mathlib.NumberTheory.Padics.PadicIntegers
/-- The unit `1 + p` of `ℤ_[p]` has infinite order: a power `(1 + p) ^ k` with `k ≠ 0` is a natural
number larger than `1`. -/
theorem orderOf_unit_one_add_natCast : orderOf (isUnit_one_add_natCast (p := p)).unit = 0 := by
  rw [orderOf_eq_zero_iff, isOfFinOrder_iff_pow_eq_one]
  rintro ⟨k, hk, hku⟩
  suffices (1 + p) ^ k = 1 by
    rcases Nat.pow_eq_one.1 this with h | h
    · exact (Fact.out : p.Prime).ne_zero (by omega)
    · exact hk.ne' h
  exact_mod_cast (by simpa using congr(Units.val $hku) : ((1 + p : ℕ) : ℤ_[p]) ^ k = 1)

end PadicInt
