/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ModP.Weights
public import PadicModForms.PAdic.Basic

/-!
# Congruent rational modular forms have congruent weights

Let `p ≥ 5`. If two rational modular forms of weights `k` and `k'` are congruent modulo `p`, and
the first one is not congruent to `0`, then `k ≡ k' mod (p - 1)`. This is the case `m = 1` of
Serre's first theorem on congruences between modular forms, stated for classical rational forms
rather than for their reductions.

Everything is deduced from `ModularForm.natCast_eq_of_mem_modPModularForms`, the corresponding
statement about mod-`p` modular forms: a congruence between `p`-integral rational forms is exactly
an equality of their reductions, so the two forms give the *same* mod-`p` modular form, of weight
`k` and of weight `k'` at once.

The three statements below differ only in how the congruence is phrased: through explicit
`p`-integral lifts, or through the valuation `PowerSeries.Padic.v` of the base change to `ℚ_[p]`,
either under Serre's normalization `v(f) = 0` or in the scale-invariant form
`v(f - f') ≥ v(f) + 1`.

## Main results

* `ModularForm.natCast_eq_of_map_toZMod_eq`: two `p`-integral rational modular forms with the same
  nonzero reduction modulo `p` have weights congruent modulo `p - 1`.
* `ModularForm.natCast_eq_of_v_eq_zero`: the same statement with the congruence expressed by the
  valuation, under the normalization `v(f) = 0`.
* `ModularForm.natCast_eq_of_v_sub_le`: Serre's statement, `v(f - f') ≥ v(f) + 1`, with no
  normalization.
-/

@[expose] public noncomputable section

open PowerSeries PowerSeries.Padic

namespace ModularForm

variable {p : ℕ} [Fact p.Prime] {k k' : ℤ} {f : rationalModularForms k}
  {f' : rationalModularForms k'} {g g' : (pLocalInt p)⟦X⟧}

/-- **The case `m = 1` of Serre's theorem on congruences, for rational modular forms.** Two
rational modular forms of weights `k` and `k'` admitting `p`-integral lifts with the same nonzero
reduction modulo `p` satisfy `k ≡ k' mod (p - 1)`. -/
theorem natCast_eq_of_map_toZMod_eq (hp : 5 ≤ p)
    (hg : g.map (algebraMap _ ℚ) = rationalQExpansion f)
    (hg' : g'.map (algebraMap _ ℚ) = rationalQExpansion f')
    (h0 : g.map pLocalInt.toZMod ≠ 0) (h : g.map pLocalInt.toZMod = g'.map pLocalInt.toZMod) :
    (k : ZMod (p - 1)) = (k' : ZMod (p - 1)) := by
  have key {l : ℤ} {F : rationalModularForms l} {G : (pLocalInt p)⟦X⟧}
      (hG : G.map (algebraMap _ ℚ) = rationalQExpansion F) (hG0 : G.map pLocalInt.toZMod ≠ 0) :
      ∃ n : ℕ, l = n := by
    refine ⟨l.toNat, ?_⟩
    have hGne : G ≠ 0 := fun hzero ↦ hG0 (by rw [hzero, _root_.map_zero])
    have : (F : ℚ⟦X⟧) ≠ 0 := fun hzero ↦ hGne <| map_injective _ pLocalInt.algebraMap_injective <|
      by rw [hG, _root_.map_zero]; simpa using hzero
    grind [nonneg_of_mem_rationalModularForms F.2 this]
  obtain ⟨n, rfl⟩ := key hg h0
  obtain ⟨n', rfl⟩ := key hg' (h ▸ h0)
  push_cast
  exact natCast_eq_of_mem_modPModularForms hp h0 ⟨g, f, hg, rfl⟩ ⟨g', f', hg', h.symm⟩

variable (f f')

/-- **The case `m = 1` of Serre's theorem on congruences, in Serre's normalized form.** If `f` has
valuation `0` and `f - f'` has valuation at least `1`, then the weights of `f` and `f'` are
congruent modulo `p - 1`. -/
theorem natCast_eq_of_v_eq_zero (hp : 5 ≤ p) (hv : v ((f : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])) = 0)
    (h : 1 ≤ v ((f : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p]) - (f' : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p]))) :
    (k : ZMod (p - 1)) = (k' : ZMod (p - 1)) := by
  rw [← map_sub] at h
  obtain ⟨g, hg⟩ := v_nonneg_iff_rat.1 hv.ge
  obtain ⟨d, hd⟩ := v_nonneg_iff_rat.1 (le_trans zero_le_one h)
  refine natCast_eq_of_map_toZMod_eq hp (f' := f') (g' := g - d) (by simpa using hg)
    (by simp [map_sub, hg, hd]) (fun hzero ↦ ?_) (by grind [(map_toZMod_eq_zero_iff hd).2 h])
  exact absurd ((map_toZMod_eq_zero_iff hg).1 hzero) (by simp [hv])

/-- **The case `m = 1` of Serre's theorem on congruences, in Serre's form.** If `f` is a nonzero
rational modular form of weight `k`, `f'` one of weight `k'`, and `f` and `f'` are congruent
modulo `p` relative to the valuation of `f`, that is `v (f - f') ≥ v f + 1`, then the weights of
`f` and `f'` are congruent modulo `p - 1`. -/
theorem natCast_eq_of_v_sub_le (hp : 5 ≤ p) (hf : (f : ℚ⟦X⟧) ≠ 0)
    (h : v ((f : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p])) + 1 ≤
      v ((f : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p]) - (f' : ℚ⟦X⟧).map (algebraMap ℚ ℚ_[p]))) :
    (k : ZMod (p - 1)) = (k' : ZMod (p - 1)) := by
  obtain ⟨m, hm⟩ := rationalQExpansion_exists_zpow_smul_v_eq_zero (p := p) f hf
  have hc : ((p : ℚ_[p]) ^ m) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 (by lia))
  have hmap (g : ℚ⟦X⟧) : ((p : ℚ) ^ m • g).map (algebraMap ℚ ℚ_[p]) =
      C ((p : ℚ_[p]) ^ m) * g.map (algebraMap ℚ ℚ_[p]) := by
    rw [smul_eq_C_mul, map_mul, map_C, map_zpow₀, map_natCast]
  rw [hmap, v_C_mul hc] at hm
  have key := add_le_add (le_refl (Padic.addValuation ((p : ℚ_[p]) ^ m) : EInt)) h
  rw [← add_assoc, hm, zero_add] at key
  refine natCast_eq_of_v_eq_zero  ⟨_, (rationalModularForms k).smul_mem ((p : ℚ) ^ m) f.2⟩
    ⟨_, (rationalModularForms k').smul_mem ((p : ℚ) ^ m) f'.2⟩ hp ?_ ?_
  · simpa only [hmap, v_C_mul hc] using hm
  · simp_all [← mul_sub, v_C_mul hc]

end ModularForm
