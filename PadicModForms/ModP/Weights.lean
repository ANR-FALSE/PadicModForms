/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ModP.KerEval

/-!
# Weights of mod-`p` modular forms are well defined modulo `p - 1`

Let `p ≥ 5`. Two weighted homogeneous polynomials with the same nonzero `q`-expansion modulo `p`
have weights congruent modulo `p - 1`. This is the case `m = 1` of Serre's first theorem on
congruences between modular forms: if `f ≡ f' mod p` and `f ≢ 0 mod p`, then the weights of `f`
and `f'` are congruent modulo `(p - 1)p⁰`.

The proof is the graded one. For the coarser grading `E₄E₆WeightsModPSubOne`, obtained by reading
the weights of `E₄` and `E₆` in `ZMod (p - 1)`, the polynomial `hasseInvPoly hp - 1` is homogeneous
of degree `0`. Hence the kernel of `evalE₄E₆ModP`, which it generates
(`ModularForm.ker_evalE₄E₆ModP`), is a homogeneous ideal, and two forms whose difference lies in it
and whose degrees differ cannot both be nonzero.

## Main results

* `ModularForm.natCast_eq_of_evalE₄E₆ModP_eq`: weighted homogeneous polynomials of weights `n` and
  `n'` with the same nonzero evaluation satisfy `(n : ZMod (p - 1)) = n'`.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace ModularForm

variable {p n n' : ℕ} [Fact p.Prime] {F G : MvPolynomial (Fin 2) (ZMod p)}

/-- **The case `m = 1` of Serre's theorem on congruences.** Two weighted homogeneous polynomials
with the same nonzero evaluation at `E₄` and `E₆` modulo `p` have weights congruent modulo
`p - 1`. -/
theorem natCast_eq_of_evalE₄E₆ModP_eq (hp : 5 ≤ p) (hF : IsWeightedHomogeneous E₄E₆Weights F n)
    (hG : IsWeightedHomogeneous E₄E₆Weights G n') (h : evalE₄E₆ModP F = evalE₄E₆ModP G)
    (h0 : evalE₄E₆ModP F ≠ 0) : (n : ZMod (p - 1)) = (n' : ZMod (p - 1)) := by
  by_contra hne
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.1 <| (ker_evalE₄E₆ModP hp) ▸
    (RingHom.mem_ker.2 (by rw [map_sub, h, sub_self]) : F - G ∈ RingHom.ker evalE₄E₆ModP)
  -- Comparing the components of degree `n` in the grading modulo `p - 1`.
  have hcomp := congrArg
    (weightedHomogeneousComponent (E₄E₆WeightsModPSubOne p) (n : ZMod (p - 1))) hH
  rw [map_sub, (isWeightedHomogeneous_modPSubOne hF).weightedHomogeneousComponent_same,
    (isWeightedHomogeneous_modPSubOne hG).weightedHomogeneousComponent_ne _ hne, sub_zero,
    ← add_zero (n : ZMod (p - 1)),
    (isWeightedHomogeneous_hasseInvPoly_sub_one_modPSubOne hp).weightedHomogeneousComponent_mul]
    at hcomp
  -- The evaluation of `hasseInvPoly hp - 1` vanishes, hence so does that of `F`.
  refine h0 ?_
  rw [hcomp, map_mul, RingHom.mem_ker.1 (hasseInvPoly_sub_one_mem_ker hp), zero_mul]

/-- **The case `m = 1` of Serre's theorem on congruences, for modular forms.** A nonzero mod-`p`
modular form has a well-defined weight modulo `p - 1`: if the same power series is a mod-`p`
modular form of weight `k` and of weight `k'`, then `k ≡ k' mod (p - 1)`. -/
theorem natCast_eq_of_mem_modPModularForms (hp : 5 ≤ p) {f : PowerSeries (ZMod p)} (hf : f ≠ 0)
    (hk : f ∈ modPModularForms p n) (hk' : f ∈ modPModularForms p n') :
    (n : ZMod (p - 1)) = (n' : ZMod (p - 1)) := by
  obtain ⟨F, hFhom, hF⟩ := exists_isWeightedHomogeneous_of_mem_modPModularForms hp hk
  obtain ⟨G, hGhom, hG⟩ := exists_isWeightedHomogeneous_of_mem_modPModularForms hp hk'
  exact natCast_eq_of_evalE₄E₆ModP_eq hp hFhom hGhom (hF.trans hG.symm) (by rw [hF]; exact hf)

end ModularForm
