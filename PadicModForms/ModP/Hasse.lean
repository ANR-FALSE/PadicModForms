/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import PadicModForms.ModP.Congruences
public import PadicModForms.ModP.Graded

/-!
# The Hasse invariant as a polynomial in `E₄` and `E₆`

For a prime `p ≥ 5` this file defines `hasseInvPoly`, the isobaric polynomial of weight `p - 1`
in `E₄` and `E₆` representing the Hasse invariant `Ẽ_{p-1}`, and proves that it evaluates to `1`.

Over `pLocalInt p` the map `evalE₄E₆Int` is injective, so `E₄` and `E₆` satisfy no relation.
Modulo `p` the congruence `E_{p-1} ≡ 1` becomes the relation `hasseInvPoly hp = 1`, and
Swinnerton-Dyer's theorem states that `hasseInvPoly hp - 1` generates the whole kernel of
`evalE₄E₆ModP`. Serre calls this polynomial `A`.
-/

@[expose] public noncomputable section

open DirectSum EisensteinSeries MvPolynomial PowerSeries

namespace ModularForm

variable {p : ℕ} [Fact p.Prime]

/-! ### The Hasse invariant -/

/-- The Hasse invariant `Ẽ_{p-1}`, written as an isobaric polynomial of weight `p - 1` in `E₄`
and `E₆` with coefficients in `ZMod p`. This is the polynomial Serre calls `A`. -/
def hasseInvPoly (hp : 5 ≤ p) : MvPolynomial (Fin 2) (ZMod p) :=
  (((evalE₄E₆IntAtWeightEquiv hp (p - 1)).symm
      ⟨ModP.E hp, E_int_mem_pLocalIntModularForms _ _ dvd_rfl⟩ : MvPolynomial _ _)).map
        pLocalInt.toZMod

/-- The Hasse invariant is isobaric of weight `p - 1`. -/
theorem hasseInvPoly_isWeightedHomogeneous (hp : 5 ≤ p) :
    IsWeightedHomogeneous E₄E₆Weights (hasseInvPoly hp) (p - 1) := fun d hd ↦
  ((evalE₄E₆IntAtWeightEquiv hp (p - 1)).symm
    ⟨ModP.E hp, E_int_mem_pLocalIntModularForms _ _ dvd_rfl⟩).property
      fun hzero ↦ hd <| by simp [hasseInvPoly, MvPolynomial.coeff_map, hzero]

/-- Evaluating the Hasse invariant at `E₄` and `E₆` gives `1`: this is the congruence
`E_{p-1} ≡ 1 mod p`, and it is the defining relation of the algebra of mod-`p` modular forms. -/
theorem evalE₄E₆ModP_hasseInvPoly (hp : 5 ≤ p) : evalE₄E₆ModP (hasseInvPoly hp) = 1 := by
  rw [hasseInvPoly, evalE₄E₆ModP_map, ← pLocalIntQExpansionAlgHom_evalE₄E₆Int,
    evalE₄E₆Int_symm_apply, pLocalIntQExpansionAlgHom_of, E_p_sub_one_mod_p hp]

/-- The Hasse invariant minus one lies in the kernel of `evalE₄E₆ModP`. Swinnerton-Dyer's theorem
states that it generates that kernel. -/
theorem hasseInvPoly_sub_one_mem_ker (hp : 5 ≤ p) :
    hasseInvPoly hp - 1 ∈ RingHom.ker evalE₄E₆ModP := by
  simp [RingHom.mem_ker, evalE₄E₆ModP_hasseInvPoly hp]

end ModularForm
