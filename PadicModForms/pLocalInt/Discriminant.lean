/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.RingTheory.PowerSeries.Inverse
public import PadicModForms.ForMathlib.PowerSeries
public import PadicModForms.pLocalInt.Graded

/-!
# The modular discriminant over `pLocalInt`

For a prime `p ≥ 5` this file constructs the modular discriminant as a power series over
`pLocalInt p`, and shows that dividing a `p`-integral modular form with vanishing constant
coefficient by it gives again a `p`-integral modular form, of weight lowered by `12`. This is
the inductive step needed to prove that `E₄_int` and `E₆_int` generate the graded ring of
`p`-integral modular forms.

## Main results

* `discriminant_int`: the modular discriminant as a power series over `pLocalInt p`.
* `discriminant_int_map_complex`: its image in `ℂ⟦X⟧` is the `q`-expansion of `Δ`.
* `divDiscriminant_int_isPLocalIntModularForm`: division by the discriminant preserves
  `p`-integrality and lowers the weight by `12`.
* `pLocalIntModularFormsEquivMvPolynomial`: for `p ≥ 5` evaluation at `E₄_int` and `E₆_int`
  identifies the polynomial ring in two variables over `pLocalInt p` with the graded ring of
  `p`-integral modular forms.
-/

@[expose] public noncomputable section

open UpperHalfPlane MatrixGroups DirectSum EisensteinSeries PowerSeries GradedMonoid

variable {p : ℕ} [Fact p.Prime]

namespace ModularForm

/-! ### Inverting `1728` -/

theorem not_dvd_1728 (hp : 5 ≤ p) : ¬ p ∣ 1728 := by
  intro h
  have Hfact : Nat.primeFactors 1728 = {2, 3} := by decide +kernel
  grind [(Nat.mem_primeFactors (n := 1728)).2 ⟨Fact.out, h, by decide⟩]

theorem inv_1728_mem_pLocalInt (hp : 5 ≤ p) : (1728 : ℚ)⁻¹ ∈ pLocalInt p := by
  simp [mem_pLocalInt_iff, not_dvd_1728 hp]

/-- For `p ≥ 5` the element `1728` is a unit of `pLocalInt p`. This is the whole reason the
modular discriminant is `p`-integral. -/
theorem isUnit_1728 (hp : 5 ≤ p) : IsUnit (1728 : pLocalInt p) :=
  .of_mul_eq_one ⟨_, inv_1728_mem_pLocalInt hp⟩ <| Subtype.ext <| by norm_num

/-- The inverse of `1728`, as an element of `ℚ`. -/
@[simp]
theorem coe_isUnit_1728_unit_inv (hp : 5 ≤ p) : (isUnit_1728 hp).unit⁻¹ = (1728 : ℚ)⁻¹ :=
  (inv_eq_of_mul_eq_one_right (congrArg (pLocalInt p).subtype (isUnit_1728 hp).mul_val_inv)).symm

/-! ### The discriminant as an integral power series -/

/-- The modular discriminant over `pLocalInt p`, defined by `(E₄_int³ - E₆_int²) / 1728`. -/
def discriminant_int (hp : 5 ≤ p) : (pLocalInt p)⟦X⟧ :=
  (↑(isUnit_1728 hp).unit⁻¹ : pLocalInt p) • (E₄_int ^ 3 - E₆_int ^ 2)

theorem smul_discriminant_int (hp : 5 ≤ p) :
    (1728 : pLocalInt p) • discriminant_int hp = E₄_int ^ 3 - E₆_int ^ 2 := by
  simp [discriminant_int, smul_smul, (isUnit_1728 hp).mul_val_inv]

@[simp]
theorem constantCoeff_discriminant_int (hp : 5 ≤ p) : constantCoeff (discriminant_int hp) = 0 := by
  simp [discriminant_int]

@[simp]
theorem coeff_discriminant_int_zero (hp : 5 ≤ p) : coeff 0 (discriminant_int hp) = 0 :=
  (coeff_zero_eq_constantCoeff_apply _).trans (constantCoeff_discriminant_int hp)

@[simp]
theorem coeff_discriminant_int_one (hp : 5 ≤ p) : coeff 1 (discriminant_int hp) = 1 :=
  Subtype.ext <| by
    simp [discriminant_int, coeff_one_pow, smul_eq_mul, coe_isUnit_1728_unit_inv hp]; norm_num

/-! ### `Δ` is `X` times a unit -/

/-- The unit factor in the decomposition `discriminant_int hp = discriminantUnitSeries hp * X`. -/
def discriminantUnitSeries (hp : 5 ≤ p) : (pLocalInt p)⟦X⟧ :=
  .mk fun n ↦ coeff (n + 1) (discriminant_int hp)

@[simp]
theorem constantCoeff_discriminantUnitSeries (hp : 5 ≤ p) :
    constantCoeff (discriminantUnitSeries hp) = 1 := by
  simp [discriminantUnitSeries]

theorem isUnit_discriminantUnitSeries (hp : 5 ≤ p) : IsUnit (discriminantUnitSeries hp) :=
  isUnit_iff_constantCoeff.mpr (by simp)

/-- The unit associated to `discriminantUnitSeries hp`. -/
def discriminantUnit (hp : 5 ≤ p) : ((pLocalInt p)⟦X⟧)ˣ :=
  (isUnit_discriminantUnitSeries hp).unit

@[simp]
theorem coe_discriminantUnit (hp : 5 ≤ p) :
    (discriminantUnit hp : (pLocalInt p)⟦X⟧) = discriminantUnitSeries hp :=
  IsUnit.unit_spec _

/-- The discriminant has order one, with unit leading factor. -/
theorem discriminant_int_eq_unit_mul_X (hp : 5 ≤ p) :
    discriminant_int hp = (discriminantUnit hp : (pLocalInt p)⟦X⟧) * X := by
  simpa [discriminantUnitSeries] using eq_shift_mul_X (constantCoeff_discriminant_int hp)

/-! ### Comparison with the classical discriminant -/

/-- Extending the coefficients of `discriminant_int` to `ℚ` gives the usual rational formula. -/
theorem discriminant_int_map_rat (hp : 5 ≤ p) :
    (discriminant_int hp).map (algebraMap _ ℚ) = (1 / 1728 : ℚ) • (E₄Rat ^ 3 - E₆Rat ^ 2) := by
  simp [discriminant_int, smul_eq_C_mul, E₄_int_map, E₆_int_map]

/-- The `q`-expansion of `Δ` is `(E₄³ - E₆²) / 1728`. -/
theorem qExpansion_discriminant : qExpansion 1 discriminant =
      (1 / 1728 : ℂ) • (qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2) := by
  simpa using congrArg (qExpansionAlgHom 1 one_pos one_mem_strictPeriods_SL)
    discriminant_eq_E₄_cube_sub_E₆_sq_graded

/-- Extending `discriminant_int` to `ℂ` gives the `q`-expansion of the modular discriminant. -/
theorem discriminant_int_map_complex (hp : 5 ≤ p) :
    ((discriminant_int hp).map (algebraMap _ ℚ)).map (algebraMap ℚ ℂ) =
      qExpansion 1 discriminant := by
  simp [discriminant_int_map_rat, qExpansion_discriminant,smul_eq_C_mul, ERat_map_complex
    (by norm_num) ⟨2, rfl⟩, ERat_map_complex (by norm_num) ⟨3, rfl⟩]

theorem qExpansion_discriminant_ne_zero : qExpansion 1 discriminant ≠ 0 := fun h ↦ by
  simpa [discriminant_qExpansion_coeff_one] using congrArg (fun f ↦ coeff 1 f) h

/-- The rational modular form underlying `discriminant_int`. -/
def discriminantRat (hp : 5 ≤ p) : rationalModularForms 12 :=
  ⟨(discriminant_int hp).map (algebraMap (pLocalInt p) ℚ),
    CuspForm.discriminant, CuspForm.coe_discriminant ▸ (discriminant_int_map_complex hp).symm⟩

/-- The modular discriminant as a `p`-integral modular form of weight `12`. -/
def discriminantIntModularForm (hp : 5 ≤ p) : pLocalIntModularForms p 12 :=
  ⟨discriminant_int hp, discriminantRat hp, by simp [discriminantRat]⟩

/-- The polynomial `(X₀³ - X₁²) / 1728` over `pLocalInt p`. -/
def discriminantPoly_int (hp : 5 ≤ p) : MvPolynomial (Fin 2) (pLocalInt p) :=
  MvPolynomial.C (↑(isUnit_1728 hp).unit⁻¹ : pLocalInt p) *
    (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2)

theorem evalE₄E₆Int_discriminantPoly_int (hp : 5 ≤ p) : evalE₄E₆Int (discriminantPoly_int hp) =
      of (fun i ↦ pLocalIntModularForms p i) 12 (discriminantIntModularForm hp) := by
  rw [discriminantPoly_int, map_mul, map_sub, map_pow, map_pow, MvPolynomial.algHom_C]
  simp only [evalE₄E₆Int, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    pLocalIntModularForms.of_pow_eq_of _ ⟨_, E₄_int_pow_three_mem⟩ (by norm_num) rfl,
    pLocalIntModularForms.of_pow_eq_of _ ⟨_, E₆_int_pow_two_mem⟩ (by norm_num) rfl,
    ← map_sub, ← of_smul]
  exact congrArg _ (Subtype.ext (by simp [discriminantIntModularForm, discriminant_int]))

/-! ### Division by the discriminant -/

/-- Divide a power series with vanishing constant coefficient by `discriminant_int`. -/
def divDiscriminant_int (hp : 5 ≤ p) (f : (pLocalInt p)⟦X⟧) : (pLocalInt p)⟦X⟧ :=
  (.mk fun n ↦ coeff (n + 1) f) * (discriminantUnit hp)⁻¹

theorem discriminant_int_mul_divDiscriminant_int (hp : 5 ≤ p) {f : (pLocalInt p)⟦X⟧}
    (hf₀ : coeff 0 f = 0) : discriminant_int hp * divDiscriminant_int hp f = f := by
  grind [discriminant_int_eq_unit_mul_X, divDiscriminant_int, Units.mul_inv,
    eq_shift_mul_X ((coeff_zero_eq_constantCoeff_apply f).symm.trans hf₀)]

/-- Division by the discriminant preserves `p`-integrality and lowers the weight by `12`. -/
theorem divDiscriminant_int_isPLocalIntModularForm (hp : 5 ≤ p) {k : ℤ}
    {f : (pLocalInt p)⟦X⟧} (hf : f.isPLocalIntModularForm k) (hf₀ : coeff 0 f = 0) :
    (divDiscriminant_int hp f).isPLocalIntModularForm (k - 12) := by
  obtain ⟨F, hF⟩ := hf
  set Fℂ := rationalModularFormToComplex F with hFℂdef
  have hfℂ : (f.map (algebraMap (pLocalInt p) ℚ)).map (algebraMap ℚ ℂ) = qExpansion 1 Fℂ := by
    simpa [hFℂdef] using congrArg (map (algebraMap ℚ ℂ)) hF
  have hFℂ₀ : coeff 0 (qExpansion 1 Fℂ) = 0 := by simp [← hfℂ, hf₀]
  refine ⟨⟨(divDiscriminant_int hp f).map (algebraMap _ ℚ),
    CuspForm.discriminantEquiv (toCuspForm Fℂ hFℂ₀), ?_⟩, by simp⟩
  refine mul_left_cancel₀ qExpansion_discriminant_ne_zero ?_
  rw [← qExpansion_eq_qExpansion_discriminant_mul Fℂ hFℂ₀, ← discriminant_int_map_complex hp,
    ← map_mul, ← map_mul, discriminant_int_mul_divDiscriminant_int hp hf₀, hfℂ]

/-! ### `E₄_int` and `E₆_int` generate -/

private theorem eq_zero_of_rationalModularForms_eq_bot {k : ℤ} (f : pLocalIntModularForms p k)
    (h : rationalModularForms k = ⊥) : f = 0 :=
  Subtype.ext <| (Submodule.eq_bot_iff _).1 (pLocalIntModularForms_eq_bot h) _ f.2

/-- Every even natural number other than `2` is of the form `4a + 6b`. -/
private theorem exists_E₄E₆_monomial_weight {n : ℕ} (hnEven : Even n) (hnTwo : n ≠ 2) :
    ∃ a b : ℕ, 4 * a + 6 * b = n := by
  obtain ⟨m, rfl⟩ := hnEven
  rcases Nat.even_or_odd m with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact ⟨a, 0, by lia⟩
  · exact ⟨b - 1, 1, by lia⟩

private theorem evalE₄E₆Int_surjective_of_weight (hp : 5 ≤ p) :
    ∀ k (f : pLocalIntModularForms p k), ∃ P : MvPolynomial (Fin 2) (pLocalInt p),
      evalE₄E₆Int P = DirectSum.of (fun i ↦ pLocalIntModularForms p i) k f := by
  intro k f
  by_cases hkNeg : k < 0
  · have hf : f = 0 :=
      eq_zero_of_rationalModularForms_eq_bot f (rationalModularForms_eq_bot_of_neg hkNeg)
    exact ⟨0, by simp [hf]⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n := ⟨k.toNat, by lia⟩
  clear hkNeg
  induction n using Nat.strong_induction_on with | h n ih => ?_
  by_cases hnOdd : Odd (n : ℤ)
  · have hf : f = 0 :=
      eq_zero_of_rationalModularForms_eq_bot f (rationalModularForms_eq_bot_of_odd hnOdd)
    exact ⟨0, by simp [hf]⟩
  rw [Int.not_odd_iff_even] at hnOdd
  have hnEven : Even n := by exact_mod_cast hnOdd
  by_cases hnTwo : n = 2
  · subst n
    have hf : f = 0 :=
      eq_zero_of_rationalModularForms_eq_bot f (by simpa using rationalModularForms_two_eq_bot)
    exact ⟨0, by simp [hf]⟩
  obtain ⟨a, b, hab⟩ := exists_E₄E₆_monomial_weight hnEven hnTwo
  let mn : pLocalIntModularForms p n := ⟨_, E₄_int_pow_mul_E₆_int_pow_mem hab⟩
  let c := coeff 0 (f : (pLocalInt p)⟦X⟧); let f₀ := f - c • mn
  have hmn₀ : coeff 0 (mn : (pLocalInt p)⟦X⟧) = 1 := by simp [mn]
  have hf₀ : coeff 0 (f₀ : (pLocalInt p)⟦X⟧) = 0 := by
    simp [f₀, c, hmn₀, -coeff_zero_eq_constantCoeff]
  have hfDecomp : f = f₀ + c • mn := by simp [f₀]
  have hmonomial : evalE₄E₆Int (MvPolynomial.C c * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)) =
      of (fun i ↦ pLocalIntModularForms p i) n (c • mn) := by
    rw [map_mul, MvPolynomial.algHom_C, evalE₄E₆Int_X_pow_mul, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul,
      pLocalIntModularForms.of_pow_eq_of _ ⟨_, SetLike.pow_mem_graded a
        E₄_int_mem_pLocalIntModularForms⟩ rfl rfl,
      pLocalIntModularForms.of_pow_eq_of _ ⟨_, SetLike.pow_mem_graded b
        E₆_int_mem_pLocalIntModularForms⟩ rfl rfl,
      pLocalIntModularForms.of_mul_of_eq_of _ _ mn (by push_cast [← hab]; ring) rfl, ← of_smul]
  by_cases hnTwelve : 12 ≤ n
  · let g : pLocalIntModularForms p ((n - 12 : ℕ)) := ⟨divDiscriminant_int hp f₀, by
      simpa [show ((n : ℤ) - 12) = ((n - 12 : ℕ)) by lia] using
      divDiscriminant_int_isPLocalIntModularForm hp f₀.property hf₀⟩
    obtain ⟨Q, hQ⟩ := ih (n - 12) (by lia) g
    have hprod : evalE₄E₆Int (discriminantPoly_int hp) * evalE₄E₆Int Q =
        of (fun i ↦ pLocalIntModularForms p i) n f₀ := by
      simpa [evalE₄E₆Int_discriminantPoly_int, hQ] using pLocalIntModularForms.of_mul_of_eq_of
        _ _ _ (by lia) (discriminant_int_mul_divDiscriminant_int hp hf₀)
    refine ⟨discriminantPoly_int hp * Q +
      MvPolynomial.C c * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b), ?_⟩
    rw [map_add, map_mul, hprod, hmonomial, ← map_add, ← hfDecomp]
  · let g : pLocalIntModularForms p (n - 12) :=
      ⟨_, divDiscriminant_int_isPLocalIntModularForm hp f₀.property hf₀⟩
    have hg : g = 0 :=
      eq_zero_of_rationalModularForms_eq_bot g (rationalModularForms_eq_bot_of_neg (by lia))
    have hgVal : divDiscriminant_int hp f₀ = 0 := by simpa [g] using congrArg Subtype.val hg
    have hf₀Zero : f₀ = 0 := Subtype.ext <| by
      simpa [hgVal] using (discriminant_int_mul_divDiscriminant_int hp hf₀).symm
    have hfScalar : f = c • mn := by simpa [hf₀Zero] using hfDecomp
    exact ⟨MvPolynomial.C c * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b),
      hmonomial.trans <| congrArg (of (fun i ↦ pLocalIntModularForms p i) (n : ℤ)) hfScalar.symm⟩

theorem evalE₄E₆Int_surjective (hp : 5 ≤ p) : Function.Surjective (evalE₄E₆Int (p := p)) := by
  intro F
  induction F using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of k f => exact evalE₄E₆Int_surjective_of_weight hp k f
  | add F G hF hG =>
      obtain ⟨P, hP⟩ := hF
      obtain ⟨Q, hQ⟩ := hG
      exact ⟨P + Q, by rw [map_add, hP, hQ]⟩

theorem evalE₄E₆Int_bijective (hp : 5 ≤ p) : Function.Bijective (evalE₄E₆Int (p := p)) :=
  ⟨evalE₄E₆Int_injective, evalE₄E₆Int_surjective hp⟩

/-- For `p ≥ 5` evaluation at `E₄_int` and `E₆_int` identifies the polynomial ring in two
variables over `pLocalInt p` with the graded ring of `p`-integral modular forms. -/
def pLocalIntModularFormsEquivMvPolynomial (hp : 5 ≤ p) :
    MvPolynomial (Fin 2) (pLocalInt p) ≃ₐ[pLocalInt p] ⨁ i, pLocalIntModularForms p i :=
  .ofBijective evalE₄E₆Int (evalE₄E₆Int_bijective hp)

/-! ### The structure theorem weight by weight -/

/-- For `p ≥ 5`, every `p`-integral modular form of weight `k` is the evaluation of a polynomial
that is weighted homogeneous of weight `k`. -/
theorem evalE₄E₆IntAtWeight_surjective (hp : 5 ≤ p) {k : ℕ} :
    Function.Surjective (evalE₄E₆IntAtWeight (p := p) k) := fun f ↦ by
  obtain ⟨P, hP⟩ := evalE₄E₆Int_surjective hp (of _ (k : ℤ) f)
  exact ⟨⟨_, MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous k P⟩, by
    simpa [evalE₄E₆Int_component_eq] using congrArg (fun F ↦ F k) hP⟩

theorem evalE₄E₆IntAtWeight_bijective (hp : 5 ≤ p) {k : ℕ} :
    Function.Bijective (evalE₄E₆IntAtWeight (p := p) k) :=
  ⟨evalE₄E₆IntAtWeight_injective, evalE₄E₆IntAtWeight_surjective hp⟩

/-- For `p ≥ 5` the `p`-integral modular forms of weight `k` are exactly the weighted homogeneous
polynomials of weight `k` in `E₄_int` and `E₆_int`. -/
def evalE₄E₆IntAtWeightEquiv (hp : 5 ≤ p) (k : ℕ) :
    E₄E₆WeightedHomogeneous k (pLocalInt p) ≃ₗ[pLocalInt p] pLocalIntModularForms p k :=
  .ofBijective _ (evalE₄E₆IntAtWeight_bijective (k := k) hp)

@[simp]
theorem evalE₄E₆IntAtWeightEquiv_apply (hp : 5 ≤ p) (k : ℕ)
    (P : E₄E₆WeightedHomogeneous k (pLocalInt p)) :
    evalE₄E₆IntAtWeightEquiv hp k P = evalE₄E₆IntAtWeight k P := rfl

/-- The weighted homogeneous polynomial of weight `k` attached to a `p`-integral modular form of
weight `k` evaluates back to the form. -/
theorem evalE₄E₆Int_symm_apply (hp : 5 ≤ p) {k : ℕ} (f : pLocalIntModularForms p k) :
    evalE₄E₆Int ((evalE₄E₆IntAtWeightEquiv hp k).symm f :
        MvPolynomial _ (pLocalInt p)) = of _ (k : ℤ) f := by
  rw [evalE₄E₆Int_eq_of_apply]
  congr 1
  exact (evalE₄E₆IntAtWeightEquiv hp k).apply_symm_apply f

end ModularForm

end
