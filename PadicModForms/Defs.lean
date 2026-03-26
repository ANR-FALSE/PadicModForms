module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Topology.Algebra.Group.CompactOpen

public import PadicModForms.WeightSpace.Defs

@[expose] public section

open PowerSeries ModularFormClass Filter

open scoped Topology

variable {p : ℕ} [Fact p.Prime] (n : ℕ)

structure pAdicModularFormStruct (f : ℚ_[p]⟦X⟧) where
  F : ℕ → ℚ⟦X⟧
  w : ℕ → ℤ
  modF : ∀ i, ∃ (g : ModularForm (CongruenceSubgroup.Gamma n) (w i)),
    qExpansion n g = (F i).map (algebraMap ℚ ℂ)
  tendsTo : TendstoUniformly (fun i n ↦ (↑(coeff n (F i)) : ℚ_[p])) (coeff · f) atTop

def PowerSeries.isPAdicModularForm (f : ℚ_[p]⟦X⟧) := Nonempty (pAdicModularFormStruct n f)

def ModularFormClass.isPAdicModularForm {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma 1) k) :=
    ∃ g : ℚ⟦X⟧, PowerSeries.isPAdicModularForm n (g.map (algebraMap ℚ ℚ_[p])) ∧
    qExpansion 1 f = g.map (algebraMap ℚ ℂ)
