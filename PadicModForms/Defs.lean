import Mathlib

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

notation "X_[" p "]" => ContinuousMonoidHom ℤ_[p]ˣ ℤ_[p]ˣ

def ι : ℤ → X_[p] := fun n ↦ ⟨zpowGroupHom n, by fun_prop⟩

theorem w_tendsto {f : ℚ_[p]⟦X⟧} (hf : f ≠ 0) (S : pAdicModularFormStruct n f) :
  ∃ (x : X_[p]), Tendsto (fun i ↦ ι (S.w i)) atTop (𝓝 x) := sorry

theorem limit_unique {f : ℚ_[p]⟦X⟧} (S S' : pAdicModularFormStruct n f) {x x' : X_[p]}
  (hx : Tendsto (fun i ↦ ι (S.w i)) atTop (𝓝 x))
  (hx' : Tendsto (fun i ↦ ι (S'.w i)) atTop (𝓝 x')) : x = x' := sorry

open Classical in
noncomputable def w {f : ℚ_[p]⟦X⟧} (hf : f.isPAdicModularForm n) : X_[p] :=
  if hf0 : f = 0 then (ι 0) else (w_tendsto n hf0 (choice hf)).choose
