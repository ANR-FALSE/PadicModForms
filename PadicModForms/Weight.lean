module

public import PadicModForms.Defs

@[expose] public section

open PowerSeries Filter Topology

variable {p : ℕ} [Fact p.Prime] (n : ℕ)

theorem w_tendsto {f : ℚ_[p]⟦X⟧} (hf : f ≠ 0) (S : pAdicModularFormStruct n f) :
    ∃ (x : X_[p]), Tendsto (fun i ↦ ι (S.w i)) atTop (𝓝 x) := by
  sorry

theorem limit_unique {f : ℚ_[p]⟦X⟧} (S S' : pAdicModularFormStruct n f) {x x' : X_[p]}
    (hx : Tendsto (fun i ↦ ι (S.w i)) atTop (𝓝 x))
    (hx' : Tendsto (fun i ↦ ι (S'.w i)) atTop (𝓝 x')) : x = x' := by
  sorry

open Classical in
noncomputable def w {f : ℚ_[p]⟦X⟧} (hf : f.isPAdicModularForm n) : X_[p] :=
  if hf0 : f = 0 then (ι 0) else (w_tendsto n hf0 (choice hf)).choose
