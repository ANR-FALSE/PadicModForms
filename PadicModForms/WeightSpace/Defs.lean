module

public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

variable {p : ℕ} [Fact p.Prime]

notation "X_[" p "]" => ContinuousMonoidHom ℤ_[p]ˣ ℤ_[p]ˣ

def ι : ℤ → X_[p] := fun n ↦ ⟨zpowGroupHom n, by fun_prop⟩
