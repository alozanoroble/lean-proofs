import Mathlib

namespace LeanProofs

open Function

/-- A composition of injective functions is injective. -/
theorem injective_comp {α β γ : Type*} {f : α → β} {g : β → γ}
    (hf : Injective f) (hg : Injective g) :
    Injective (g ∘ f) := by
  intro x y h
  apply hf
  apply hg
  exact h

end LeanProofs
