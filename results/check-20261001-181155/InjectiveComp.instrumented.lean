import Mathlib

namespace LeanProofs

open Function

/-- A composition of injective functions is injective. -/
theorem injective_comp {α β γ : Type*} {f : α → β} {g : β → γ}
    (hf : Injective f) (hg : Injective g) :
    Injective (g ∘ f) := by
  trace_state
  intro x y h
  trace_state
  apply hf
  trace_state
  apply hg
  trace_state
  exact h
  trace_state

end LeanProofs
#print axioms LeanProofs.injective_comp
#print LeanProofs.injective_comp
