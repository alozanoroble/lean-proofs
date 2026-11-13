import Mathlib

namespace LeanProofs

variable {G : Type*} [Group G]

/-- Inverses in a group are unique: if `a * b = 1` then `b = a⁻¹`.
Written as a `calc` chain, the way it is written on paper. -/
theorem inv_unique_calc (a b : G) (h : a * b = 1) : b = a⁻¹ := by
  trace_state
  calc b = 1 * b := by rw [one_mul]
    _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * b) := by rw [mul_assoc]
    _ = a⁻¹ * 1 := by rw [h]
    _ = a⁻¹ := by rw [mul_one]
  trace_state

/-- The same theorem, proved by rewriting the hypothesis step by step. -/
theorem inv_unique (a b : G) (h : a * b = 1) : b = a⁻¹ := by
  trace_state
  have h2 : a⁻¹ * (a * b) = a⁻¹ * 1 := by rw [h]
  trace_state
  rw [← mul_assoc] at h2
  trace_state
  rw [inv_mul_cancel] at h2
  trace_state
  rw [one_mul] at h2
  trace_state
  rw [mul_one] at h2
  trace_state
  exact h2
  trace_state

end LeanProofs
#print axioms LeanProofs.inv_unique_calc
#print LeanProofs.inv_unique_calc
#print axioms LeanProofs.inv_unique
#print LeanProofs.inv_unique
