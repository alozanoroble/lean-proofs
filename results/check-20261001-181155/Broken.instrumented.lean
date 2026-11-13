import Mathlib

namespace LeanProofs

/-- A false statement. The proof attempt is rejected. -/
theorem false_claim (n : ℕ) : n + 1 = n := by
  trace_state
  omega
  trace_state

/-- A true statement with a gap: `sorry` tells Lean "trust me". Lean
accepts the file with a warning, and `#print axioms` exposes the gap. -/
theorem with_a_gap (n : ℕ) : n * 0 = 0 := by
  trace_state
  sorry
  trace_state

end LeanProofs
#print axioms LeanProofs.false_claim
#print LeanProofs.false_claim
#print axioms LeanProofs.with_a_gap
#print LeanProofs.with_a_gap
