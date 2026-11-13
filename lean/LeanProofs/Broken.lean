import Mathlib

namespace LeanProofs

/-- A false statement. The proof attempt is rejected. -/
theorem false_claim (n : ℕ) : n + 1 = n := by
  omega

/-- A true statement with a gap: `sorry` tells Lean "trust me". Lean
accepts the file with a warning, and `#print axioms` exposes the gap. -/
theorem with_a_gap (n : ℕ) : n * 0 = 0 := by
  sorry

end LeanProofs
