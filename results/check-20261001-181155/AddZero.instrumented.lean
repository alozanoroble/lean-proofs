namespace LeanProofs

/-- `n + 0 = n` holds *by definition*: Lean defines addition by recursion
on the second argument, with `n + 0 := n`. So `rfl` ("both sides compute
to the same thing") is a complete proof. -/
theorem add_zero (n : Nat) : n + 0 = n := rfl

/-- `0 + n = n` is *not* true by definition, because the recursion runs on
the second argument. It needs induction on `n`. -/
theorem zero_add (n : Nat) : 0 + n = n := by
  trace_state
  induction n with
  | zero =>
    trace_state
    rfl
    trace_state
  | succ k ih =>
    trace_state
    rw [Nat.add_succ]
    trace_state
    rw [ih]
    trace_state
  trace_state

end LeanProofs
#print axioms LeanProofs.add_zero
#print LeanProofs.add_zero
#print axioms LeanProofs.zero_add
#print LeanProofs.zero_add
