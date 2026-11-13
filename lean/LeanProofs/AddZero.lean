namespace LeanProofs

/-- `n + 0 = n` holds *by definition*: Lean defines addition by recursion
on the second argument, with `n + 0 := n`. So `rfl` ("both sides compute
to the same thing") is a complete proof. -/
theorem add_zero (n : Nat) : n + 0 = n := rfl

/-- `0 + n = n` is *not* true by definition, because the recursion runs on
the second argument. It needs induction on `n`. -/
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    rfl
  | succ k ih =>
    rw [Nat.add_succ]
    rw [ih]

end LeanProofs
