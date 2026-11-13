import Mathlib

namespace LeanProofs

/-- Euclid: for every `n` there is a prime `p ≥ n`. So there are
infinitely many primes.

The idea: let `p` be the smallest prime factor of `n! + 1`. If `p < n`,
then `p` divides `n!`, and also `n! + 1`, so it divides `1`.
That is impossible. -/
theorem exists_prime_ge (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime := by
  trace_state
  have hpos : 0 < n.factorial := Nat.factorial_pos n
  trace_state
  have hne : n.factorial + 1 ≠ 1 := by omega
  trace_state
  let p := Nat.minFac (n.factorial + 1)
  trace_state
  have hp : p.Prime := Nat.minFac_prime hne
  trace_state
  refine ⟨p, ?_, hp⟩
  trace_state
  by_contra hlt
  trace_state
  rw [not_le] at hlt
  trace_state
  have h1 : p ∣ n.factorial := Nat.dvd_factorial hp.pos hlt.le
  trace_state
  have h2 : p ∣ n.factorial + 1 := Nat.minFac_dvd (n.factorial + 1)
  trace_state
  have h3 : p ∣ 1 := (Nat.dvd_add_right h1).mp h2
  trace_state
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  trace_state

/-- The same fact, stated as "the set of primes is infinite", and proved by
looking the result up in Mathlib. -/
theorem primes_infinite : {p : ℕ | p.Prime}.Infinite :=
  Nat.infinite_setOfPred_prime

end LeanProofs
#print axioms LeanProofs.exists_prime_ge
#print LeanProofs.exists_prime_ge
#print axioms LeanProofs.primes_infinite
#print LeanProofs.primes_infinite
