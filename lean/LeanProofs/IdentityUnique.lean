import Mathlib

namespace LeanProofs

/-- If `e` and `e'` are both two-sided identities for a multiplication,
then `e = e'`. Only a multiplication `*` is assumed: no associativity,
no inverses. -/
theorem identity_unique {M : Type*} [Mul M] (e e' : M)
    (he : ∀ a : M, e * a = a ∧ a * e = a)
    (he' : ∀ a : M, e' * a = a ∧ a * e' = a) :
    e = e' := by
  have h1 : e * e' = e' := (he e').1
  have h2 : e * e' = e := (he' e).2
  rw [← h2]
  exact h1

/-- In a group, an element that acts as a left identity on even one
element must be the identity `1` of the group. -/
theorem eq_one_of_mul_left {G : Type*} [Group G] (e a : G)
    (h : e * a = a) :
    e = 1 := by
  have h2 : e * a * a⁻¹ = a * a⁻¹ := by rw [h]
  rw [mul_assoc] at h2
  rw [mul_inv_cancel] at h2
  rw [mul_one] at h2
  exact h2

end LeanProofs
