import OEISOpen.A089073.Product

/-!
# Uniqueness of the normalized A089073 coefficient sequence

The two initial values and the step-two recurrence determine the rational
sequence uniquely. This permits any independently derived coefficient sequence
with these properties to be identified with the proved binomial formula.
-/

namespace OEISOpen.A089073

/-- The two initial values and the short recurrence characterize `b` uniquely. -/
theorem sequence_eq_b_of_step (c : ℕ → ℚ)
    (hc0 : c 0 = 1) (hc1 : c 1 = 2)
    (hstep : ∀ k : ℕ,
      ((k : ℚ) + 2) * ((k : ℚ) + 3) * c (k + 2) =
        12 * (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 5) * c k) :
    ∀ k : ℕ, c k = b k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => simpa using hc0
  | one => simpa using hc1
  | more k ih _ =>
    have hlead : ((k : ℚ) + 2) * ((k : ℚ) + 3) ≠ 0 := by positivity
    apply mul_left_cancel₀ hlead
    calc
      ((k : ℚ) + 2) * ((k : ℚ) + 3) * c (k + 2) =
          12 * (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 5) * c k := hstep k
      _ = 12 * (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 5) * b k := by rw [ih]
      _ = ((k : ℚ) + 2) * ((k : ℚ) + 3) * b (k + 2) := (b_step_two k).symm

#print axioms sequence_eq_b_of_step

end OEISOpen.A089073
