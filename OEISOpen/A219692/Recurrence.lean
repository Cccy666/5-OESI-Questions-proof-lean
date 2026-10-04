import OEISOpen.A219692.Shifts
import OEISOpen.A219692.Summation

namespace OEISOpen.A219692

/-- The certificate holds for every index, including all support boundaries. -/
theorem local_telescoping (n j : ℕ) (hn : 2 ≤ n) :
    (n : ℚ)^3 * (S n j : ℚ) - (p n : ℚ) * (S (n-1) j : ℚ) +
      (q n : ℚ) * (S (n-2) j : ℚ) = G n (j+1) - G n j := by
  have h := local_certificate_of_crossed_shifts (n : ℚ) (j : ℚ)
    (S n j : ℚ) (S (n-1) j : ℚ) (S (n-2) j : ℚ) (S n (j+1) : ℚ)
    (first_denominator_ne_zero n j) (second_denominator_ne_zero n j)
    (shift1 n j (by omega)) (shift2 n j hn) (shiftJ n j)
  simpa [p, q, G] using h

/-- The explicit positive binomial sum satisfies the target recurrence. -/
theorem positive_recurrence (n : ℕ) (hn : 2 ≤ n) : residual v n = 0 := by
  exact positive_recurrence_of_local_certificate n (fun j => local_telescoping n j hn)

/-- Bridge remains a separate, explicit hypothesis until its Lean proof is supplied. -/
theorem normalized_eq_positive_of_bridge
    (bridge : ∀ n : ℕ, 1 ≤ n → a n = v n) : u = v := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [u_eq_a_of_pos (by omega)]
    exact bridge n (by omega)

/-- T1 reduced to Bridge; this is not an unconditional formal proof of T1. -/
theorem normalized_recurrence_of_bridge
    (bridge : ∀ n : ℕ, 1 ≤ n → a n = v n) (n : ℕ) (hn : 2 ≤ n) :
    residual u n = 0 := by
  rw [normalized_eq_positive_of_bridge bridge]
  exact positive_recurrence n hn

/-- T2 reduced to the same Bridge. -/
theorem original_tail_recurrence_of_bridge
    (bridge : ∀ n : ℕ, 1 ≤ n → a n = v n) (n : ℕ) (hn : 3 ≤ n) :
    residual a n = 0 := by
  exact tail_recurrence_of_normalized (normalized_recurrence_of_bridge bridge) n hn

end OEISOpen.A219692
