import OEISOpen.A089073.Product
import OEISOpen.A089073.Parity

/-!
# A089073: the recurrence for the explicit rational closed formula

This is T-number. The value `a 0 = 1/2` is auxiliary. A theorem identifying
`a n` with the cardinality of the reflection-fixed graph class is NOT assumed
or claimed in this module. No original benchmark declaration was supplied.
-/
namespace OEISOpen.A089073

def a : ℕ → ℚ := parityLift b

theorem a_even (k : ℕ) : a (2 * k) = b k / 2 := parityLift_even b k
theorem a_odd (k : ℕ) : a (2 * k + 1) = b k := parityLift_odd b k

theorem a_even_closed (k : ℕ) :
    a (2 * k) = 4 ^ k / (2 * ((k : ℚ) + 1)) *
      Ring.choose ((3 * (k : ℚ) - 1) / 2) k := by
  rw [a_even, b_eq_choose]
  field_simp

theorem a_odd_closed (k : ℕ) :
    a (2 * k + 1) = 4 ^ k / ((k : ℚ) + 1) *
      Ring.choose ((3 * (k : ℚ) - 1) / 2) k := by
  rw [a_odd, b_eq_choose]

theorem a_initial : a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 2 ∧ a 4 = 5 := by
  norm_num [a, parityLift, b, P, Finset.prod_range_succ]

theorem a_auxiliary_zero : a 0 = 1 / 2 := by
  norm_num [a, parityLift]

/-- Every index here is at least one, so the auxiliary value is irrelevant. -/
theorem a_recurrence (n : ℕ) (hn : 5 ≤ n) : residual a n = 0 :=
  parityLift_recurrence b b_step_two n hn

/-- The requested polynomial-coefficient recurrence, with its coefficients expanded. -/
theorem a089073_recurrence (n : ℕ) (hn : 5 ≤ n) :
    (n : ℚ) * (n + 2) * (23 * (n : ℚ) ^ 2 - 162 * n + 199) * a n +
      12 * (27 * (n : ℚ) ^ 2 - 47 * n - 10) *
        (a (n - 1) - 2 * a (n - 2) + 4 * a (n - 3)) -
      12 * (3 * (n : ℚ) - 13) * (3 * (n : ℚ) - 5) *
        (23 * (n : ℚ) ^ 2 - 116 * n + 60) * a (n - 4) = 0 :=
  a_recurrence n hn

/-- Extending to n=4 forces an auxiliary value 1/2, not an empty-graph count. -/
theorem residual_at_four (c : ℚ) :
    residual (fun n => if n = 0 then c else a n) 4 = 1512 - 3024 * c := by
  norm_num [residual, a, parityLift, b, P, q, r, t, Finset.prod_range_succ]

#print axioms a089073_recurrence
#print axioms residual_at_four

end OEISOpen.A089073
