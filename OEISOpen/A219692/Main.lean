import OEISOpen.A219692.TransformIdentity
import OEISOpen.A219692.Specialization

/-! Exact final targets. Original `a 0 = 2` and normalized `u 0 = 1` stay separate. -/
namespace OEISOpen.A219692

/-- The formerly missing instance of P is now supplied by the general transformation. -/
theorem specialized_transform (n : ℕ) : SpecializedTransform n := by
  unfold SpecializedTransform
  rw [convolution_eq_binomial_sum, central_binomial_transform, specialized_transform_sum]

/-- Bridge, with its necessary positive-index hypothesis. -/
theorem original_eq_positive (n : ℕ) (hn : 1 ≤ n) : a n = v n := by
  exact bridge_of_specialized_transform n hn (specialized_transform n)

/-- The explicitly normalized original sum equals the positive sum at every index. -/
theorem normalized_eq_positive : u = v := by
  exact normalized_eq_positive_of_bridge original_eq_positive

/-- T1: the normalized original binomial sum satisfies the recurrence from n=2. -/
theorem normalized_recurrence (n : ℕ) (hn : 2 ≤ n) : residual u n = 0 := by
  exact normalized_recurrence_of_bridge original_eq_positive n hn

/-- T2: the original OEIS normalization satisfies the recurrence from n=3. -/
theorem original_tail_recurrence (n : ℕ) (hn : 3 ≤ n) : residual a n = 0 := by
  exact original_tail_recurrence_of_bridge original_eq_positive n hn

/-- T0 and T2 together: the original recurrence has precisely the stated boundary defect. -/
theorem original_residual_from_two (n : ℕ) (hn : 2 ≤ n) :
    residual a n = if n = 2 then 180 else 0 := by
  by_cases h : n = 2
  · subst n
    simp [original_residual_two]
  · rw [ite_eq_right h]
    exact original_tail_recurrence n (by omega)

end OEISOpen.A219692
