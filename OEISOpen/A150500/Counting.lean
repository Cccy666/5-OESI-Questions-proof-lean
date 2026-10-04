import OEISOpen.A150500.Insertion
import OEISOpen.A150500.Meanders
import OEISOpen.A150500.BinomialTransform

/-! The combinatorial bridge from the original five-step prefix count to the
explicit binomial sum. Both ingredients are finite-cardinality theorems. -/
namespace OEISOpen.A150500

theorem pathCount_eq_aSum (n : ℕ) : (pathCount n : ℚ) = aSum n := by
  rw [pathCount_eq_sum_moving]
  simp only [aSum, Nat.cast_sum, Nat.cast_mul, movingPathCount_eq_choose_square,
    Nat.cast_pow, meanderSquare]

end OEISOpen.A150500
