import OEISOpen.A371753.SumBridge
import OEISOpen.A371753.Binomial
import OEISOpen.A371753.Hypergeometric
import Mathlib.Tactic.IntervalCases

/-!
Self-contained formalization of the exact recurrence supplied for A371753.
The sequence `a` is the original finite binomial sum, with `a 0 = 1`.
This is a new local formalization, not a claimed solution of an official
LeanOpenProblems benchmark file.
-/
namespace OEISOpen.A371753

theorem filtered_closed (n : ℕ) (hn : 1 ≤ n) :
    5*(5*(n:ℚ)-1)*(5*(n:ℚ)-2)*(5*(n:ℚ)-3)*(16*a n+a (n-1)) =
      8*F n*((5*n).choose n : ℚ) := by
  by_cases hsmall : n < 4
  · interval_cases n <;> norm_num [a, F, Finset.sum_range_succ, Nat.choose]
  · rw [filtered_five n (by omega)]
    simpa only [binom] using five_binomial_collapse n (by omega)

theorem filtered_recurrence (n : ℕ) (hn : 2 ≤ n) :
    U n * (16*a n+a (n-1)) = V n * (16*a (n-1)+a (n-2)) := by
  refine filtered_relation_of_closed_forms (n:ℚ) _ _
    ((5*n).choose n : ℚ) ((5*(n-1)).choose (n-1) : ℚ)
    (by exact_mod_cast hn) ?_ ?_ ?_
  · exact filtered_closed n (by omega)
  · have hp := filtered_closed (n-1) (by omega)
    have hc : ((n-1 : ℕ) : ℚ) = (n:ℚ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [hc, show n-1-1 = n-2 by omega] at hp
    exact hp
  · exact binomial_shift_cleared n (by omega)

theorem second_order_recurrence (n : ℕ) (hn : 2 ≤ n) :
    R2 n (a n) (a (n-1)) (a (n-2)) = 0 :=
  R2_of_filtered_relation _ _ _ _ (filtered_recurrence n hn)

theorem third_order_recurrence (n : ℕ) (hn : 3 ≤ n) :
    R3 n (a n) (a (n-1)) (a (n-2)) (a (n-3)) = 0 := by
  refine R3_of_R2 (n:ℚ) _ _ _ _ (by exact_mod_cast (show 2 ≤ n by omega))
    (second_order_recurrence n (by omega)) ?_
  have hp := second_order_recurrence (n-1) (by omega)
  have hc : ((n-1 : ℕ) : ℚ) = (n:ℚ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [hc, show n-1-1 = n-2 by omega, show n-1-2 = n-3 by omega] at hp
  exact hp

/-- The exact OEIS recurrence, for every required natural index. -/
theorem recurrence (n : ℕ) (hn : 3 ≤ n) :
    p0 n*a n + p1 n*a (n-1) + p2 n*a (n-2) + p3 n*a (n-3) = 0 :=
  third_order_recurrence n hn

end OEISOpen.A371753

#print axioms OEISOpen.A371753.filtered_closed
#print axioms OEISOpen.A371753.filtered_recurrence
#print axioms OEISOpen.A371753.second_order_recurrence
#print axioms OEISOpen.A371753.third_order_recurrence
#print axioms OEISOpen.A371753.recurrence
