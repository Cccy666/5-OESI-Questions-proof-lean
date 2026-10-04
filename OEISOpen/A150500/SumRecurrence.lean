import OEISOpen.A150500.SeriesPullback
import OEISOpen.A150500.Recurrence
import OEISOpen.A150500.BinomialTransform

/-! Unconditional recurrence for the explicit binomial sum.
The original path count is a separately defined object. -/
namespace OEISOpen.A150500
open PowerSeries

theorem aSumSeries_target : targetOperator aSumSeries = 1-5*X := by
  apply target_of_generating_function
  simpa only [gauge, rho, geom, geometricSeries_eq_inverse] using aSumSeries_bridge

theorem aSum_recurrence (n : ℕ) (hn : 4 ≤ n) :
    ((n:ℚ)+1)^2 * aSum n - (9*(n:ℚ)+4)*aSum (n-1) +
      (-22*(n:ℚ)^2+27*(n:ℚ)+15)*aSum (n-2) -
      3*((n:ℚ)-2)*(8*(n:ℚ)-31)*aSum (n-3) +
      45*((n:ℚ)-2)*((n:ℚ)-3)*aSum (n-4) = 0 := by
  simpa only [aSumSeries, coeff_mk] using
    recurrence_of_target_explicit aSumSeries aSumSeries_target n hn

end OEISOpen.A150500
