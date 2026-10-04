import OEISOpen.A006343.Differential
import OEISOpen.A006343.Coefficients

/-!
# A006343: the specified recurrence from its algebraic generating function

This is a project-authored formal statement. The algebraic generating-function
identity is an explicit permitted input; no combinatorial definition is hidden
in an axiom. Polynomial coefficients and subtraction are interpreted in ℚ.
-/
namespace OEISOpen.A006343
open PowerSeries

/-- Every rational formal series on the specified algebraic branch satisfies
the six-term recurrence for every natural index at least five. -/
theorem recurrence_of_algebraic (A : PowerSeries ℚ)
    (hP : X ^ 3 * A ^ 3 - (X - 1) * A ^ 2 + (X - 2) * A + 1 = 0)
    (h0 : coeff 0 A = 1) (h1 : coeff 1 A = 0)
    (n : ℕ) (hn : 5 ≤ n) :
    -((n : ℚ) + 3) * ((n : ℚ) - 1) * coeff n A
      + (11 * (n : ℚ)^2 - 2 * (n : ℚ) - 45) * coeff (n - 1) A
      - (37 * (n : ℚ) + 29) * ((n : ℚ) - 3) * coeff (n - 2) A
      + (29 * (n : ℚ)^2 - 125 * (n : ℚ) + 78) * coeff (n - 3) A
      + (61 * (n : ℚ) - 106) * ((n : ℚ) - 3) * coeff (n - 4) A
      - 155 * ((n : ℚ) - 3) * ((n : ℚ) - 4) * coeff (n - 5) A = 0 := by
  have hd := differential_equation A hP h0 h1
  exact recurrence_of_differential_equation A hd n hn

end OEISOpen.A006343
