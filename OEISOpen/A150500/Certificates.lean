import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Central

/-! Kernel-checkable algebraic components for the A150500 proof.
These theorems do not by themselves connect the original walk count to a series.
All variables in the certificate are in a commutative ring, so no division or
exceptional-parameter assumption is hidden in the cleared identities. -/
namespace OEISOpen.A150500

section Certificate
variable {R : Type*} [CommRing R]

def alpha (t : R) : R := 1 - 22*t^2 - 24*t^3 + 45*t^4
def beta (t : R) : R := 2 - 9*t - 61*t^2 - 3*t^3 + 135*t^4
def gamma (t : R) : R := 1 - 13*t - 19*t^2 + 21*t^3 + 90*t^4
def delta (t : R) : R := alpha t + beta t

theorem alpha_factor (t : R) :
    alpha t = (1-t)*(1-5*t)*(1+3*t)^2 := by unfold alpha; ring

/-- Coefficient of F'', multiplied by (1-t)^7. -/
theorem pullback_second (t : R) :
    alpha t * t^3 * (1+3*t) =
    t^3 * (1+3*t)^2 * (1-t) * ((1-t)^2 - 16*t^2) := by
  unfold alpha
  ring

/-- Coefficient of F', multiplied by 2*(1-t)^5. -/
theorem pullback_first (t : R) :
    t * (alpha t * (-1+9*t+12*t^2) + delta t * (1+3*t)*(1-t)) =
    2*t*(1+3*t)^2*(1-t)*((1-t)^2-32*t^2) := by
  unfold delta alpha beta
  ring

/-- Coefficient of F, multiplied by 4*t*(1-t)^3. -/
theorem pullback_zero (t : R) :
    (2*alpha t - delta t + gamma t)*(1-t)^3 + 8*alpha t*t^3 +
      4*delta t*t^2*(1-t) + 4*gamma t*t*(1-t)^2 =
    -16*t^2*(1+3*t)^2*(1-t) := by
  unfold delta alpha beta gamma
  ring

/-- Inhomogeneous remainder, multiplied by 4*t. -/
theorem pullback_constant (t : R) :
    -2*alpha t + delta t - gamma t - 4*t*(1-5*t) = 0 := by
  unfold delta alpha beta gamma
  ring

def r4Poly (n a b c d e : R) : R :=
  (n+1)^2*a - (9*n+4)*b + (-22*n^2+27*n+15)*c -
    3*(n-2)*(8*n-31)*d + 45*(n-2)*(n-3)*e

def r3Poly (n a b c d : R) : R :=
  (n+1)^2*(8*n-5)*a - (24*n^3+33*n^2-13*n-20)*b -
    (n-1)*(104*n^2-105*n-69)*c + 15*(n-1)*(n-2)*(8*n+3)*d

/-- An identity for arbitrary entries of an arbitrary sequence. -/
theorem r3_r4_relation (n a b c d e : R) :
    r3Poly n a b c d + 3*r3Poly (n-1) b c d e =
    (8*n-5)*r4Poly n a b c d e := by
  unfold r3Poly r4Poly
  ring

/-- Audit of the n-j substitution in each left-multiplied theta operator. -/
theorem operator_shifts (n : R) :
    -(9*(n-1)+13) = -(9*n+4) ∧
    -22*(n-2)^2-61*(n-2)-19 = -22*n^2+27*n+15 ∧
    -3*((n-3)+1)*(8*(n-3)-7) = -3*(n-2)*(8*n-31) ∧
    45*((n-4)+2)*((n-4)+1) = 45*(n-2)*(n-3) := by
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring
end Certificate

/-- B9, directly from Mathlib's central binomial recurrence. -/
theorem central_square_recurrence (k : ℕ) :
    (k+1)^2 * (Nat.centralBinom (k+1))^2 =
    4*(2*k+1)^2*(Nat.centralBinom k)^2 := by
  calc
    _ = ((k+1)*Nat.centralBinom (k+1))^2 := by ring
    _ = (2*(2*k+1)*Nat.centralBinom k)^2 := by
      rw [Nat.succ_mul_centralBinom_succ]
    _ = _ := by ring

end OEISOpen.A150500
