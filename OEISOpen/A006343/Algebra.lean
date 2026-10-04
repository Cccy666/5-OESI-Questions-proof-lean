import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Finite integer certificate for the A006343 algebraic generating function.
This file uses no assumption about a sequence or about formal differentiation. -/
namespace OEISOpen.A006343

variable {K : Type*} [CommRing K]

def P (x y : K) : K := x ^ 3 * y ^ 3 - (x - 1) * y ^ 2 + (x - 2) * y + 1
def Px (x y : K) : K := 3 * x ^ 2 * y ^ 3 - y ^ 2 + y
def Py (x y : K) : K := 3 * x ^ 3 * y ^ 2 - 2 * (x - 1) * y + x - 2
def Pxx (x y : K) : K := 6 * x * y ^ 3
def Pxy (x y : K) : K := 9 * x ^ 2 * y ^ 2 - 2 * y + 1
def Pyy (x y : K) : K := 6 * x ^ 3 * y - 2 * (x - 1)
def H (x y : K) : K :=
  Pxx x y * Py x y ^ 2 - 2 * Pxy x y * Px x y * Py x y + Pyy x y * Px x y ^ 2
def q2 (x : K) : K := -x ^ 2 * (5 * x - 1) * (31 * x ^ 4 - 6 * x ^ 3 - 7 * x ^ 2 + 6 * x - 1)
def q1 (x : K) : K := -x * (620 * x ^ 5 - 260 * x ^ 4 - 78 * x ^ 3 + 103 * x ^ 2 - 31 * x + 3)
def q0 (x : K) : K := -310 * x ^ 5 + 138 * x ^ 4 - 36 * x ^ 3 + 103 * x ^ 2 - 36 * x + 3
def residual (x : K) : K := 3 - 36 * x + 98 * x ^ 2

def quotient (x y : K) : K :=
  -1512*x^9*y^4 + 3564*x^8*y^4 - 1215*x^7*y^4 + 2016*x^7*y^3
  -1218*x^7*y^2 + 108*x^6*y^4 - 6768*x^6*y^3 + 6534*x^6*y^2
  -1230*x^6*y + 6372*x^5*y^3 - 8904*x^5*y^2 + 3408*x^5*y
  -98*x^5 - 1764*x^4*y^3 + 4410*x^4*y^2 - 3288*x^4*y + 624*x^4
  +144*x^3*y^3 - 2802*x^3*y^2 + 4014*x^3*y - 1395*x^3
  +1554*x^2*y^2 - 2784*x^2*y + 1234*x^2 - 348*x*y^2 + 672*x*y
  -324*x + 24*y^2 - 48*y + 24

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
-- Expanding the 30-term integer certificate needs a larger normalization budget.
theorem certificate (x y : K) :
    -q2 x * H x y - q1 x * Px x y * Py x y ^ 2
      + (q0 x * y - residual x) * Py x y ^ 3 = quotient x y * P x y := by
  unfold q2 q1 q0 H Pxx Pxy Pyy Px Py residual quotient P
  ring

theorem cleared_second (x y a b : K)
    (h1 : Px x y + Py x y * a = 0)
    (h2 : Pxx x y + 2 * Pxy x y * a + Pyy x y * a ^ 2 + Py x y * b = 0) :
    Py x y ^ 3 * b = -H x y := by
  unfold H
  linear_combination (Py x y)^2 * h2 -
    (2 * Pxy x y * Py x y + Pyy x y * (Py x y * a - Px x y)) * h1

theorem cleared_equation (x y a b : K) (hp : P x y = 0)
    (h1 : Px x y + Py x y * a = 0)
    (h2 : Py x y ^ 3 * b = -H x y) :
    Py x y ^ 3 * (q2 x * b + q1 x * a + q0 x * y - residual x) = 0 := by
  have hc := certificate x y
  rw [hp, mul_zero] at hc
  linear_combination hc + q2 x * h2 + q1 x * Py x y ^ 2 * h1

end OEISOpen.A006343
