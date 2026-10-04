import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite certificates for the recurrence of OEIS A371753

This file verifies polynomial identities over `ℚ`.  In particular, it proves
that the proposed second-order recurrence implies the OEIS third-order
recurrence when the index is at least two.  It does not identify a sequence
defined by binomial sums with a solution of the second-order recurrence.
-/

namespace OEISOpen.A371753

def F (n : ℚ) : ℚ := 1047 * n ^ 3 - 1277 * n ^ 2 + 479 * n - 54

def U (n : ℚ) : ℚ :=
  4 * n * (4 * n - 1) * (4 * n - 2) * (4 * n - 3) * F (n - 1)

def V (n : ℚ) : ℚ :=
  5 * (5 * n - 4) * (5 * n - 6) * (5 * n - 7) * (5 * n - 8) * F n

def C (n : ℚ) : ℚ := 8 * (796184150374453 * n - 1374782084855770)

def D (n : ℚ) : ℚ := 5 * (719005061479699 * n - 1438086256867727)

def p0 (n : ℚ) : ℚ :=
  1024 * n * (796184150374453 * n - 1374782084855770) *
    (4 * n - 3) * (2 * n - 1) * (4 * n - 1)

def p1 (n : ℚ) : ℚ :=
  64 * (-4720591427354845074 * n ^ 5 + 16046598674673412696 * n ^ 4 -
    14164434258362644374 * n ^ 3 - 6132680339747354209 * n ^ 2 +
    16406971563067867560 * n - 7312237120275595200)

def p2 (n : ℚ) : ℚ :=
  40 * (-4968388566264801507 * n ^ 5 + 51044954667717039608 * n ^ 4 -
    218029351288077225930 * n ^ 3 + 471970442274586326109 * n ^ 2 -
    511707487331990011785 * n + 221366817798624198360)

def p3 (n : ℚ) : ℚ :=
  -25 * (5 * n - 11) * (719005061479699 * n - 1438086256867727) *
    (5 * n - 9) * (5 * n - 13) * (5 * n - 12)

def R2 (n a b c : ℚ) : ℚ :=
  16 * U n * a + (U n - 16 * V n) * b - V n * c

def R3 (n a b c d : ℚ) : ℚ :=
  p0 n * a + p1 n * b + p2 n * c + p3 n * d

def Q (z : ℚ) : ℚ := z ^ 4 - 5 * z ^ 3 + 11 * z ^ 2 - 15 * z + 16

theorem pole_cancellation (z : ℚ) :
    16 + z * (1 - z) ^ 4 = (1 + z) * Q z := by
  unfold Q
  ring

theorem F_shift (n : ℚ) :
    F (n + 1) = 1047 * n ^ 3 + 1864 * n ^ 2 + 1066 * n + 195 := by
  unfold F
  ring

theorem F_pos (n : ℚ) (hn : 1 ≤ n) : 0 < F n := by
  have h : 0 ≤ n - 1 := sub_nonneg.mpr hn
  have heq := F_shift (n - 1)
  have hp2 : 0 ≤ (n - 1) ^ 2 := sq_nonneg _
  have hp3 : 0 ≤ (n - 1) ^ 3 := pow_nonneg h _
  simp only [sub_add_cancel] at heq
  nlinarith

theorem F_ne_zero (n : ℚ) (hn : 1 ≤ n) : F n ≠ 0 :=
  ne_of_gt (F_pos n hn)

/-! Each of the four coefficients is checked separately. -/

theorem E4_coeff0 (n : ℚ) : F (n - 1) * p0 n = C n * (16 * U n) := by
  unfold p0 C U F
  ring

theorem E4_coeff1 (n : ℚ) :
    F (n - 1) * p1 n = C n * (U n - 16 * V n) + D n * (16 * U (n - 1)) := by
  unfold p1 C D U V F
  ring

theorem E4_coeff2 (n : ℚ) :
    F (n - 1) * p2 n = C n * (-V n) + D n * (U (n - 1) - 16 * V (n - 1)) := by
  unfold p2 C D U V F
  ring

theorem E4_coeff3 (n : ℚ) : F (n - 1) * p3 n = D n * (-V (n - 1)) := by
  unfold p3 D V F
  ring

theorem recurrence_certificate (n a b c d : ℚ) :
    F (n - 1) * R3 n a b c d = C n * R2 n a b c + D n * R2 (n - 1) b c d := by
  unfold R2 R3
  linear_combination E4_coeff0 n * a + E4_coeff1 n * b +
    E4_coeff2 n * c + E4_coeff3 n * d

theorem R3_of_R2 (n a b c d : ℚ) (hn : 2 ≤ n)
    (h0 : R2 n a b c = 0) (h1 : R2 (n - 1) b c d = 0) :
    R3 n a b c d = 0 := by
  have hf : F (n - 1) ≠ 0 := F_ne_zero _ (by linarith)
  have hcert := recurrence_certificate n a b c d
  rw [h0, h1, mul_zero, mul_zero, add_zero] at hcert
  exact (mul_eq_zero.mp hcert).resolve_left hf

theorem R2_of_filtered_relation (n a b c : ℚ)
    (h : U n * (16 * a + b) = V n * (16 * b + c)) : R2 n a b c = 0 := by
  unfold R2
  linear_combination h

/-- Polynomial form of the collapse of the five consecutive binomial ratios.
The extra factor `n` keeps this statement valid at every rational index and
avoids introducing division by `n` or by `5*n-j`.
-/
theorem five_ratio_cleared (n : ℚ) :
    16 * (5 * n) * (5 * n - 1) * (5 * n - 2) * (5 * n - 3) -
      15 * n * (5 * n - 1) * (5 * n - 2) * (5 * n - 3) +
      11 * n * (n - 1) * (5 * n - 2) * (5 * n - 3) -
      5 * n * (n - 1) * (n - 2) * (5 * n - 3) +
      n * (n - 1) * (n - 2) * (n - 3) = 8 * n * F n := by
  unfold F
  ring

/-- Cleared shift-quotient certificate used after the factorial ratio for
`choose (5*n) n` and the filtered closed formula have been established. -/
theorem hypergeometric_shift_cleared (n : ℚ) :
    U n * (8 * F n) *
        (5 * (5 * (n - 1) - 1) * (5 * (n - 1) - 2) * (5 * (n - 1) - 3)) *
        ((5 * n) * (5 * n - 1) * (5 * n - 2) * (5 * n - 3) * (5 * n - 4)) =
      V n * (8 * F (n - 1)) *
        (5 * (5 * n - 1) * (5 * n - 2) * (5 * n - 3)) *
        (n * (4 * n) * (4 * n - 1) * (4 * n - 2) * (4 * n - 3)) := by
  unfold U V F
  ring

/-- Denominator of the filtered closed formula, before any cancellation. -/
def denom (n : ℚ) : ℚ := 5 * (5 * n - 1) * (5 * n - 2) * (5 * n - 3)

theorem denom_pos (n : ℚ) (hn : 1 ≤ n) : 0 < denom n := by
  have h1 : 0 < 5 * n - 1 := by linarith
  have h2 : 0 < 5 * n - 2 := by linarith
  have h3 : 0 < 5 * n - 3 := by linarith
  unfold denom
  positivity

/-- The two closed formulas and the binomial cross-shift imply the filtered
recurrence.  All premises and the proof use cross products, not division. -/
theorem filtered_relation_of_closed_forms (n h h' b b' : ℚ) (hn : 2 ≤ n)
    (h0 : denom n * h = 8 * F n * b)
    (h1 : denom (n - 1) * h' = 8 * F (n - 1) * b')
    (hs : (n * (4 * n) * (4 * n - 1) * (4 * n - 2) * (4 * n - 3)) * b =
      ((5 * n) * (5 * n - 1) * (5 * n - 2) * (5 * n - 3) * (5 * n - 4)) * b') :
    U n * h = V n * h' := by
  let l : ℚ := n * (4 * n) * (4 * n - 1) * (4 * n - 2) * (4 * n - 3)
  let p : ℚ := (5 * n) * (5 * n - 1) * (5 * n - 2) * (5 * n - 3) * (5 * n - 4)
  have hl : 0 < l := by
    have hn0 : 0 < n := by linarith
    have hn1 : 0 < 4 * n - 1 := by linarith
    have hn2 : 0 < 4 * n - 2 := by linarith
    have hn3 : 0 < 4 * n - 3 := by linarith
    dsimp [l]
    positivity
  have hd0 : 0 < denom n := denom_pos n (by linarith)
  have hd1 : 0 < denom (n - 1) := denom_pos (n - 1) (by linarith)
  have hprod : denom n * denom (n - 1) * l ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos hd0 hd1) hl)
  apply mul_left_cancel₀ hprod
  have hc : U n * (8 * F n) * denom (n - 1) * p =
      V n * (8 * F (n - 1)) * denom n * l := hypergeometric_shift_cleared n
  change l * b = p * b' at hs
  linear_combination (U n * denom (n - 1) * l) * h0 +
    (8 * U n * F n * denom (n - 1)) * hs -
    (V n * denom n * l) * h1 + b' * hc

end OEISOpen.A371753

#print axioms OEISOpen.A371753.pole_cancellation
#print axioms OEISOpen.A371753.F_pos
#print axioms OEISOpen.A371753.five_ratio_cleared
#print axioms OEISOpen.A371753.hypergeometric_shift_cleared
#print axioms OEISOpen.A371753.E4_coeff0
#print axioms OEISOpen.A371753.E4_coeff1
#print axioms OEISOpen.A371753.E4_coeff2
#print axioms OEISOpen.A371753.E4_coeff3
#print axioms OEISOpen.A371753.recurrence_certificate
#print axioms OEISOpen.A371753.R3_of_R2
#print axioms OEISOpen.A371753.filtered_relation_of_closed_forms
