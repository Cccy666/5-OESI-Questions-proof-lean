import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

/-!
# A006343: extraction of the six-term recurrence

This module proves the coefficient step independently of the algebraic certificate.
The differential equation is deliberately inhomogeneous. Its right hand side has
degree two, and the recurrence is asserted only for `n ≥ 5`.
-/

namespace OEISOpen.A006343

open PowerSeries

noncomputable section

/-- The Euler operator on rational formal power series. -/
def coeffEuler (A : PowerSeries ℚ) : PowerSeries ℚ :=
  X * derivative ℚ A

theorem coeff_coeffEuler (A : PowerSeries ℚ) (n : ℕ) :
    coeff n (coeffEuler A) = (n : ℚ) * coeff n A := by
  cases n with
  | zero => simp [coeffEuler]
  | succ n =>
    rw [coeffEuler, mul_comm, coeff_succ_mul_X, coeff_derivative]
    push_cast
    ring

/-- A quadratic polynomial in the Euler operator. -/
def coeffEulerPoly (a b c : ℚ) (A : PowerSeries ℚ) : PowerSeries ℚ :=
  C a * coeffEuler (coeffEuler A) + C b * coeffEuler A + C c * A

theorem coeff_coeffEulerPoly (a b c : ℚ) (A : PowerSeries ℚ) (n : ℕ) :
    coeff n (coeffEulerPoly a b c A) =
      (a * (n : ℚ) ^ 2 + b * (n : ℚ) + c) * coeff n A := by
  simp only [coeffEulerPoly, map_add, coeff_C_mul, coeff_coeffEuler]
  ring

theorem coeff_shift_coeffEulerPoly (a b c : ℚ) (A : PowerSeries ℚ)
    (n j : ℕ) (h : j ≤ n) :
    coeff n (X ^ j * coeffEulerPoly a b c A) =
      (a * ((n : ℚ) - j) ^ 2 + b * ((n : ℚ) - j) + c) * coeff (n - j) A := by
  rw [coeff_X_pow_mul', ite_eq_left h, coeff_coeffEulerPoly, Nat.cast_sub h]

/-- The differential operator written in a form with coefficient shifts at most five. -/
def coeffRecurrenceOperator (A : PowerSeries ℚ) : PowerSeries ℚ :=
  coeffEulerPoly (-1) (-2) 3 A +
  X ^ 1 * coeffEulerPoly 11 20 (-36) A +
  X ^ 2 * coeffEulerPoly (-37) (-66) 103 A +
  X ^ 3 * coeffEulerPoly 29 49 (-36) A +
  X ^ 4 * coeffEulerPoly 61 199 138 A +
  X ^ 5 * coeffEulerPoly (-155) (-465) (-310) A

theorem coeffRecurrenceOperator_eq (A : PowerSeries ℚ) :
    coeffRecurrenceOperator A =
      (-X ^ 2 * (5 * X - 1) * (31 * X ^ 4 - 6 * X ^ 3 - 7 * X ^ 2 + 6 * X - 1)) *
          derivative ℚ (derivative ℚ A) +
      (-X * (620 * X ^ 5 - 260 * X ^ 4 - 78 * X ^ 3 + 103 * X ^ 2 - 31 * X + 3)) *
          derivative ℚ A +
      (-310 * X ^ 5 + 138 * X ^ 4 - 36 * X ^ 3 + 103 * X ^ 2 - 36 * X + 3) * A := by
  simp only [coeffRecurrenceOperator, coeffEulerPoly, coeffEuler,
    Derivation.leibniz, derivative_X, smul_eq_mul, map_neg, map_ofNat, map_one]
  ring

/-- The exact six-term recurrence, with all polynomial arithmetic in `ℚ`. -/
def coeffRecurrence (A : PowerSeries ℚ) (n : ℕ) : ℚ :=
  -((n : ℚ) + 3) * ((n : ℚ) - 1) * coeff n A +
  (11 * (n : ℚ) ^ 2 - 2 * (n : ℚ) - 45) * coeff (n - 1) A -
  (37 * (n : ℚ) + 29) * ((n : ℚ) - 3) * coeff (n - 2) A +
  (29 * (n : ℚ) ^ 2 - 125 * (n : ℚ) + 78) * coeff (n - 3) A +
  (61 * (n : ℚ) - 106) * ((n : ℚ) - 3) * coeff (n - 4) A -
  155 * ((n : ℚ) - 3) * ((n : ℚ) - 4) * coeff (n - 5) A

theorem coeff_coeffRecurrenceOperator (A : PowerSeries ℚ) (n : ℕ) (hn : 5 ≤ n) :
    coeff n (coeffRecurrenceOperator A) = coeffRecurrence A n := by
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := by omega
  simp only [coeffRecurrenceOperator, map_add, coeff_coeffEulerPoly,
    coeff_shift_coeffEulerPoly _ _ _ _ _ _ h1,
    coeff_shift_coeffEulerPoly _ _ _ _ _ _ h2,
    coeff_shift_coeffEulerPoly _ _ _ _ _ _ h3,
    coeff_shift_coeffEulerPoly _ _ _ _ _ _ h4,
    coeff_shift_coeffEulerPoly _ _ _ _ _ _ hn]
  unfold coeffRecurrence
  push_cast
  ring

/-- The inhomogeneous differential equation implies Mathar's recurrence for `n ≥ 5`. -/
theorem recurrence_of_differential_equation (A : PowerSeries ℚ)
    (h :
      (-X ^ 2 * (5 * X - 1) * (31 * X ^ 4 - 6 * X ^ 3 - 7 * X ^ 2 + 6 * X - 1)) *
          derivative ℚ (derivative ℚ A) +
      (-X * (620 * X ^ 5 - 260 * X ^ 4 - 78 * X ^ 3 + 103 * X ^ 2 - 31 * X + 3)) *
          derivative ℚ A +
      (-310 * X ^ 5 + 138 * X ^ 4 - 36 * X ^ 3 + 103 * X ^ 2 - 36 * X + 3) * A =
      3 - 36 * X + 98 * X ^ 2)
    (n : ℕ) (hn : 5 ≤ n) : coeffRecurrence A n = 0 := by
  rw [← coeffRecurrenceOperator_eq] at h
  have hc := congrArg (coeff n) h
  rw [coeff_coeffRecurrenceOperator A n hn] at hc
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn2 : n ≠ 2 := by omega
  have hR : (3 - 36 * X + 98 * X ^ 2 : PowerSeries ℚ) =
      C 3 - C 36 * X + C 98 * X ^ 2 := by
    simp only [map_ofNat]
  rw [hR] at hc
  simpa [coeff_C, coeff_X, hn0, hn1, hn2] using hc

end

end OEISOpen.A006343
