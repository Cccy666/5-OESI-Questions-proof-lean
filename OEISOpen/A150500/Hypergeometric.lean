import OEISOpen.A150500.Certificates
import Mathlib.RingTheory.PowerSeries.Derivative

/-! The formal power series with central-binomial-square coefficients.
This file proves its hypergeometric differential equation from a coefficient
identity. It does not yet connect this series to the original walk count. -/

namespace OEISOpen.A150500

open PowerSeries

noncomputable def centralSquareSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => (Nat.centralBinom n : ℚ)^2

@[simp] theorem coeff_centralSquareSeries (n : ℕ) :
    coeff n centralSquareSeries = (Nat.centralBinom n : ℚ)^2 := by
  exact coeff_mk _ _

@[simp] theorem constantCoeff_centralSquareSeries :
    constantCoeff centralSquareSeries = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_centralSquareSeries]
  norm_num [Nat.centralBinom]

theorem central_square_recurrence_rat (n : ℕ) :
    (n+1 : ℚ)^2 * (Nat.centralBinom (n+1) : ℚ)^2 =
      4*(2*n+1 : ℚ)^2*(Nat.centralBinom n : ℚ)^2 := by
  exact_mod_cast central_square_recurrence n

noncomputable def euler (F : PowerSeries ℚ) : PowerSeries ℚ :=
  X * derivative ℚ F

@[simp] theorem coeff_euler (n : ℕ) (F : PowerSeries ℚ) :
    coeff n (euler F) = (n : ℚ) * coeff n F := by
  cases n with
  | zero => simp [euler]
  | succ n => simp [euler, coeff_derivative, mul_comm]

theorem centralSquareSeries_euler_equation :
    euler (euler centralSquareSeries) =
      X * (C 16 * euler (euler centralSquareSeries) +
        C 16 * euler centralSquareSeries + C 4 * centralSquareSeries) := by
  ext n
  cases n with
  | zero => simp [euler]
  | succ n =>
    simp only [coeff_euler, coeff_succ_X_mul, map_add, coeff_C_mul,
      coeff_centralSquareSeries, Nat.cast_add, Nat.cast_one]
    have h := central_square_recurrence_rat n
    nlinarith

theorem euler_euler (F : PowerSeries ℚ) :
    euler (euler F) =
      X * (derivative ℚ F + X * derivative ℚ (derivative ℚ F)) := by
  simp only [euler, Derivation.leibniz, derivative_X, smul_eq_mul, mul_one]
  ring

/-- B10: the ordinary second-order equation, including its constant coefficient.
The cancellation used here is multiplication by the series variable, an
injective map; no inverse of the variable is introduced. -/
theorem centralSquareSeries_differential_equation :
    X * (1 - C 16 * X) * derivative ℚ (derivative ℚ centralSquareSeries) +
      (1 - C 32 * X) * derivative ℚ centralSquareSeries -
        C 4 * centralSquareSeries = 0 := by
  have h := centralSquareSeries_euler_equation
  rw [euler_euler] at h
  simp only [euler] at h
  apply X_mul_cancel
  simp only [mul_zero]
  norm_num only [map_ofNat] at h ⊢
  linear_combination h

end OEISOpen.A150500
