import OEISOpen.A006343.Algebra
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.NormNum

namespace OEISOpen.A006343
open PowerSeries

local notation "D" => PowerSeries.derivative ℚ
local notation "x" => (PowerSeries.X : PowerSeries ℚ)

private theorem derivative_two : D (2 : PowerSeries ℚ) = 0 :=
  Derivation.map_natCast (derivative ℚ) 2
private theorem derivative_three : D (3 : PowerSeries ℚ) = 0 :=
  Derivation.map_natCast (derivative ℚ) 3

theorem first_derivative (A : PowerSeries ℚ) (hp : P x A = 0) :
    Px x A + Py x A * D A = 0 := by
  have hd := congrArg D hp
  simp [P, map_add, map_sub, Derivation.leibniz, smul_eq_mul, derivative_two] at hd
  unfold Px Py
  linear_combination hd

theorem second_derivative (A : PowerSeries ℚ) (hp : P x A = 0) :
    Pxx x A + 2 * Pxy x A * D A + Pyy x A * (D A) ^ 2 + Py x A * D (D A) = 0 := by
  have hd := congrArg D (first_derivative A hp)
  simp [Px, Py, map_add, map_sub, Derivation.leibniz, smul_eq_mul,
    derivative_two, derivative_three] at hd
  unfold Pxx Pxy Pyy Py
  linear_combination hd

theorem py_coeff_one (A : PowerSeries ℚ)
    (h0 : coeff 0 A = 1) (h1 : coeff 1 A = 0) : coeff 1 (Py x A) = -1 := by
  have hc : constantCoeff A = 1 := by simpa only [coeff_zero_eq_constantCoeff] using h0
  have hc2 : constantCoeff (2 : PowerSeries ℚ) = 2 := by
    exact map_ofNat constantCoeff 2
  simp [Py, coeff_one_mul, coeff_one_pow, hc, h1, hc2]
  ring

theorem py_ne_zero (A : PowerSeries ℚ)
    (h0 : coeff 0 A = 1) (h1 : coeff 1 A = 0) : Py x A ≠ 0 := by
  intro hz
  have h := py_coeff_one A h0 h1
  rw [hz, map_zero] at h
  norm_num at h

/-- The nonhomogeneous equation follows by cancellation of a nonzero series;
`Py x A` is never treated as a unit. -/
theorem differential_equation (A : PowerSeries ℚ) (hp : P x A = 0)
    (h0 : coeff 0 A = 1) (h1 : coeff 1 A = 0) :
    q2 x * D (D A) + q1 x * D A + q0 x * A = residual x := by
  have hc := cleared_equation x A (D A) (D (D A)) hp (first_derivative A hp)
    (cleared_second x A (D A) (D (D A)) (first_derivative A hp) (second_derivative A hp))
  exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ (py_ne_zero A h0 h1)))

end OEISOpen.A006343
