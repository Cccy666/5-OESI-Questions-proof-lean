import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

/-! The coefficient substitution behind the finite binomial bridge. -/
namespace OEISOpen.A219692

open PowerSeries

noncomputable def inverseOneAddX : PowerSeries ℚ := (1 + X)⁻¹

theorem oneAddX_mul_inverse :
    (1 + X : PowerSeries ℚ) * inverseOneAddX = 1 := by
  apply PowerSeries.mul_inv_cancel
  simp

theorem derivative_inverse_power (r : ℕ) :
    PowerSeries.derivative ℚ (inverseOneAddX ^ r) =
      -(r : PowerSeries ℚ) * inverseOneAddX ^ (r+1) := by
  cases r with
  | zero => simp
  | succ r =>
    rw [PowerSeries.derivative_pow]
    simp only [Nat.add_sub_cancel, inverseOneAddX, PowerSeries.derivative_inv',
      map_add, PowerSeries.derivative_one, PowerSeries.derivative_X, zero_add, mul_one]
    simp only [pow_succ]
    ring

theorem coeff_inverse_kernel_succ (r : ℕ) :
    PowerSeries.coeff (r+1)
      ((1 + 2*X : PowerSeries ℚ) * inverseOneAddX ^ (r+2)) = 0 := by
  have h := congrArg (PowerSeries.coeff r) (derivative_inverse_power (r+1))
  rw [PowerSeries.coeff_derivative] at h
  have hid : (1 + 2*X : PowerSeries ℚ) * inverseOneAddX ^ (r+2) =
      inverseOneAddX ^ (r+1) + X * inverseOneAddX ^ (r+2) := by
    have hc := congrArg (fun f : PowerSeries ℚ => f * inverseOneAddX ^ (r+1))
      oneAddX_mul_inverse
    simp only [one_mul] at hc
    calc
      _ = (1 + X) * inverseOneAddX * inverseOneAddX ^ (r+1) +
          X * inverseOneAddX ^ (r+2) := by ring
      _ = _ := by rw [hc]
  rw [hid, map_add]
  have hX : PowerSeries.coeff (r+1) (X * inverseOneAddX ^ (r+2)) =
      PowerSeries.coeff r (inverseOneAddX ^ (r+2)) := by
    simpa only [pow_one] using
      (PowerSeries.coeff_X_pow_mul (inverseOneAddX ^ (r+2)) 1 r)
  rw [hX]
  have hclean :
      PowerSeries.coeff (r+1) (inverseOneAddX ^ (r+1)) * ((r : ℚ)+1) =
      -((r : ℚ)+1) * PowerSeries.coeff r (inverseOneAddX ^ (r+2)) := by
    rw [show (-(↑(r+1)) : PowerSeries ℚ) = C (-((r : ℚ)+1)) by simp,
      PowerSeries.coeff_C_mul] at h
    simpa only [Nat.cast_add, Nat.cast_one, show r+1+1 = r+2 by omega] using h
  have hr : (r : ℚ)+1 ≠ 0 := by positivity
  apply (mul_eq_zero.mp ?_).resolve_left hr
  linear_combination hclean

theorem coeff_inverse_kernel (r : ℕ) :
    PowerSeries.coeff r
      ((1 + 2*X : PowerSeries ℚ) * inverseOneAddX ^ (r+1)) =
      if r = 0 then 1 else 0 := by
  cases r with
  | zero => simp [inverseOneAddX]
  | succ r => simpa using coeff_inverse_kernel_succ r

theorem inverse_power_cancel (k m : ℕ) :
    inverseOneAddX ^ (k+m) * (1 + X : PowerSeries ℚ)^m = inverseOneAddX^k := by
  calc
    _ = inverseOneAddX^k * ((1 + X) * inverseOneAddX)^m := by
      rw [pow_add, mul_pow]
      ring
    _ = _ := by rw [oneAddX_mul_inverse, one_pow, mul_one]

/-- Lemma C for a monomial, including both sides of the coefficient cutoff. -/
theorem coefficient_substitution_monomial (n m : ℕ) :
    PowerSeries.coeff n
      ((1 + 2*X : PowerSeries ℚ) * inverseOneAddX ^ (n+1) * (X*(1+X))^m) =
      if n = m then 1 else 0 := by
  have hfactor :
      (1 + 2*X : PowerSeries ℚ) * inverseOneAddX ^ (n+1) * (X*(1+X))^m =
      X^m * ((1+2*X) * (inverseOneAddX^(n+1) * (1+X)^m)) := by
    rw [mul_pow]
    ring
  rw [hfactor, PowerSeries.coeff_X_pow_mul']
  by_cases hm : m ≤ n
  · rw [ite_eq_left hm]
    rw [show n+1 = (n-m+1)+m by omega, inverse_power_cancel, coeff_inverse_kernel]
    simp only [show (n-m = 0) ↔ n = m by omega]
  · rw [ite_eq_right hm, ite_eq_right (by omega : n ≠ m)]

/-- The complete polynomial coefficient substitution C, as an identity in Q[[X]]. -/
theorem coefficient_substitution (n : ℕ) (Q : Polynomial ℚ) :
    PowerSeries.coeff n
      ((1 + 2*X : PowerSeries ℚ) * inverseOneAddX ^ (n+1) *
        Polynomial.aeval (X*(1+X) : PowerSeries ℚ) Q) = Q.coeff n := by
  induction Q using Polynomial.induction_on' with
  | add Q W hQ hW =>
    rw [map_add, mul_add, map_add, hQ, hW, Polynomial.coeff_add]
  | monomial m c =>
    rw [Polynomial.aeval_monomial, PowerSeries.algebraMap_eq]
    have hfactor :
        (1 + 2*X : PowerSeries ℚ) * inverseOneAddX ^ (n+1) *
          (C c * (X*(1+X))^m) =
        C c * ((1 + 2*X) * inverseOneAddX ^ (n+1) * (X*(1+X))^m) := by ring
    rw [hfactor, PowerSeries.coeff_C_mul, coefficient_substitution_monomial]
    simp only [Polynomial.coeff_monomial]
    by_cases h : n = m
    · subst m
      simp only [ite_true, mul_one]
    · simp only [ite_eq_right h, ite_eq_right (Ne.symm h), mul_zero]

end OEISOpen.A219692
