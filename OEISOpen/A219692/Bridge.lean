import OEISOpen.A219692.CoefficientRepresentation
import OEISOpen.A219692.Recurrence
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
The coefficient assembly in Bridge. The positive coefficient evaluation is
unconditional; the remaining bivariate transformation P is an explicit input
to `bridge_of_specialized_transform`, never an axiom or an implicit assumption.
-/
namespace OEISOpen.A219692

open Polynomial

noncomputable def bridgePolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n/2+1),
    C (((2*k).choose k : ℚ) * ((2*n-2*k).choose (n-k) : ℚ) * ((n-k).choose k : ℚ)) *
      X^(3*k) * (1+3*X)^(n-2*k)

theorem coeff_one_add_three_X_pow (N m : ℕ) :
    ((1+3*X : Polynomial ℚ)^N).coeff m = (N.choose m : ℚ)*3^m := by
  have h := Polynomial.comp_C_mul_X_coeff
    (p := (1+X : Polynomial ℚ)^N) (r := (3 : ℚ)) (n := m)
  simpa [Polynomial.coeff_one_add_X_pow, Polynomial.C_ofNat] using h

theorem bridge_polynomial_term_supported (n k : ℕ) (hk : 3*k ≤ n) :
    (C (((2*k).choose k : ℚ) * ((2*n-2*k).choose (n-k) : ℚ) * ((n-k).choose k : ℚ)) *
      X^(3*k) * (1+3*X)^(n-2*k)).coeff n = (positiveTerm n k : ℚ) := by
  rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', ite_eq_left hk,
    coeff_one_add_three_X_pow]
  have hp := congrArg (fun z : ℕ => (z : ℚ)) (bridge_binomial_product n k hk)
  push_cast at hp
  simp only [positiveTerm, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast]
  linear_combination
    (((2*k).choose k : ℚ) * ((2*n-2*k).choose (n-k) : ℚ) * (3 : ℚ)^(n-3*k)) * hp

theorem bridge_polynomial_term_unsupported (n k : ℕ) (hk : n < 3*k) :
    (C (((2*k).choose k : ℚ) * ((2*n-2*k).choose (n-k) : ℚ) * ((n-k).choose k : ℚ)) *
      X^(3*k) * (1+3*X)^(n-2*k)).coeff n = 0 := by
  rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul',
    ite_eq_right (by omega : ¬ 3*k ≤ n), mul_zero]

/-- The positive side of Bridge, independent of P and valid also at n=0. -/
theorem bridgePolynomial_coeff (n : ℕ) : (bridgePolynomial n).coeff n = (v n : ℚ) := by
  unfold bridgePolynomial
  rw [Polynomial.finsetSum_coeff]
  have hcut :
      (∑ k ∈ Finset.range (n/3+1),
        (C (((2*k).choose k : ℚ) * ((2*n-2*k).choose (n-k) : ℚ) * ((n-k).choose k : ℚ)) *
          X^(3*k) * (1+3*X)^(n-2*k)).coeff n) =
      ∑ k ∈ Finset.range (n/2+1),
        (C (((2*k).choose k : ℚ) * ((2*n-2*k).choose (n-k) : ℚ) * ((n-k).choose k : ℚ)) *
          X^(3*k) * (1+3*X)^(n-2*k)).coeff n := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hk
    apply bridge_polynomial_term_unsupported
    have h : ¬ k < n/3+1 := by simpa only [Finset.mem_range] using hk
    omega
  rw [← hcut]
  simp only [v, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply bridge_polynomial_term_supported
  have h := Finset.mem_range.mp hk
  omega

/-- Exactly the specialized transformation still required from P. -/
def SpecializedTransform (n : ℕ) : Prop :=
  convolution n ((1+PowerSeries.X)^3) (-(PowerSeries.X^3)) =
    Polynomial.aeval (PowerSeries.X*(1+PowerSeries.X) : PowerSeries ℚ) (bridgePolynomial n)

/-- B1 and C plus the fully checked positive coefficient evaluation assemble Bridge.
`hP` remains an explicit mathematical obligation, not a claim that P is proved. -/
theorem bridge_of_specialized_transform (n : ℕ) (hn : 1 ≤ n)
    (hP : SpecializedTransform n) : a n = v n := by
  have h := original_coefficient_representation n hn
  rw [show convolution n ((1+PowerSeries.X)^3) (-(PowerSeries.X^3)) =
    Polynomial.aeval (PowerSeries.X*(1+PowerSeries.X) : PowerSeries ℚ) (bridgePolynomial n)
      from hP, coefficient_substitution, bridgePolynomial_coeff] at h
  exact_mod_cast h.symm

/-- T1 reduced to P's precise specialization, with no hidden Bridge hypothesis. -/
theorem normalized_recurrence_of_specialized_transform
    (hP : ∀ n : ℕ, 1 ≤ n → SpecializedTransform n) (n : ℕ) (hn : 2 ≤ n) :
    residual u n = 0 := by
  apply normalized_recurrence_of_bridge (fun m hm => bridge_of_specialized_transform m hm (hP m hm)) n hn

end OEISOpen.A219692
