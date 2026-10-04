import OEISOpen.A219692.Definitions
import OEISOpen.A219692.Coefficient
import OEISOpen.A219692.BinomialTransform

/-! Original alternating sum as a coefficient of the bivariate convolution. -/
namespace OEISOpen.A219692

open PowerSeries

noncomputable def convolution (n : ℕ) (A B : PowerSeries ℚ) : PowerSeries ℚ :=
  ∑ j ∈ Finset.range (n+1),
    C ((n.choose j : ℚ) * ((2*j).choose j : ℚ) * ((2*n-2*j).choose (n-j) : ℚ)) *
      A^(n-j) * B^j

theorem coeff_oneAddX_pow (m r : ℕ) :
    PowerSeries.coeff r ((1+X : PowerSeries ℚ)^m) = (m.choose r : ℚ) := by
  calc
    _ = PowerSeries.coeff r (((1+Polynomial.X : Polynomial ℚ)^m : Polynomial ℚ) :
        PowerSeries ℚ) := by simp
    _ = _ := by rw [Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem inverse_power_cancel_left (m k : ℕ) :
    inverseOneAddX^m * (1+X : PowerSeries ℚ)^(m+k) = (1+X)^k := by
  rw [pow_add, ← mul_assoc]
  have hc : inverseOneAddX^m * (1+X : PowerSeries ℚ)^m = 1 := by
    simpa using inverse_power_cancel 0 m
  rw [hc, one_mul]

theorem coeff_original_bracket (M n : ℕ) (hn : 1 ≤ n) (hMn : n ≤ M) :
    PowerSeries.coeff (M-n) ((1+2*X : PowerSeries ℚ)*(1+X)^(M-1)) =
      ((M-1).choose n : ℚ) + (M.choose n : ℚ) := by
  by_cases he : M = n
  · subst M
    simp [Nat.choose_eq_zero_of_lt (by omega : n-1 < n)]
  have hm : 1 ≤ M := by omega
  have hdecomp : (1+2*X : PowerSeries ℚ)*(1+X)^(M-1) =
      (1+X)^M + X*(1+X)^(M-1) := by
    calc
      _ = (1+X : PowerSeries ℚ)^(M-1)*(1+X) + X*(1+X)^(M-1) := by ring
      _ = _ := by rw [← pow_succ, show M-1+1 = M by omega]
  rw [hdecomp, map_add, coeff_oneAddX_pow]
  have hx := PowerSeries.coeff_X_pow_mul' ((1+X : PowerSeries ℚ)^(M-1)) 1 (M-n)
  simp only [pow_one, ite_eq_left (by omega : 1 ≤ M-n)] at hx
  rw [hx, coeff_oneAddX_pow, Nat.choose_symm hMn]
  have hs : (M-1).choose (M-n-1) = (M-1).choose n := by
    rw [show M-n-1 = M-1-n by omega, Nat.choose_symm (by omega : n ≤ M-1)]
  rw [hs]
  ring

theorem original_coefficient_term_factor (n j : ℕ) (c : ℚ) :
    (1+2*X : PowerSeries ℚ)*inverseOneAddX^(n+1) *
      (C c * ((1+X)^3)^(n-j) * (-(X^3))^j) =
      C ((-1 : ℚ)^j * c) *
        (X^(3*j) * ((1+2*X)*inverseOneAddX^(n+1)*(1+X)^(3*(n-j)))) := by
  have hneg : (-(X^3 : PowerSeries ℚ))^j = C ((-1 : ℚ)^j) * X^(3*j) := by
    rw [neg_pow, ← pow_mul]
    simp
  rw [hneg, ← pow_mul, map_mul]
  ring

theorem coeff_original_term_supported (n j : ℕ) (hn : 1 ≤ n) (hj : 3*j ≤ n) :
    PowerSeries.coeff n
      ((1+2*X : PowerSeries ℚ)*inverseOneAddX^(n+1) *
        (C ((n.choose j : ℚ) * ((2*j).choose j : ℚ) * ((2*n-2*j).choose (n-j) : ℚ)) *
          ((1+X)^3)^(n-j) * (-(X^3))^j)) = (originalTerm n j : ℚ) := by
  rw [original_coefficient_term_factor, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', ite_eq_left hj]
  have he : 3*(n-j) = (n+1)+(2*n-3*j-1) := by omega
  rw [he, mul_assoc (1+2*X), inverse_power_cancel_left]
  have hind : n-3*j = (2*n-3*j)-n := by omega
  rw [hind, coeff_original_bracket (2*n-3*j) n hn (by omega)]
  simp only [originalTerm, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, Int.cast_add]
  ring

theorem coeff_original_term_unsupported (n j : ℕ) (hj : n < 3*j) :
    PowerSeries.coeff n
      ((1+2*X : PowerSeries ℚ)*inverseOneAddX^(n+1) *
        (C ((n.choose j : ℚ) * ((2*j).choose j : ℚ) * ((2*n-2*j).choose (n-j) : ℚ)) *
          ((1+X)^3)^(n-j) * (-(X^3))^j)) = 0 := by
  rw [original_coefficient_term_factor, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega : ¬ 3*j ≤ n), mul_zero]

/-- B1, with every supported and unsupported summand and the original n≥1 convention checked. -/
theorem original_coefficient_representation (n : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff n
      ((1+2*X : PowerSeries ℚ)*inverseOneAddX^(n+1) *
        convolution n ((1+X)^3) (-(X^3))) = (a n : ℚ) := by
  unfold convolution
  rw [Finset.mul_sum, map_sum]
  have hsum :
      (∑ j ∈ Finset.range (n+1), PowerSeries.coeff n
        ((1+2*X : PowerSeries ℚ)*inverseOneAddX^(n+1) *
          (C ((n.choose j : ℚ) * ((2*j).choose j : ℚ) * ((2*n-2*j).choose (n-j) : ℚ)) *
            ((1+X)^3)^(n-j) * (-(X^3))^j))) =
      ∑ j ∈ Finset.range (n/3+1), PowerSeries.coeff n
        ((1+2*X : PowerSeries ℚ)*inverseOneAddX^(n+1) *
          (C ((n.choose j : ℚ) * ((2*j).choose j : ℚ) * ((2*n-2*j).choose (n-j) : ℚ)) *
            ((1+X)^3)^(n-j) * (-(X^3))^j)) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    apply coeff_original_term_unsupported
    have h : ¬ j < n/3+1 := by simpa only [Finset.mem_range] using hj
    omega
  rw [hsum]
  have ha : (a n : ℚ) = ∑ j ∈ Finset.range (n/3+1), (originalTerm n j : ℚ) := by
    simp only [a, ite_eq_right (by omega : n ≠ 0), Int.cast_sum]
  rw [ha]
  apply Finset.sum_congr rfl
  intro j hj
  apply coeff_original_term_supported n j hn
  have h := Finset.mem_range.mp hj
  omega

end OEISOpen.A219692
