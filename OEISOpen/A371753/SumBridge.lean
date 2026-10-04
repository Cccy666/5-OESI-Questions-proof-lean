import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! The original finite sum and its formal-power-series filter. -/
namespace OEISOpen.A371753

open Finset PowerSeries

def a (n : ℕ) : ℚ :=
  if n = 0 then 1 else ∑ k ∈ range (n / 2 + 1),
    ((5 * n - 2 * k - 1).choose (n - 2 * k) : ℚ)

noncomputable def B (m : ℕ) : PowerSeries ℚ := (invOneSubPow ℚ m).val

def E : PowerSeries ℚ := mk fun n => if n % 2 = 0 then 1 else 0

lemma E_inverse : E * (1 - X ^ 2) = (1 : PowerSeries ℚ) := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow']
  simp only [E, coeff_mk]
  rcases n with _ | _ | n
  · norm_num
  · norm_num
  · simp only [show 2 ≤ n + 1 + 1 by omega, ite_true]
    have hm : (n + 1 + 1) % 2 = n % 2 := by omega
    simp [hm]

lemma coeff_B (m k : ℕ) (hm : 0 < m) :
    coeff k (B m) = ((m - 1 + k).choose k : ℚ) := by
  rw [B, invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℚ m hm, coeff_mk,
    Nat.choose_symm_add]

lemma coeff_E_mul (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (E * f) = ∑ k ∈ range (n / 2 + 1), coeff (n - 2 * k) f := by
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [E, coeff_mk, ite_mul, one_mul, zero_mul]
  rw [← sum_filter]
  symm
  refine sum_nbij' (fun k => 2 * k) (fun k => k / 2) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_range] at hk
    simp only [mem_filter, mem_range]
    omega
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    simp only [mem_range]
    omega
  · intro k hk
    omega
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    omega
  · intro k hk
    rfl

theorem a_eq_coeff (n : ℕ) : a n = coeff n (E * B (4 * n)) := by
  by_cases hn : n = 0
  · subst n
    simp [a, E, B, invOneSubPow_zero]
  · rw [a, ite_eq_right hn, coeff_E_mul]
    apply sum_congr rfl
    intro k hk
    have hk' : 2 * k ≤ n := by simp only [mem_range] at hk; omega
    rw [coeff_B (4*n) (n-2*k) (by omega)]
    congr 2
    omega

lemma B_mul (m k : ℕ) : B (m + k) = B m * B k := by
  simp [B, invOneSubPow_add, Units.val_mul]

lemma B_inverse (m : ℕ) : B m * (1-X)^m = (1 : PowerSeries ℚ) := by
  rw [B, ← invOneSubPow_inv_eq_one_sub_pow]
  exact (invOneSubPow ℚ m).val_inv

lemma B_shift (m k : ℕ) : (1-X)^k * B (m+k) = B m := by
  exact one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℚ m k

noncomputable def Qseries : PowerSeries ℚ := 16 - 15*X + 11*X^2 - 5*X^3 + X^4

lemma filter_series (n : ℕ) :
    (16 + X*(1-X)^4) * (E * B (4*n)) = Qseries * B (4*n+1) := by
  apply mul_left_cancel₀ (b := (16 + X*(1-X)^4) * (E * B (4*n)))
    (a := (1-X^2) * (1-X)^(4*n))
    (by
      apply mul_ne_zero
      · intro h
        have := congrArg (coeff 0) h
        norm_num at this
      · apply pow_ne_zero
        intro h
        have := congrArg (coeff 0) h
        norm_num at this)
  have he := E_inverse
  have hb := B_inverse (4*n)
  have hb1 := B_inverse (4*n+1)
  have hleft : ((1-X^2) * (1-X)^(4*n)) *
      ((16+X*(1-X)^4)*(E*B (4*n))) = 16+X*(1-X)^4 := by
    calc
      _ = (16+X*(1-X)^4) * (E*(1-X^2)) * (B (4*n)*(1-X)^(4*n)) := by ring
      _ = _ := by rw [he, hb]; ring
  rw [hleft]
  calc
    _ = Qseries * (1+X) := by unfold Qseries; ring
    _ = Qseries * (1+X) * (B (4*n+1)*(1-X)^(4*n+1)) := by rw [hb1]; ring
    _ = _ := by rw [pow_succ]; ring

theorem filtered_coeff (n : ℕ) (hn : 1 ≤ n) :
    16*a n + a (n-1) = coeff n (Qseries * B (4*n+1)) := by
  rw [← filter_series, add_mul, map_add]
  have hshift : X*(1-X)^4*(E*B (4*n)) = X * (E*B (4*(n-1))) := by
    have hidx : 4*n = 4*(n-1)+4 := by omega
    rw [hidx]
    calc
      _ = X * (E * ((1-X)^4*B (4*(n-1)+4))) := by ring
      _ = _ := by rw [B_shift]
  rw [hshift]
  have hcoeff : coeff n (X*(E*B (4*(n-1)))) = a (n-1) := by
    rw [← pow_one X, coeff_X_pow_mul', ite_eq_left hn, ← a_eq_coeff]
  rw [hcoeff]
  have hc : coeff n (16 * (E*B (4*n))) = 16*a n := by
    rw [show (16 : PowerSeries ℚ) = PowerSeries.C 16 by exact (map_natCast PowerSeries.C 16).symm,
      coeff_C_mul, ← a_eq_coeff]
  rw [hc]

lemma coeff_nat_mul (r n : ℕ) (f : PowerSeries ℚ) :
    coeff n ((r : PowerSeries ℚ)*f) = (r : ℚ)*coeff n f := by
  rw [← map_natCast PowerSeries.C r, coeff_C_mul]

lemma coeff_shift_B (n j : ℕ) (hj : j ≤ n) :
    coeff n (X^j * B (4*n+1)) = ((5*n-j).choose (n-j) : ℚ) := by
  rw [coeff_X_pow_mul', ite_eq_left hj, coeff_B _ _ (by omega)]
  congr 2
  omega

theorem filtered_five (n : ℕ) (hn : 4 ≤ n) :
    16*a n + a (n-1) =
      16 * ((5*n).choose n : ℚ) -
      15 * ((5*n-1).choose (n-1) : ℚ) +
      11 * ((5*n-2).choose (n-2) : ℚ) -
      5 * ((5*n-3).choose (n-3) : ℚ) +
      ((5*n-4).choose (n-4) : ℚ) := by
  rw [filtered_coeff n (by omega)]
  have hpoly : Qseries * B (4*n+1) =
      16*(X^0*B (4*n+1)) - 15*(X^1*B (4*n+1)) +
      11*(X^2*B (4*n+1)) - 5*(X^3*B (4*n+1)) + X^4*B (4*n+1) := by
    unfold Qseries
    ring
  rw [hpoly]
  simp only [map_add, map_sub]
  rw [show (16 : PowerSeries ℚ) = PowerSeries.C 16 by exact (map_natCast PowerSeries.C 16).symm,
    show (15 : PowerSeries ℚ) = PowerSeries.C 15 by exact (map_natCast PowerSeries.C 15).symm,
    show (11 : PowerSeries ℚ) = PowerSeries.C 11 by exact (map_natCast PowerSeries.C 11).symm,
    show (5 : PowerSeries ℚ) = PowerSeries.C 5 by exact (map_natCast PowerSeries.C 5).symm]
  simp only [coeff_C_mul]
  rw [coeff_shift_B n 0 (by omega), coeff_shift_B n 1 (by omega),
    coeff_shift_B n 2 (by omega), coeff_shift_B n 3 (by omega),
    coeff_shift_B n 4 (by omega)]
  simp

end OEISOpen.A371753

#print axioms OEISOpen.A371753.a_eq_coeff
#print axioms OEISOpen.A371753.filtered_coeff
#print axioms OEISOpen.A371753.filtered_five
