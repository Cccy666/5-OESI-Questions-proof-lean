import OEISOpen.A150500.Hypergeometric
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Formal ingredients of the binomial transform, with its full coefficient
support and the odd/even central-binomial square decomposition. The auxiliary
finite sum in this file is not redefined to be the original walk count. -/
namespace OEISOpen.A150500
open PowerSeries

noncomputable def geometricSeries : PowerSeries ℚ := PowerSeries.mk 1

@[simp] theorem coeff_geometricSeries (n : ℕ) :
    coeff n geometricSeries = 1 := coeff_mk _ _

theorem geometricSeries_pow (m : ℕ) :
    geometricSeries^(m+1) =
      PowerSeries.mk (fun n => (Nat.choose (m+n) m : ℚ)) :=
  mk_one_pow_eq_mk_choose_add ℚ m

/-- The kernel of the binomial transform, including its zero support. -/
theorem coeff_binomial_kernel (n m : ℕ) :
    coeff n (X^m * geometricSeries^(m+1)) = (Nat.choose n m : ℚ) := by
  rw [coeff_X_pow_mul']
  split_ifs with h
  · rw [geometricSeries_pow, coeff_mk]
    congr 2
    omega
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    rfl

def meanderSquare (n : ℕ) : ℚ := (Nat.choose n (n/2) : ℚ)^2

noncomputable def meanderSquareSeries : PowerSeries ℚ :=
  PowerSeries.mk meanderSquare

@[simp] theorem coeff_meanderSquareSeries (n : ℕ) :
    coeff n meanderSquareSeries = meanderSquare n := coeff_mk _ _

theorem meanderSquare_even (k : ℕ) :
    meanderSquare (2*k) = (Nat.centralBinom k : ℚ)^2 := by
  simp [meanderSquare, Nat.centralBinom]

theorem centralBinom_succ_eq_twice_odd (k : ℕ) :
    Nat.centralBinom (k+1) = 2 * Nat.choose (2*k+1) k := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  rw [show 2*(k+1) = (2*k+1)+1 by omega, Nat.choose_succ_succ',
    Nat.choose_symm_half]
  omega

theorem meanderSquare_odd (k : ℕ) :
    4 * meanderSquare (2*k+1) = (Nat.centralBinom (k+1) : ℚ)^2 := by
  have h : (2*k+1)/2 = k := by omega
  simp only [meanderSquare, h, centralBinom_succ_eq_twice_odd, Nat.cast_mul,
    Nat.cast_ofNat]
  ring

@[simp] theorem coeff_even_centralSquare_subst (k : ℕ) :
    coeff (2*k) (centralSquareSeries.subst (X^2 : PowerSeries ℚ)) =
      (Nat.centralBinom k : ℚ)^2 := by
  rw [coeff_subst_X_pow (by decide : (2:ℕ) ≠ 0)]
  simp

@[simp] theorem coeff_odd_centralSquare_subst (k : ℕ) :
    coeff (2*k+1) (centralSquareSeries.subst (X^2 : PowerSeries ℚ)) = 0 := by
  rw [coeff_subst_X_pow (by decide : (2:ℕ) ≠ 0)]
  simp [show ¬ 2 ∣ 2*k+1 by omega]

/-- The parity decomposition B8 in its form with no negative powers. -/
theorem meanderSquareSeries_bridge :
    C 4 * X * meanderSquareSeries =
      (1+C 4*X) * centralSquareSeries.subst (X^2 : PowerSeries ℚ) - 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul,
      coeff_succ_X_mul, coeff_meanderSquareSeries, coeff_one,
      Nat.succ_ne_zero, ↓reduceIte, sub_zero]
    have hpar : n = 2*(n/2) ∨ n = 2*(n/2)+1 := by omega
    rcases hpar with h | h
    · rw [h]
      simp [meanderSquare_even]
    · rw [h]
      rw [show 2*(n/2)+1+1 = 2*(n/2+1) by omega]
      simp [meanderSquare_odd]

def aSum (n : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (n+1), (Nat.choose n m : ℚ) * meanderSquare m

noncomputable def aSumSeries : PowerSeries ℚ := PowerSeries.mk aSum

theorem geometric_argument_hasSubst :
    HasSubst (X*geometricSeries : PowerSeries ℚ) := by
  apply HasSubst.of_constantCoeff_zero'
  simp

/-- A coefficientwise proof of the binomial-transform generating function.
Every exchange below is between a finite antidiagonal sum and a finitely
supported coefficient sum. -/
theorem coeff_binomial_transform (F : PowerSeries ℚ) (n : ℕ) :
    coeff n (geometricSeries * F.subst (X*geometricSeries)) =
      ∑ m ∈ Finset.range (n+1), (Nat.choose n m : ℚ) * coeff m F := by
  have ht (m : ℕ) :
      (∑ p ∈ Finset.antidiagonal n,
        coeff p.2 ((X*geometricSeries)^m)) = (Nat.choose n m : ℚ) := by
    calc
      _ = coeff n (geometricSeries * (X*geometricSeries)^m) := by
        rw [coeff_mul]
        simp
      _ = coeff n (X^m * geometricSeries^(m+1)) := by
        congr 1
        rw [mul_pow, pow_succ]
        ring
      _ = _ := coeff_binomial_kernel n m
  rw [coeff_mul]
  simp_rw [coeff_geometricSeries, one_mul,
    coeff_subst' geometric_argument_hasSubst, smul_eq_mul]
  rw [sum_finsum_comm _ _ (fun p _ => by
    simpa only [smul_eq_mul] using
      coeff_subst_finite' geometric_argument_hasSubst F p.2)]
  simp_rw [← Finset.mul_sum, ht]
  rw [finsum_eq_finsetSum_of_support_subset _ (s := Finset.range (n+1))]
  · apply Finset.sum_congr rfl
    intro m hm
    ring
  · intro m hm
    simp only [Function.mem_support] at hm
    have hmn : m ≤ n := by
      by_contra h
      apply hm
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
    simpa only [Finset.mem_coe, Finset.mem_range] using Nat.lt_succ_of_le hmn

theorem aSumSeries_eq_binomial_transform :
    aSumSeries = geometricSeries *
      meanderSquareSeries.subst (X*geometricSeries) := by
  ext n
  rw [coeff_binomial_transform]
  simp [aSumSeries, aSum]

theorem geometricSeries_eq_inverse :
    geometricSeries = (1-X : PowerSeries ℚ)⁻¹ := by
  symm
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by simp)).mpr
  exact mk_one_mul_one_sub_eq_one ℚ

/-- The complete generating-function bridge for the explicit finite sum.
The separate combinatorial theorem identifying aSum with walk counts is not
assumed or asserted here. -/
theorem aSumSeries_bridge :
    1+4*X*aSumSeries = (1+3*X)*geometricSeries *
      centralSquareSeries.subst (X^2*geometricSeries^2) := by
  have hb := meanderSquareSeries_bridge
  norm_num only [map_ofNat] at hb
  have h := congrArg (substAlgHom geometric_argument_hasSubst) hb
  simp only [map_mul, map_add, map_sub, map_one, map_ofNat, substAlgHom_X] at h
  have hcomp :
      substAlgHom geometric_argument_hasSubst
          (centralSquareSeries.subst (X^2 : PowerSeries ℚ)) =
        centralSquareSeries.subst (X^2*geometricSeries^2) := by
    rw [coe_substAlgHom, subst_comp_subst_apply
      (HasSubst.X_pow (by decide : (2:ℕ) ≠ 0)) geometric_argument_hasSubst,
      subst_pow geometric_argument_hasSubst, subst_X geometric_argument_hasSubst,
      mul_pow]
  rw [hcomp, coe_substAlgHom] at h
  have hg : geometricSeries*(1-X) = (1 : PowerSeries ℚ) :=
    mk_one_mul_one_sub_eq_one ℚ
  have hf : (1+4*X*geometricSeries : PowerSeries ℚ) =
      (1+3*X)*geometricSeries := by
    linear_combination -hg
  rw [← mul_assoc, hf] at h
  rw [aSumSeries_eq_binomial_transform]
  linear_combination h

end OEISOpen.A150500
