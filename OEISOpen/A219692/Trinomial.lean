import OEISOpen.A219692.BinomialTransform
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! The general trinomial coefficient expansion and the finite identity P1. -/
namespace OEISOpen.A219692

open Finset Polynomial

theorem coeff_one_add_two_X_pow (N m : ℕ) :
    ((1 + 2*X : Polynomial ℚ)^N).coeff m = (N.choose m : ℚ)*2^m := by
  have h := Polynomial.comp_C_mul_X_coeff
    (p := (1+X : Polynomial ℚ)^N) (r := (2 : ℚ)) (n := m)
  simpa [Polynomial.coeff_one_add_X_pow, Polynomial.C_ofNat] using h

/-- The coefficient of an arbitrary power of 1+2X+X², with its full finite support. -/
theorem trinomial_coefficient_expanded (N m : ℕ) (hm : m ≤ N) :
    ((1 + 2*X + X^2 : Polynomial ℚ)^N).coeff m =
      ∑ r ∈ range (m/2+1),
        (N.choose r : ℚ) * ((N-r).choose (m-2*r) : ℚ) * 2^(m-2*r) := by
  let f : ℕ → ℚ := fun r => if 2*r ≤ m then
    (N.choose r : ℚ) * ((N-r).choose (m-2*r) : ℚ) * 2^(m-2*r) else 0
  have hlarge : ((1 + 2*X + X^2 : Polynomial ℚ)^N).coeff m =
      ∑ r ∈ range (N+1), f r := by
    rw [show (1 + 2*X + X^2 : Polynomial ℚ) = X^2+(1+2*X) by ring,
      add_pow, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro r _
    rw [Polynomial.coeff_mul_natCast, ← pow_mul, Polynomial.coeff_X_pow_mul']
    by_cases hr : 2*r ≤ m
    · rw [ite_eq_left hr, coeff_one_add_two_X_pow]
      simp only [f, ite_eq_left hr]
      ring
    · simp [f, hr]
  have hcut : (∑ r ∈ range (m/2+1), f r) = ∑ r ∈ range (N+1), f r := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro r _ hr
    have hh : ¬ r < m/2+1 := by simpa only [Finset.mem_range] using hr
    simp [f, show ¬ 2*r ≤ m by omega]
  rw [hlarge, ← hcut]
  apply Finset.sum_congr rfl
  intro r hr
  have hh : 2*r ≤ m := by have := Finset.mem_range.mp hr; omega
  simp only [f, ite_eq_left hh]

/-- P1 as a general natural-number identity; no factorials or division are used. -/
theorem p1 (n k : ℕ) (hk : 2*k ≤ n) :
    (∑ ell ∈ Icc k (n/2),
      n.choose (2*ell) * (2*ell).choose ell * ell.choose k * 2^(n-2*ell)) =
      n.choose k * (2*n-2*k).choose n := by
  have hcoeff := trinomial_coefficient_expanded (n-k) (n-2*k) (by omega)
  rw [trinomial_coefficient_closed n k hk] at hcoeff
  have hq :
      (∑ ell ∈ Icc k (n/2),
        (n.choose (2*ell) : ℚ) * ((2*ell).choose ell : ℚ) *
          (ell.choose k : ℚ) * (2 : ℚ)^(n-2*ell)) =
      (n.choose k : ℚ) * ((2*n-2*k).choose n : ℚ) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    rw [show n/2+1-k = (n-2*k)/2+1 by omega]
    calc
      _ = ∑ r ∈ range ((n-2*k)/2+1),
          (n.choose k : ℚ) * ((n-k).choose r : ℚ) *
            ((n-k-r).choose (n-2*k-2*r) : ℚ) * (2 : ℚ)^(n-2*k-2*r) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hh : 2*(k+r) ≤ n := by have := Finset.mem_range.mp hr; omega
        have he1 : k+r-k = r := by omega
        have he2 : n-(k+r) = n-k-r := by omega
        have he3 : n-2*(k+r) = n-2*k-2*r := by omega
        have hp := congrArg (fun z : ℕ => (z : ℚ))
          (p1_summand_rearrangement n k (k+r) (by omega) hh)
        push_cast at hp
        rw [he1, he2, he3] at hp
        rw [he3]
        linear_combination (2 : ℚ)^(n-2*k-2*r)*hp
      _ = (n.choose k : ℚ) *
          (∑ r ∈ range ((n-2*k)/2+1),
            ((n-k).choose r : ℚ) * ((n-k-r).choose (n-2*k-2*r) : ℚ) *
              (2 : ℚ)^(n-2*k-2*r)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = _ := by rw [← hcoeff]
  exact_mod_cast hq

end OEISOpen.A219692
