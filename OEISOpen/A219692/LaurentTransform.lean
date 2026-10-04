import OEISOpen.A219692.Trinomial
import Mathlib.Algebra.Polynomial.Laurent

/-! Finite Laurent constant-term tools for the binomial transformation P. -/
namespace OEISOpen.A219692

open Finset

theorem coeff_linear_pow {R : Type*} [CommRing R] (a b : R) (N m : ℕ) :
    ((Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial R)^N).coeff m =
      b^(N-m) * (N.choose m : R) * a^m := by
  have h := Polynomial.comp_C_mul_X_coeff
    (p := (Polynomial.X+Polynomial.C b : Polynomial R)^N) (r := a) (n := m)
  simpa [Polynomial.coeff_X_add_C_pow] using h

theorem quadratic_middle_coeff {R : Type*} [CommRing R] (n : ℕ) (a b c : R) :
    ((Polynomial.C b + Polynomial.C c*Polynomial.X +
        Polynomial.C a*Polynomial.X^2 : Polynomial R)^n).coeff n =
      ∑ r ∈ range (n/2+1),
        (n.choose (2*r) : R) * ((2*r).choose r : R) * c^(n-2*r) * (a*b)^r := by
  let f : ℕ → R := fun r => if 2*r ≤ n then
    (n.choose (2*r) : R) * ((2*r).choose r : R) * c^(n-2*r) * (a*b)^r else 0
  have hlarge :
      ((Polynomial.C b + Polynomial.C c*Polynomial.X +
          Polynomial.C a*Polynomial.X^2 : Polynomial R)^n).coeff n =
        ∑ r ∈ range (n+1), f r := by
    rw [show (Polynomial.C b + Polynomial.C c*Polynomial.X +
        Polynomial.C a*Polynomial.X^2 : Polynomial R) =
        Polynomial.C a*Polynomial.X^2 + (Polynomial.C c*Polynomial.X+Polynomial.C b) by ring,
      add_pow, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro r _
    rw [Polynomial.coeff_mul_natCast, mul_pow, ← Polynomial.C_pow, ← pow_mul,
      mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    by_cases hr : 2*r ≤ n
    · rw [ite_eq_left hr, coeff_linear_pow,
        show n-r-(n-2*r) = r by omega]
      simp only [f, ite_eq_left hr, mul_pow]
      have hnat := p1_summand_rearrangement n 0 r (by omega) hr
      simp only [Nat.choose_zero_right, mul_one, one_mul, Nat.sub_zero] at hnat
      have hp := congrArg (fun z : ℕ => (z : R)) hnat
      push_cast at hp
      linear_combination -(a^r * b^r * c^(n-2*r)) * hp
    · simp [f, hr]
  have hcut : (∑ r ∈ range (n/2+1), f r) = ∑ r ∈ range (n+1), f r := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro r _ hr
    have hh : ¬ r < n/2+1 := by simpa only [Finset.mem_range] using hr
    simp [f, show ¬ 2*r ≤ n by omega]
  rw [hlarge, ← hcut]
  apply Finset.sum_congr rfl
  intro r hr
  have hh : 2*r ≤ n := by have := Finset.mem_range.mp hr; omega
  simp only [f, ite_eq_left hh]

theorem shifted_toLaurent_coeff {R : Type*} [CommRing R] (p : Polynomial R) (n : ℕ) :
    (p.toLaurent * LaurentPolynomial.T (-(n : ℤ))).coeff 0 = p.coeff n := by
  rw [LaurentPolynomial.T, AddMonoidAlgebra.coeff_mul_single_apply]
  simp only [neg_neg, zero_add, mul_one, LaurentPolynomial.coeff_toLaurent]
  simpa only [Polynomial.toFinsupp_apply, Nat.castEmbedding_apply] using
    (Finsupp.mapDomain_apply (f := (Nat.castEmbedding : ℕ ↪ ℤ))
      (Nat.castEmbedding : ℕ ↪ ℤ).injective p.toFinsupp.coeff n)

/-- General three-term Laurent constant term, including all finite-support boundaries. -/
theorem laurent_ct_trinomial {R : Type*} [CommRing R]
    (n : ℕ) (c a b : R) :
    ((LaurentPolynomial.C c +
        LaurentPolynomial.C a * LaurentPolynomial.T 1 +
        LaurentPolynomial.C b * LaurentPolynomial.T (-1))^n).coeff 0 =
      ∑ r ∈ range (n/2+1),
        (n.choose (2*r) : R) * ((2*r).choose r : R) *
          c^(n-2*r) * (a*b)^r := by
  let p : Polynomial R := Polynomial.C b + Polynomial.C c*Polynomial.X +
    Polynomial.C a*Polynomial.X^2
  have hbase : LaurentPolynomial.C c +
      LaurentPolynomial.C a * LaurentPolynomial.T 1 +
      LaurentPolynomial.C b * LaurentPolynomial.T (-1) =
        p.toLaurent * LaurentPolynomial.T (-1) := by
    dsimp [p]
    simp only [map_add, map_mul, Polynomial.toLaurent_C,
      Polynomial.toLaurent_X_pow, Polynomial.toLaurent_X, add_mul,
      LaurentPolynomial.mul_T_assoc]
    norm_num
    ring
  rw [hbase, mul_pow, LaurentPolynomial.T_pow]
  simp only [mul_neg_one]
  rw [← map_pow, shifted_toLaurent_coeff]
  exact quadratic_middle_coeff n a b c

end OEISOpen.A219692
