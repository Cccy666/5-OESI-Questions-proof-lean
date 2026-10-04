import OEISOpen.A219692.PolynomialTransform
import OEISOpen.A219692.TransformSum

/-! Completion of the general finite binomial transformation P. -/
namespace OEISOpen.A219692

open Finset LaurentPolynomial

noncomputable section

def transformSummand {R : Type*} [CommRing R] (n : ℕ) (A B : R) (ell k : ℕ) : R :=
  ((-1 : R)^k * ((2*k).choose k : R) * (A*B)^k * (A+B)^(n-2*k)) *
    ((n.choose (2*ell) : R) * ((2*ell).choose ell : R) *
      (ell.choose k : R) * (2 : R)^(n-2*ell))

theorem rotated_row_ct {R : Type*} [CommRing R] (n ell : ℕ) (hell : 2*ell ≤ n) (A B : R) :
    laurentCT ((n.choose (2*ell) : LaurentPolynomial R) * ((2*ell).choose ell : LaurentPolynomial R) *
      C (2*(A+B))^(n-2*ell) *
        ((C A*T 1+C B*T (-1))*(C A*T (-1)+C B*T 1))^ell) =
      ∑ k ∈ range (ell+1), transformSummand n A B ell k := by
  let W : R := (n.choose (2*ell) : R) * ((2*ell).choose ell : R) * (2*(A+B))^(n-2*ell)
  let D : LaurentPolynomial R := T 1-T (-1)
  have hfactor :
      (n.choose (2*ell) : LaurentPolynomial R) * ((2*ell).choose ell : LaurentPolynomial R) *
        C (2*(A+B))^(n-2*ell) *
          ((C A*T 1+C B*T (-1))*(C A*T (-1)+C B*T 1))^ell =
      C W * (C (A*B)*D^2+C ((A+B)^2))^ell := by
    rw [mixed_laurent_product]
    simp only [W, D, map_mul, map_pow, map_natCast]
    ring
  rw [hfactor, add_pow, Finset.mul_sum, laurentCT_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkell : k ≤ ell := by have := Finset.mem_range.mp hk; omega
  have hterm : C W * ((C (A*B)*D^2)^k * C ((A+B)^2)^(ell-k) *
      (ell.choose k : LaurentPolynomial R)) =
      C (W*(A*B)^k*(A+B)^(2*(ell-k))*(ell.choose k : R))*D^(2*k) := by
    simp only [map_mul, map_pow, map_natCast, mul_pow, pow_mul]
    ring
  rw [hterm, laurentCT_C_mul,
    show laurentCT (D^(2*k)) = (-1 : R)^k*((2*k).choose k : R) from
      laurent_ct_antisymmetric_even k]
  dsimp only [W, transformSummand]
  rw [show (2*(A+B))^(n-2*ell) = (2 : R)^(n-2*ell)*(A+B)^(n-2*ell) by rw [mul_pow]]
  have hpow : (A+B)^(n-2*ell)*(A+B)^(2*(ell-k)) = (A+B)^(n-2*k) := by
    rw [← pow_add, show n-2*ell+2*(ell-k) = n-2*k by omega]
  linear_combination (n.choose (2*ell) : R) * ((2*ell).choose ell : R) *
    (2 : R)^(n-2*ell) * (A*B)^k * (ell.choose k : R) *
      (-1 : R)^k * ((2*k).choose k : R) * hpow

theorem rotatedKernel_ct_double_sum {R : Type*} [CommRing R] (n : ℕ) (A B : R) :
    laurentCT (laurentCT ((rotatedKernel A B)^n)) =
      ∑ ell ∈ range (n/2+1), ∑ k ∈ range (ell+1), transformSummand n A B ell k := by
  have houter : laurentCT ((rotatedKernel A B)^n) =
      ∑ ell ∈ range (n/2+1),
        (n.choose (2*ell) : LaurentPolynomial R) * ((2*ell).choose ell : LaurentPolynomial R) *
          C (2*(A+B))^(n-2*ell) *
            ((C A*T 1+C B*T (-1))*(C A*T (-1)+C B*T 1))^ell :=
    laurent_ct_trinomial n (C (2*(A+B))) (C A*T 1+C B*T (-1)) (C A*T (-1)+C B*T 1)
  rw [houter, laurentCT_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  exact rotated_row_ct n ell (by have := Finset.mem_range.mp hell; omega) A B

theorem transform_double_sum {R : Type*} [CommRing R] (n : ℕ) (A B : R) :
    (∑ ell ∈ range (n/2+1), ∑ k ∈ range (ell+1), transformSummand n A B ell k) =
      ∑ k ∈ range (n/2+1),
        (-1 : R)^k * ((2*k).choose k : R) * ((2*(n-k)).choose (n-k) : R) *
          ((n-k).choose k : R) * (A*B)^k * (A+B)^(n-2*k) := by
  have hrect :
      (∑ ell ∈ range (n/2+1), ∑ k ∈ range (ell+1), transformSummand n A B ell k) =
      ∑ ell ∈ range (n/2+1), ∑ k ∈ range (n/2+1), transformSummand n A B ell k := by
    apply Finset.sum_congr rfl
    intro ell hell
    have hellN : ell ≤ n/2 := by have := Finset.mem_range.mp hell; omega
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k _ hk
    have hlt : ell < k := by
      have hh : ¬ k < ell+1 := by simpa only [Finset.mem_range] using hk
      omega
    simp [transformSummand, Nat.choose_eq_zero_of_lt hlt]
  rw [hrect, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hk2 : 2*k ≤ n := by have := Finset.mem_range.mp hk; omega
  have hc := congrArg (fun z : ℕ => (z : R)) (p1_range_central n k hk2)
  push_cast at hc
  calc
    _ = ((-1 : R)^k * ((2*k).choose k : R) * (A*B)^k * (A+B)^(n-2*k)) *
        (∑ ell ∈ range (n/2+1),
          (n.choose (2*ell) : R) * ((2*ell).choose ell : R) *
            (ell.choose k : R) * (2 : R)^(n-2*ell)) := by
      simp only [transformSummand, Finset.mul_sum]
    _ = _ := by rw [hc]; ring

/-- P: the general two-variable central-binomial transformation in any commutative ring. -/
theorem central_binomial_transform {R : Type*} [CommRing R] (n : ℕ) (A B : R) :
    (∑ j ∈ range (n+1),
      (n.choose j : R) * ((2*j).choose j : R) *
        ((2*(n-j)).choose (n-j) : R) * A^(n-j) * B^j) =
    ∑ k ∈ range (n/2+1),
      (-1 : R)^k * ((2*k).choose k : R) * ((2*(n-k)).choose (n-k) : R) *
        ((n-k).choose k : R) * (A*B)^k * (A+B)^(n-2*k) := by
  rw [← separatedKernel_ct, ← rotatedKernel_ct_eq_separated,
    rotatedKernel_ct_double_sum, transform_double_sum]

end

end OEISOpen.A219692
