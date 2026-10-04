import OEISOpen.A219692.Bridge

/-!
Algebraic specialization of the right side of P. This module does not assume or
prove P. It connects its exact finite right-hand sum to `bridgePolynomial`.
-/
namespace OEISOpen.A219692

theorem specialization_sum {R : Type*} [CommRing R] (x : R) :
    (1+x)^3 + -(x^3) = 1 + 3*(x*(1+x)) := by ring

theorem specialization_product {R : Type*} [CommRing R] (x : R) :
    (1+x)^3 * -(x^3) = -((x*(1+x))^3) := by ring

/-- The two signs cancel before any coefficient or finite-sum argument. -/
theorem specialization_term {R : Type*} [CommRing R] (x c : R) (n k : ℕ) :
    (-1 : R)^k * c * ((1+x)^3 * -(x^3))^k *
        ((1+x)^3 + -(x^3))^(n-2*k) =
      c * (x*(1+x))^(3*k) * (1+3*(x*(1+x)))^(n-2*k) := by
  rw [specialization_sum, specialization_product]
  have hsign : (-1 : R)^k * (-((x*(1+x))^3))^k = (x*(1+x))^(3*k) := by
    rw [← mul_pow]
    simp only [neg_one_mul, neg_neg, ← pow_mul]
  calc
    _ = c * ((-1 : R)^k * (-((x*(1+x))^3))^k) *
        (1+3*(x*(1+x)))^(n-2*k) := by ring
    _ = _ := by rw [hsign]

/-- The left side expected by general P is the already defined convolution. -/
theorem convolution_eq_binomial_sum (n : ℕ) (A B : PowerSeries ℚ) :
    convolution n A B =
      ∑ j ∈ Finset.range (n+1),
        (n.choose j : PowerSeries ℚ) * ((2*j).choose j : PowerSeries ℚ) *
          ((2*(n-j)).choose (n-j) : PowerSeries ℚ) * A^(n-j) * B^j := by
  unfold convolution
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  rw [show 2*n-2*j = 2*(n-j) by omega]
  simp only [map_mul, map_natCast]

/-- P's finite right side at A=(1+X)^3, B=-X^3 is exactly the evaluation of Q_n.
This is unconditional, includes n=0, and does not invoke P itself. -/
theorem specialized_transform_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n/2+1),
      (-1 : PowerSeries ℚ)^k * ((2*k).choose k : PowerSeries ℚ) *
        ((2*(n-k)).choose (n-k) : PowerSeries ℚ) *
        ((n-k).choose k : PowerSeries ℚ) *
        (((1+PowerSeries.X)^3 : PowerSeries ℚ) * -(PowerSeries.X^3))^k *
        (((1+PowerSeries.X)^3 : PowerSeries ℚ) + -(PowerSeries.X^3))^(n-2*k)) =
      Polynomial.aeval (PowerSeries.X*(1+PowerSeries.X) : PowerSeries ℚ)
        (bridgePolynomial n) := by
  unfold bridgePolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [show 2*(n-k) = 2*n-2*k by omega]
  simp only [map_mul, map_pow, map_add, map_one, map_ofNat,
    Polynomial.aeval_C, Polynomial.aeval_X, PowerSeries.algebraMap_eq,
    map_mul, map_natCast]
  simpa only [mul_assoc] using
    (specialization_term (PowerSeries.X : PowerSeries ℚ)
      (((2*k).choose k : PowerSeries ℚ) * ((2*n-2*k).choose (n-k) : PowerSeries ℚ) *
        ((n-k).choose k : PowerSeries ℚ)) n k)

end OEISOpen.A219692
