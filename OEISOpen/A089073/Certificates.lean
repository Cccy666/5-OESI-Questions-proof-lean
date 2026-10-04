import Mathlib.Tactic

/-! Exact ring certificates for A089073. All polynomial subtraction is in ℚ. -/
namespace OEISOpen.A089073

def q (n : ℚ) : ℚ := 23 * n ^ 2 - 162 * n + 199
def r (n : ℚ) : ℚ := 27 * n ^ 2 - 47 * n - 10
def t (n : ℚ) : ℚ := 23 * n ^ 2 - 116 * n + 60

def residual (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  (n : ℚ) * (n + 2) * q n * a n +
    12 * r n * (a (n - 1) - 2 * a (n - 2) + 4 * a (n - 3)) -
    12 * (3 * n - 13) * (3 * n - 5) * t n * a (n - 4)

theorem even_polynomial_certificate (n : ℚ) :
    96 * r n - 12 * (3 * n - 13) * (3 * n - 5) * t n =
      -12 * (3 * n - 10) * (3 * n - 2) * q n := by
  unfold q r t
  ring

theorem odd_polynomial_certificate (n : ℚ) :
    n * (n + 2) * q n + 6 * r n = (n - 1) * (n + 1) * t n := by
  unfold q r t
  ring

/-- L5 after multiplying by `(1 - 6*z*y)^3`; no division hypothesis is needed. -/
theorem ode_cleared_certificate {R : Type*} [CommRing R] (z y : R) :
    z * (1 - 108 * z ^ 2) * (4 * y ^ 3 * (5 - 24 * z * y)) +
      (2 - 324 * z ^ 2) * (2 * y ^ 2) * (1 - 6 * z * y) ^ 2 -
      (60 * z * y + 4) * (1 - 6 * z * y) ^ 3 =
    (4 - 12 * z * y) * (y ^ 2 - 4 * z * y ^ 3 - 1) := by
  ring

/-- Clearing the denominator of B = M/(2-M) in the graph-folding proof. -/
theorem folding_algebra_certificate {R : Type*} [CommRing R] (z m : R) :
    m ^ 2 * (2 - m) - 4 * z * m ^ 3 - (2 - m) ^ 3 =
      -4 * (z * m ^ 3 + m ^ 2 - 3 * m + 2) := by
  ring

theorem q_nonzero (n : ℕ) (hn : 5 ≤ n) : q n ≠ 0 := by
  by_cases h5 : n = 5
  · subst n
    norm_num [q]
  · have hn6 : (6 : ℚ) ≤ n := by exact_mod_cast (show 6 ≤ n by omega)
    have hs : (0 : ℚ) ≤ ((n : ℚ) - 6) ^ 2 := sq_nonneg _
    unfold q
    nlinarith

theorem residual_even_factor (a : ℕ → ℚ) (n : ℕ)
    (h : a (n - 1) - 2 * a (n - 2) + 4 * a (n - 3) = 8 * a (n - 4)) :
    residual a n = q n * ((n : ℚ) * (n + 2) * a n -
      12 * (3 * n - 10) * (3 * n - 2) * a (n - 4)) := by
  unfold residual
  rw [h]
  unfold q r t
  ring

theorem residual_odd_factor (a : ℕ → ℚ) (n : ℕ)
    (h : a (n - 1) - 2 * a (n - 2) + 4 * a (n - 3) = a n / 2) :
    residual a n = t n * (((n : ℚ) - 1) * (n + 1) * a n -
      12 * (3 * n - 13) * (3 * n - 5) * a (n - 4)) := by
  unfold residual
  rw [h]
  unfold q r t
  ring

end OEISOpen.A089073
