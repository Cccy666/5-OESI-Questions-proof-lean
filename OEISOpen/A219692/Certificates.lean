import OEISOpen.A219692.Definitions

/-!
The small polynomial certificate is unconditional. Its application to `S`
still requires the three shift identities. This module does not assert T1,
T2, Bridge, or the unconditional local telescoping theorem.
-/

namespace OEISOpen.A219692

def R (n j : ℚ) : ℚ := -9 * (4*n-3) * j^3 / (2*n-2*j-1)
def G (n j : ℕ) : ℚ := R n j * (S n j : ℚ)

@[simp] theorem G_zero (n : ℕ) : G n 0 = 0 := by simp [G, R]

theorem G_eq_zero_of_unsupported {n j : ℕ} (h : n < 3*j) : G n j = 0 := by
  simp [G, S_eq_zero_of_unsupported h]

theorem G_at_upper_endpoint (n : ℕ) : G n (n / 3 + 1) = 0 := by
  simp [G, S_at_upper_endpoint]

theorem odd_denominator_int_ne_zero (n j : ℤ) : 2*n-2*j-1 ≠ 0 := by omega

theorem first_denominator_ne_zero (n j : ℕ) :
    (2*(n : ℚ)-2*(j : ℚ)-1) ≠ 0 := by
  exact_mod_cast odd_denominator_int_ne_zero n j

theorem second_denominator_ne_zero (n j : ℕ) :
    (2*(n : ℚ)-2*(j : ℚ)-3) ≠ 0 := by
  have h : (2*(n : ℤ)-2*(j : ℤ)-3) ≠ 0 := by omega
  exact_mod_cast h

/-- Tel divided by S, multiplied by 3(2n-2j-1)(2n-2j-3). -/
theorem cleared_telescoping_certificate (n j : ℚ) :
    3*(2*n-2*j-1)*(2*n-2*j-3)*n^3
    - (2*n-1)*(7*n^2-7*n+3)*(n-3*j)*(2*n-2*j-3)
    + (4*n-5)*(n-1)*(4*n-3)*(n-3*j)*(n-3*j-1)
    = -(4*n-3)*(2*j+1)*(n-3*j)*(n-3*j-1)*(n-3*j-2)
      + 27*(4*n-3)*j^3*(2*n-2*j-3) := by ring

/-- The rational local certificate. Both denominator hypotheses are explicit. -/
theorem rational_telescoping_certificate (n j : ℚ)
    (h1 : 2*n-2*j-1 ≠ 0) (h2 : 2*n-2*j-3 ≠ 0) :
    n^3
    - 2*(2*n-1)*(7*n^2-7*n+3) * ((n-3*j)/(6*(2*n-2*j-1)))
    + 12*(4*n-5)*(n-1)*(4*n-3) *
      ((n-3*j)*(n-3*j-1)/(36*(2*n-2*j-1)*(2*n-2*j-3)))
    = -(4*n-3)*(2*j+1)*(n-3*j)*(n-3*j-1)*(n-3*j-2) /
        (3*(2*n-2*j-1)*(2*n-2*j-3))
      + 9*(4*n-3)*j^3/(2*n-2*j-1) := by
  have h1' : 2*(n-j)-1 ≠ 0 := by intro h; apply h1; linarith
  have h2' : 2*(n-j)-3 ≠ 0 := by intro h; apply h2; linarith
  field_simp [h1', h2']
  ring

/-- Applying the certificate requires only crossed shift identities, never division by a term. -/
theorem local_certificate_of_crossed_shifts (n j x0 x1 x2 y : ℚ)
    (h1 : 2*n-2*j-1 ≠ 0) (h2 : 2*n-2*j-3 ≠ 0)
    (shift1 : 6*(2*n-2*j-1)*x1 = (n-3*j)*x0)
    (shift2 : 36*(2*n-2*j-1)*(2*n-2*j-3)*x2 = (n-3*j)*(n-3*j-1)*x0)
    (shiftJ : 27*(j+1)^3*(2*n-2*j-1)*y =
      (2*j+1)*(n-3*j)*(n-3*j-1)*(n-3*j-2)*x0) :
    n^3*x0 - 2*(2*n-1)*(7*n^2-7*n+3)*x1 +
      12*(4*n-5)*(n-1)*(4*n-3)*x2 = R n (j+1)*y - R n j*x0 := by
  have h1' : 2*(n-j)-1 ≠ 0 := by intro h; apply h1; linarith
  have h2' : 2*(n-j)-3 ≠ 0 := by intro h; apply h2; linarith
  have hx1 : x1 = (n-3*j)/(6*(2*n-2*j-1))*x0 := by
    apply (mul_left_cancel₀ (show 6*(2*n-2*j-1) ≠ 0 from mul_ne_zero (by norm_num) h1))
    rw [shift1]
    field_simp [h1', h2']
  have hx2 : x2 = (n-3*j)*(n-3*j-1)/(36*(2*n-2*j-1)*(2*n-2*j-3))*x0 := by
    apply (mul_left_cancel₀ (show 36*(2*n-2*j-1)*(2*n-2*j-3) ≠ 0 from mul_ne_zero (mul_ne_zero (by norm_num) h1) h2))
    rw [shift2]
    field_simp [h1', h2']
  have hy : R n (j+1)*y =
      -(4*n-3)*(2*j+1)*(n-3*j)*(n-3*j-1)*(n-3*j-2) /
        (3*(2*n-2*j-1)*(2*n-2*j-3))*x0 := by
    have he : 2*n-2*(j+1)-1 = 2*n-2*j-3 := by ring
    simp only [R, he]
    field_simp [h1', h2']
    linear_combination - (4*n-3) * shiftJ
  rw [hx1, hx2, hy]
  have hc := congrArg (fun z : ℚ => z*x0) (rational_telescoping_certificate n j h1 h2)
  unfold R
  linear_combination hc

end OEISOpen.A219692



