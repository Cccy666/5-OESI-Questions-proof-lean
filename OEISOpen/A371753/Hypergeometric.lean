import OEISOpen.A371753.Certificates
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
The binomial shift needed by Route A, proved without division or factorial
quotients. Four elementary shifts of the upper binomial index are followed by
one simultaneous shift of both indices. All sequence indices remain natural;
polynomial factors are rational.
-/

namespace OEISOpen.A371753

private theorem choose_top_step (m r : ℕ) :
    (Nat.choose (5 * m + r) m : ℚ) * (5 * (m : ℚ) + r + 1) =
      (Nat.choose (5 * m + r + 1) m : ℚ) * (4 * (m : ℚ) + r + 1) := by
  have h := Nat.choose_mul_succ_eq (5 * m + r) m
  have he : 5 * m + r + 1 - m = 4 * m + r + 1 := by omega
  rw [he] at h
  exact_mod_cast h

theorem binomial_five_step (m : ℕ) :
    ((m : ℚ) + 1) * (4 * m + 4) * (4 * m + 3) * (4 * m + 2) * (4 * m + 1) *
        (Nat.choose (5 * m + 5) (m + 1) : ℚ) =
      (5 * (m : ℚ) + 5) * (5 * m + 4) * (5 * m + 3) * (5 * m + 2) * (5 * m + 1) *
        (Nat.choose (5 * m) m : ℚ) := by
  have h0 := choose_top_step m 0
  have h1 := choose_top_step m 1
  have h2 := choose_top_step m 2
  have h3 := choose_top_step m 3
  norm_num at h0 h1 h2 h3
  have h4 : (5 * (m : ℚ) + 5) * (Nat.choose (5 * m + 4) m : ℚ) =
      (Nat.choose (5 * m + 5) (m + 1) : ℚ) * ((m : ℚ) + 1) := by
    have h := Nat.add_one_mul_choose_eq (5 * m + 4) m
    have he : 5 * m + 4 + 1 = 5 * m + 5 := by omega
    rw [he] at h
    exact_mod_cast h
  linear_combination
    -(5 * (m : ℚ) + 5) * (5 * m + 4) * (5 * m + 3) * (5 * m + 2) * h0 -
    (5 * (m : ℚ) + 5) * (5 * m + 4) * (5 * m + 3) * (4 * m + 1) * h1 -
    (5 * (m : ℚ) + 5) * (5 * m + 4) * (4 * m + 2) * (4 * m + 1) * h2 -
    (5 * (m : ℚ) + 5) * (4 * m + 3) * (4 * m + 2) * (4 * m + 1) * h3 -
    (4 * (m : ℚ) + 4) * (4 * m + 3) * (4 * m + 2) * (4 * m + 1) * h4

theorem binomial_shift_cleared (n : ℕ) (hn : 1 ≤ n) :
    (n : ℚ) * (4 * n) * (4 * n - 1) * (4 * n - 2) * (4 * n - 3) *
        (Nat.choose (5 * n) n : ℚ) =
      (5 * (n : ℚ)) * (5 * n - 1) * (5 * n - 2) * (5 * n - 3) * (5 * n - 4) *
        (Nat.choose (5 * (n - 1)) (n - 1) : ℚ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := binomial_five_step m
  rw [show 1 + m - 1 = m by omega]
  rw [show 5 * (1 + m) = 5 * m + 5 by omega]
  rw [show 1 + m = m + 1 by omega]
  push_cast
  convert h using 1 <;> ring

end OEISOpen.A371753

#print axioms OEISOpen.A371753.binomial_five_step
#print axioms OEISOpen.A371753.binomial_shift_cleared
