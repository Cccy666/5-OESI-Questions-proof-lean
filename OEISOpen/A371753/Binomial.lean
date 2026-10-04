import OEISOpen.A371753.Certificates
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OEISOpen.A371753

def binom (N K : ℕ) : ℚ := Nat.choose N K

theorem binom_step (N K : ℕ) (hN : 1 ≤ N) (hK : 1 ≤ K) :
    (N : ℚ) * binom (N - 1) (K - 1) = (K : ℚ) * binom N K := by
  have h := Nat.add_one_mul_choose_eq (N - 1) (K - 1)
  rw [Nat.sub_add_cancel hN, Nat.sub_add_cancel hK] at h
  unfold binom
  exact_mod_cast h.trans (Nat.mul_comm _ _)

/-- Algebraic assembly of the four adjacent-binomial cross products. -/
theorem five_collapse_of_steps (n b0 b1 b2 b3 b4 : ℚ) (hn : n ≠ 0)
    (h1 : (5 * n) * b1 = n * b0)
    (h2 : (5 * n - 1) * b2 = (n - 1) * b1)
    (h3 : (5 * n - 2) * b3 = (n - 2) * b2)
    (h4 : (5 * n - 3) * b4 = (n - 3) * b3) :
    5 * (5 * n - 1) * (5 * n - 2) * (5 * n - 3) *
        (16 * b0 - 15 * b1 + 11 * b2 - 5 * b3 + b4) = 8 * F n * b0 := by
  apply mul_left_cancel₀ hn
  linear_combination
    ((-15 * (5 * n - 1) * (5 * n - 2) * (5 * n - 3) +
      11 * (n - 1) * (5 * n - 2) * (5 * n - 3) -
      5 * (n - 1) * (n - 2) * (5 * n - 3) +
      (n - 1) * (n - 2) * (n - 3))) * h1 +
    ((11 * (5 * n) * (5 * n - 2) * (5 * n - 3) -
      5 * (5 * n) * (n - 2) * (5 * n - 3) +
      (5 * n) * (n - 2) * (n - 3))) * h2 +
    ((-5 * (5 * n) * (5 * n - 1) * (5 * n - 3) +
      (5 * n) * (5 * n - 1) * (n - 3))) * h3 +
    ((5 * n) * (5 * n - 1) * (5 * n - 2)) * h4 +
    b0 * five_ratio_cleared n

theorem five_binomial_collapse (n : ℕ) (hn : 4 ≤ n) :
    5 * (5 * (n : ℚ) - 1) * (5 * (n : ℚ) - 2) * (5 * (n : ℚ) - 3) *
        (16 * binom (5 * n) n - 15 * binom (5 * n - 1) (n - 1) +
          11 * binom (5 * n - 2) (n - 2) - 5 * binom (5 * n - 3) (n - 3) +
          binom (5 * n - 4) (n - 4)) = 8 * F n * binom (5 * n) n := by
  have h1 := binom_step (5 * n) n (by omega) (by omega)
  have h2 := binom_step (5 * n - 1) (n - 1) (by omega) (by omega)
  have h3 := binom_step (5 * n - 2) (n - 2) (by omega) (by omega)
  have h4 := binom_step (5 * n - 3) (n - 3) (by omega) (by omega)
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  apply five_collapse_of_steps _ _ _ _ _ _ hnq
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using h1
  · simpa only [Nat.sub_sub, Nat.cast_sub (by omega : 1 ≤ 5 * n),
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h2
  · simpa only [Nat.sub_sub, Nat.cast_sub (by omega : 2 ≤ 5 * n),
      Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_mul, Nat.cast_ofNat] using h3
  · simpa only [Nat.sub_sub, Nat.cast_sub (by omega : 3 ≤ 5 * n),
      Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_mul, Nat.cast_ofNat] using h4

end OEISOpen.A371753

#print axioms OEISOpen.A371753.five_binomial_collapse
