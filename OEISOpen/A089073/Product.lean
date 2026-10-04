import Mathlib.RingTheory.Binomial
import Mathlib.Tactic

/-!
# A089073: the finite-product normalization

The definitions in this file are rational-valued explicit formulas. No graph
enumeration is encoded or assumed here.
-/

namespace OEISOpen.A089073

def P (k : ℕ) : ℚ := ∏ j ∈ Finset.range k, ((k : ℚ) + 1 + 2 * j)

def b (k : ℕ) : ℚ := 2 ^ k * P k / (Nat.factorial (k + 1) : ℚ)

theorem P_step_two (k : ℕ) :
    ((k : ℚ) + 1) * P (k + 2) =
      (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 3) * (3 * (k : ℚ) + 5) * P k := by
  let f : ℕ → ℚ := fun j => (k : ℚ) + 1 + 2 * j
  have hs : (∏ j ∈ Finset.range (k + 2), f (j + 1)) = P (k + 2) := by
    apply Finset.prod_congr rfl
    intro j hj
    dsimp [f]
    push_cast
    ring
  calc
    ((k : ℚ) + 1) * P (k + 2) = ∏ j ∈ Finset.range (k + 3), f j := by
      rw [show k + 3 = (k + 2) + 1 by omega, Finset.prod_range_succ', hs]
      dsimp [f]
      ring
    _ = (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 3) *
        (3 * (k : ℚ) + 5) * P k := by
      rw [show k + 3 = (k + 1 + 1) + 1 by omega]
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
      change P k * f k * f (k + 1) * f (k + 1 + 1) = _
      dsimp [f]
      push_cast
      ring

@[simp] theorem b_zero : b 0 = 1 := by norm_num [b, P]

@[simp] theorem b_one : b 1 = 2 := by norm_num [b, P]

theorem b_step_two (k : ℕ) :
    ((k : ℚ) + 2) * ((k : ℚ) + 3) * b (k + 2) =
      12 * (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 5) * b k := by
  have hfac : (Nat.factorial (k + 2 + 1) : ℚ) =
      ((k : ℚ) + 3) * ((k : ℚ) + 2) * (Nat.factorial (k + 1) : ℚ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hn : (Nat.factorial (k + 1) : ℚ) ≠ 0 := by positivity
  have hk : (k : ℚ) + 1 ≠ 0 := by positivity
  have hk2 : (k : ℚ) + 2 ≠ 0 := by positivity
  have hk3 : (k : ℚ) + 3 ≠ 0 := by positivity
  have hP : P (k + 2) = 3 * (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 5) * P k := by
    apply mul_left_cancel₀ hk
    calc
      ((k : ℚ) + 1) * P (k + 2) = _ := P_step_two k
      _ = _ := by ring
  dsimp [b]
  rw [hfac, pow_add, hP]
  norm_num
  field_simp
  ring

private theorem ascPochhammer_eval_prod (x : ℚ) (k : ℕ) :
    (ascPochhammer ℚ k).eval x = ∏ j ∈ Finset.range k, (x + j) := by
  induction k with
  | zero => simp
  | succ k ih => rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]

/-- Mathlib's generalized binomial coefficient has the expected rising-product form. -/
theorem choose_eq_asc_product (x : ℚ) (k : ℕ) :
    Ring.choose x k =
      (∏ j ∈ Finset.range k, (x - k + 1 + j)) / (Nat.factorial k : ℚ) := by
  rw [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval, ascPochhammer_eval_prod]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Exact bridge from the product definition to the generalized-binomial formula. -/
theorem b_eq_choose (k : ℕ) :
    b k = 4 ^ k / ((k : ℚ) + 1) * Ring.choose ((3 * (k : ℚ) - 1) / 2) k := by
  have hp : (∏ j ∈ Finset.range k, ((3 * (k : ℚ) - 1) / 2 - k + 1 + j)) =
      P k / 2 ^ k := by
    calc
      _ = ∏ j ∈ Finset.range k, (((k : ℚ) + 1 + 2 * j) / 2) := by
        apply Finset.prod_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.prod_div_distrib]; simp [P]
  have hfac : (Nat.factorial (k + 1) : ℚ) =
      ((k : ℚ) + 1) * (Nat.factorial k : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    rfl
  have hk : (k : ℚ) + 1 ≠ 0 := by positivity
  have hn : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  have ht : (2 : ℚ) ^ k ≠ 0 := by positivity
  have hfour : (4 : ℚ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
  rw [choose_eq_asc_product, hp, hfour]
  dsimp [b]
  rw [hfac]
  field_simp

#print axioms P_step_two
#print axioms b_step_two
#print axioms b_eq_choose

end OEISOpen.A089073
