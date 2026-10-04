import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Sum

/-!
Exact, separate definitions for A219692.  Natural subtraction occurs only in
binomial arguments on the stated finite support. Polynomial coefficients and
the alternating sum live in `ℤ`, so their subtraction is ordinary subtraction.
The original zeroth term is explicitly 2; the normalized zeroth term is 1.
-/

namespace OEISOpen.A219692

def originalTerm (n j : ℕ) : ℤ :=
  (-1 : ℤ)^j * n.choose j * (2*j).choose j * (2*n-2*j).choose (n-j) *
    ((2*n-3*j-1).choose n + ((2*n-3*j).choose n : ℤ))

def a (n : ℕ) : ℤ :=
  if n = 0 then 2 else ∑ j ∈ Finset.range (n / 3 + 1), originalTerm n j

def u (n : ℕ) : ℤ := if n = 0 then 1 else a n

def positiveTerm (n j : ℕ) : ℤ :=
  (3 : ℤ)^(n-3*j) * (2*n-2*j).choose (n-j) * (n-j).choose (2*j) *
    ((2*j).choose j : ℤ)^2

/-- Explicit zero extension; no factorial or power outside the support is used. -/
def S (n j : ℕ) : ℤ := if 3*j ≤ n then positiveTerm n j else 0

def v (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n / 3 + 1), positiveTerm n j

def p (n : ℤ) : ℤ := 2 * (2*n-1) * (7*n^2-7*n+3)
def q (n : ℤ) : ℤ := 12 * (4*n-5) * (n-1) * (4*n-3)

/-- The inherited numerical display `p 2 = 126` was a separate typo. -/
theorem p_two : p 2 = 102 := by norm_num [p]
theorem q_two : q 2 = 180 := by norm_num [q]

def residual (b : ℕ → ℤ) (n : ℕ) : ℤ :=
  (n : ℤ)^3 * b n - p n * b (n-1) + q n * b (n-2)

@[simp] theorem a_zero : a 0 = 2 := by norm_num [a]
@[simp] theorem a_one : a 1 = 6 := by norm_num [a, originalTerm, Finset.sum_range_succ]
@[simp] theorem a_two : a 2 = 54 := by norm_num [a, originalTerm, Finset.sum_range_succ, Nat.choose]
@[simp] theorem u_zero : u 0 = 1 := by norm_num [u]
@[simp] theorem u_one : u 1 = 6 := by norm_num [u]
@[simp] theorem u_two : u 2 = 54 := by norm_num [u]
@[simp] theorem v_zero : v 0 = 1 := by norm_num [v, positiveTerm, Finset.sum_range_succ]
@[simp] theorem v_one : v 1 = 6 := by norm_num [v, positiveTerm, Finset.sum_range_succ]
@[simp] theorem v_two : v 2 = 54 := by norm_num [v, positiveTerm, Finset.sum_range_succ, Nat.choose]

/-- T0: the unnormalized statement already fails at its first proposed index. -/
theorem original_residual_two : residual a 2 = 180 := by
  norm_num [residual, p, q]

/-- Exact boundary witness used to audit the inherited factorial simplification. -/
theorem original_term_three_one : originalTerm 3 1 = -36 := by
  norm_num [originalTerm, Nat.choose]

theorem original_recurrence_from_two_false :
    ¬ (∀ n : ℕ, 2 ≤ n → residual a n = 0) := by
  intro h
  have h2 := h 2 (by omega)
  rw [original_residual_two] at h2
  norm_num at h2

theorem normalized_residual_two : residual u 2 = 0 := by
  norm_num [residual, p, q]

theorem u_eq_a_of_pos {n : ℕ} (hn : 0 < n) : u n = a n := by
  simp [u, Nat.ne_of_gt hn]

theorem residual_u_eq_a {n : ℕ} (hn : 3 ≤ n) : residual u n = residual a n := by
  have h0 : 0 < n := by omega
  have h1 : 0 < n-1 := by omega
  have h2 : 0 < n-2 := by omega
  simp only [residual, u_eq_a_of_pos h0, u_eq_a_of_pos h1, u_eq_a_of_pos h2]

/-- The logical passage T1 → T2, with the first index kept explicit. -/
theorem tail_recurrence_of_normalized
    (h : ∀ n : ℕ, 2 ≤ n → residual u n = 0) :
    ∀ n : ℕ, 3 ≤ n → residual a n = 0 := by
  intro n hn
  rw [← residual_u_eq_a hn]
  exact h n (by omega)

theorem supported_iff (n j : ℕ) : 3*j ≤ n ↔ j < n / 3 + 1 := by omega

theorem S_eq_zero_of_unsupported {n j : ℕ} (h : n < 3*j) : S n j = 0 := by
  simp [S, show ¬ 3*j ≤ n by omega]

theorem S_eq_positiveTerm {n j : ℕ} (h : 3*j ≤ n) : S n j = positiveTerm n j := by
  simp [S, h]

theorem S_at_upper_endpoint (n : ℕ) : S n (n / 3 + 1) = 0 := by
  apply S_eq_zero_of_unsupported
  omega

/-- The cutoff definition is equal to the sum of the explicitly supported terms. -/
theorem v_eq_sum_S (n : ℕ) : v n = ∑ j ∈ Finset.range (n / 3 + 1), S n j := by
  unfold v
  apply Finset.sum_congr rfl
  intro j hj
  symm
  apply S_eq_positiveTerm
  have := Finset.mem_range.mp hj
  omega

theorem original_binomial_arguments {n j : ℕ} (hn : 1 ≤ n) (hj : 3*j ≤ n) :
    j ≤ n ∧ 1 ≤ 2*n-3*j ∧ n ≤ 2*n-3*j ∧ n-j ≤ 2*n-2*j := by
  omega

end OEISOpen.A219692
