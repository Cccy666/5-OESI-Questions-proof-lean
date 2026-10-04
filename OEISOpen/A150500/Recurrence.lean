import OEISOpen.A150500.Pullback

/-! Coefficient extraction from the differential equation for A150500.
This module is conditional on the equation for a rational power series; it does
not identify that series with the original walk count. -/
namespace OEISOpen.A150500
open PowerSeries

noncomputable def thetaSeries (A : Series) : Series := X * D A

theorem coeff_thetaSeries (A : Series) (n : ℕ) :
    coeff n (thetaSeries A) = (n : ℚ) * coeff n A := by
  cases n with
  | zero => simp [thetaSeries]
  | succ n =>
    rw [thetaSeries, coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

theorem targetOperator_euler (A : Series) :
    targetOperator A =
      (thetaSeries (thetaSeries A) + C 2 * thetaSeries A + A) +
      X^1 * (C (-9) * thetaSeries A + C (-13) * A) +
      X^2 * (C (-22) * thetaSeries (thetaSeries A) +
        C (-61) * thetaSeries A + C (-19) * A) +
      X^3 * (C (-24) * thetaSeries (thetaSeries A) +
        C (-3) * thetaSeries A + C 21 * A) +
      X^4 * (C 45 * thetaSeries (thetaSeries A) +
        C 135 * thetaSeries A + C 90 * A) := by
  simp [targetOperator, thetaSeries, D, Derivation.leibniz, alpha, beta, gamma, delta,
    map_ofNat]
  ring

theorem coeff_targetOperator_shifted (A : Series) (k : ℕ) :
    coeff (k+4) (targetOperator A) =
      r4Poly ((k:ℚ)+4) (coeff (k+4) A) (coeff (k+3) A)
        (coeff (k+2) A) (coeff (k+1) A) (coeff k A) := by
  rw [targetOperator_euler]
  have h1 : 1 ≤ k+4 := by omega
  have h2 : 2 ≤ k+4 := by omega
  have h3 : 3 ≤ k+4 := by omega
  have h4 : 4 ≤ k+4 := by omega
  have e1 : k+4-1 = k+3 := by omega
  have e2 : k+4-2 = k+2 := by omega
  have e3 : k+4-3 = k+1 := by omega
  have e4 : k+4-4 = k := by omega
  simp only [map_add, coeff_X_pow_mul', h1, h2, h3, h4, ite_true,
    e1, e2, e3, e4, coeff_C_mul, coeff_thetaSeries]
  unfold r4Poly
  push_cast
  ring

theorem recurrence_of_target_shifted (A : Series)
    (h : targetOperator A = 1-5*X) (k : ℕ) :
    r4Poly ((k:ℚ)+4) (coeff (k+4) A) (coeff (k+3) A)
      (coeff (k+2) A) (coeff (k+1) A) (coeff k A) = 0 := by
  have heq := congrArg (coeff (k+4) : Series →ₗ[ℚ] ℚ) h
  rw [coeff_targetOperator_shifted] at heq
  have hz : coeff (k+4) (1-5*X : Series) = 0 := by
    have hc : (5 : Series) = C (5 : ℚ) := by rw [map_ofNat]
    rw [hc, map_sub, coeff_C_mul]
    simp [coeff_X, coeff_one, show k+4 ≠ 1 by omega]
  exact heq.trans hz

theorem recurrence_of_target (A : Series)
    (h : targetOperator A = 1-5*X) (n : ℕ) (hn : 4 ≤ n) :
    r4Poly (n:ℚ) (coeff n A) (coeff (n-1) A)
      (coeff (n-2) A) (coeff (n-3) A) (coeff (n-4) A) = 0 := by
  have e0 : n-4+4 = n := by omega
  have e1 : n-4+3 = n-1 := by omega
  have e2 : n-4+2 = n-2 := by omega
  have e3 : n-4+1 = n-3 := by omega
  have en : ((n-4:ℕ):ℚ)+4 = (n:ℚ) := by exact_mod_cast e0
  simpa only [e0, e1, e2, e3, en] using recurrence_of_target_shifted A h (n-4)

/-- The original n >= 4 expression, with integer-like subtraction in rational coefficients. -/
theorem recurrence_of_target_explicit (A : Series)
    (h : targetOperator A = 1-5*X) (n : ℕ) (hn : 4 ≤ n) :
    ((n:ℚ)+1)^2 * coeff n A - (9*(n:ℚ)+4)*coeff (n-1) A +
      (-22*(n:ℚ)^2+27*(n:ℚ)+15)*coeff (n-2) A -
      3*((n:ℚ)-2)*(8*(n:ℚ)-31)*coeff (n-3) A +
      45*((n:ℚ)-2)*((n:ℚ)-3)*coeff (n-4) A = 0 := by
  exact recurrence_of_target A h n hn

def r3Sequence (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  r3Poly (n:ℚ) (a n) (a (n-1)) (a (n-2)) (a (n-3))

def r4Sequence (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  r4Poly (n:ℚ) (a n) (a (n-1)) (a (n-2)) (a (n-3)) (a (n-4))

theorem r3_r4_sequence_relation (a : ℕ → ℚ) (n : ℕ) (hn : 4 ≤ n) :
    r3Sequence a n + 3*r3Sequence a (n-1) = (8*(n:ℚ)-5)*r4Sequence a n := by
  have e1 : n-1-1 = n-2 := by omega
  have e2 : n-1-2 = n-3 := by omega
  have e3 : n-1-3 = n-4 := by omega
  unfold r3Sequence r4Sequence
  simp only [e1, e2, e3, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  exact r3_r4_relation (n:ℚ) (a n) (a (n-1)) (a (n-2)) (a (n-3)) (a (n-4))

/-- E2 needs exactly one initial condition for its converse implication. -/
theorem r3_recurrence_iff_r4_and_initial (a : ℕ → ℚ) :
    (∀ n, 3 ≤ n → r3Sequence a n = 0) ↔
      (r3Sequence a 3 = 0 ∧ ∀ n, 4 ≤ n → r4Sequence a n = 0) := by
  constructor
  · intro h
    refine ⟨h 3 (by omega), ?_⟩
    intro n hn
    have rel := r3_r4_sequence_relation a n hn
    rw [h n (by omega), h (n-1) (by omega)] at rel
    simp only [mul_zero, zero_add] at rel
    have hnonzero : 8*(n:ℚ)-5 ≠ 0 := by
      have hnq : (4:ℚ) ≤ (n:ℚ) := by exact_mod_cast hn
      linarith
    exact (mul_eq_zero.mp rel.symm).resolve_left hnonzero
  · rintro ⟨hbase, hfour⟩ n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases heq : n = 3
      · simpa only [heq] using hbase
      · have hn4 : 4 ≤ n := by omega
        have hp : r3Sequence a (n-1) = 0 := ih (n-1) (by omega) (by omega)
        have rel := r3_r4_sequence_relation a n hn4
        rw [hp, hfour n hn4] at rel
        simpa using rel

theorem r3_initial_of_values (a : ℕ → ℚ)
    (h0 : a 0 = 1) (h1 : a 1 = 2) (h2 : a 2 = 7) (h3 : a 3 = 25) :
    r3Sequence a 3 = 0 := by
  norm_num [r3Sequence, r3Poly, h0, h1, h2, h3]

theorem r3_recurrence_iff_r4_of_values (a : ℕ → ℚ)
    (h0 : a 0 = 1) (h1 : a 1 = 2) (h2 : a 2 = 7) (h3 : a 3 = 25) :
    (∀ n, 3 ≤ n → r3Sequence a n = 0) ↔
      (∀ n, 4 ≤ n → r4Sequence a n = 0) := by
  rw [r3_recurrence_iff_r4_and_initial]
  simp only [r3_initial_of_values a h0 h1 h2 h3, true_and]

end OEISOpen.A150500
