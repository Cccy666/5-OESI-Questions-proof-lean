import OEISOpen.A219692.Definitions

namespace OEISOpen.A219692

/-- The recurrence determines a sequence from its first two values.
This does not identify either binomial sum with a recurrence-defined sequence. -/
theorem recurrence_unique (b c : ℕ → ℤ) (h0 : b 0 = c 0) (h1 : b 1 = c 1)
    (hb : ∀ n : ℕ, 2 ≤ n → residual b n = 0)
    (hc : ∀ n : ℕ, 2 ≤ n → residual c n = 0) : b = c := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · simpa [hn0] using h0
    by_cases hn1 : n = 1
    · simpa [hn1] using h1
    have hn : 2 ≤ n := by omega
    have hprev1 := ih (n-1) (by omega)
    have hprev2 := ih (n-2) (by omega)
    have hb' := hb n hn
    have hc' := hc n hn
    simp only [residual, hprev1, hprev2] at hb' hc'
    have hlead : (n : ℤ)^3 ≠ 0 := pow_ne_zero _ (by omega)
    apply mul_left_cancel₀ hlead
    linear_combination hb' - hc'

end OEISOpen.A219692
