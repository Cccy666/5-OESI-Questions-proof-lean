import OEISOpen.A089073.Certificates

namespace OEISOpen.A089073

/-- Parity lift. Its value at zero is auxiliary, not an empty-graph count. -/
def parityLift (b : ℕ → ℚ) (n : ℕ) : ℚ :=
  if n % 2 = 0 then b (n / 2) / 2 else b (n / 2)

theorem parityLift_even (b : ℕ → ℚ) (k : ℕ) :
    parityLift b (2 * k) = b k / 2 := by
  simp [parityLift]

theorem parityLift_odd (b : ℕ → ℚ) (k : ℕ) :
    parityLift b (2 * k + 1) = b k := by
  simp [parityLift, Nat.add_div]

theorem parityLift_recurrence_even (b : ℕ → ℚ)
    (hb : ∀ k : ℕ, ((k : ℚ) + 2) * (k + 3) * b (k + 2) =
      12 * (3 * k + 1) * (3 * k + 5) * b k) (m : ℕ) :
    residual (parityLift b) (2 * m + 6) = 0 := by
  have h := hb (m + 1)
  have h0 : 2 * m + 6 = 2 * (m + 3) := by omega
  have h1 : 2 * m + 6 - 1 = 2 * (m + 2) + 1 := by omega
  have h2 : 2 * m + 6 - 2 = 2 * (m + 2) := by omega
  have h3 : 2 * m + 6 - 3 = 2 * (m + 1) + 1 := by omega
  have h4 : 2 * m + 6 - 4 = 2 * (m + 1) := by omega
  have hcomb : parityLift b (2 * m + 6 - 1) -
      2 * parityLift b (2 * m + 6 - 2) +
      4 * parityLift b (2 * m + 6 - 3) =
      8 * parityLift b (2 * m + 6 - 4) := by
    rw [h1, h2, h3, h4, parityLift_even, parityLift_even,
      parityLift_odd, parityLift_odd]
    ring
  rw [residual_even_factor _ _ hcomb]
  have hs : ((2 * m + 6 : ℕ) : ℚ) * (↑(2 * m + 6) + 2) *
      parityLift b (2 * m + 6) -
      12 * (3 * ↑(2 * m + 6) - 10) * (3 * ↑(2 * m + 6) - 2) *
      parityLift b (2 * m + 6 - 4) = 0 := by
    rw [h4, parityLift_even]
    rw [show parityLift b (2 * m + 6) = b (m + 3) / 2 by
      rw [h0, parityLift_even]]
    norm_num [Nat.cast_add, Nat.cast_mul] at h ⊢
    have hi : m + 1 + 2 = m + 3 := by omega
    rw [hi] at h
    linear_combination 2 * h
  rw [hs, mul_zero]

theorem parityLift_recurrence_odd (b : ℕ → ℚ)
    (hb : ∀ k : ℕ, ((k : ℚ) + 2) * (k + 3) * b (k + 2) =
      12 * (3 * k + 1) * (3 * k + 5) * b k) (m : ℕ) :
    residual (parityLift b) (2 * m + 5) = 0 := by
  have h := hb m
  have h0 : 2 * m + 5 = 2 * (m + 2) + 1 := by omega
  have h1 : 2 * m + 5 - 1 = 2 * (m + 2) := by omega
  have h2 : 2 * m + 5 - 2 = 2 * (m + 1) + 1 := by omega
  have h3 : 2 * m + 5 - 3 = 2 * (m + 1) := by omega
  have h4 : 2 * m + 5 - 4 = 2 * m + 1 := by omega
  have hcomb : parityLift b (2 * m + 5 - 1) -
      2 * parityLift b (2 * m + 5 - 2) +
      4 * parityLift b (2 * m + 5 - 3) =
      parityLift b (2 * m + 5) / 2 := by
    rw [h1, h2, h3, h0, parityLift_even, parityLift_even,
      parityLift_odd, parityLift_odd]
    ring
  rw [residual_odd_factor _ _ hcomb]
  have hs : (↑(2 * m + 5) - 1 : ℚ) * (↑(2 * m + 5) + 1) *
      parityLift b (2 * m + 5) -
      12 * (3 * ↑(2 * m + 5) - 13) * (3 * ↑(2 * m + 5) - 5) *
      parityLift b (2 * m + 5 - 4) = 0 := by
    rw [h4, parityLift_odd]
    rw [show parityLift b (2 * m + 5) = b (m + 2) by
      rw [h0, parityLift_odd]]
    norm_num [Nat.cast_add, Nat.cast_mul]
    linear_combination 4 * h
  rw [hs, mul_zero]

theorem parityLift_recurrence (b : ℕ → ℚ)
    (hb : ∀ k : ℕ, ((k : ℚ) + 2) * (k + 3) * b (k + 2) =
      12 * (3 * k + 1) * (3 * k + 5) * b k) (n : ℕ) (hn : 5 ≤ n) :
    residual (parityLift b) n = 0 := by
  by_cases he : n % 2 = 0
  · obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 6 := ⟨n / 2 - 3, by omega⟩
    rw [hm]
    exact parityLift_recurrence_even b hb m
  · obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 5 := ⟨n / 2 - 2, by omega⟩
    rw [hm]
    exact parityLift_recurrence_odd b hb m

end OEISOpen.A089073
