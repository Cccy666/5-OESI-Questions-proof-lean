import OEISOpen.A219692.Certificates

/-!
The summation stage is checked independently of the still-unproved shift and
Bridge identities. Theorems with a local-certificate hypothesis are proof
reductions, not claims that the binomial recurrence has been formalized.
-/

namespace OEISOpen.A219692

theorem v_eq_extended_sum {m N : ℕ} (hm : m / 3 ≤ N) :
    v m = ∑ j ∈ Finset.range (N+1), S m j := by
  rw [v_eq_sum_S]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j _ hj
  apply S_eq_zero_of_unsupported
  have h : ¬ j < m / 3 + 1 := by simpa only [Finset.mem_range] using hj
  omega

theorem v_cast_eq_extended_sum {m N : ℕ} (hm : m / 3 ≤ N) :
    (v m : ℚ) = ∑ j ∈ Finset.range (N+1), (S m j : ℚ) := by
  exact_mod_cast v_eq_extended_sum hm

theorem sum_G_differences (n : ℕ) :
    ∑ j ∈ Finset.range (n / 3 + 1), (G n (j+1) - G n j) = 0 := by
  rw [Finset.sum_range_sub, G_at_upper_endpoint, G_zero, sub_self]

/-- Finite summation has no remaining endpoint or cutoff proof obligation. -/
theorem positive_recurrence_of_local_certificate (n : ℕ)
    (hTel : ∀ j : ℕ,
      (n : ℚ)^3 * (S n j : ℚ) - (p n : ℚ) * (S (n-1) j : ℚ) +
        (q n : ℚ) * (S (n-2) j : ℚ) = G n (j+1) - G n j) :
    residual v n = 0 := by
  have hs := Finset.sum_congr (s₁ := Finset.range (n / 3 + 1)) rfl
    (fun j _ => hTel j)
  rw [sum_G_differences] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  rw [← v_cast_eq_extended_sum (m := n) (N := n / 3) (by omega),
    ← v_cast_eq_extended_sum (m := n-1) (N := n / 3) (by omega),
    ← v_cast_eq_extended_sum (m := n-2) (N := n / 3) (by omega)] at hs
  have hq : (residual v n : ℚ) = 0 := by
    simpa only [residual, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast] using hs
  exact_mod_cast hq

end OEISOpen.A219692
