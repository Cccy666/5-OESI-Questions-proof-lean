import OEISOpen.A219692.Trinomial

/-! Final finite-sum and binomial coefficient rearrangements used in P. -/
namespace OEISOpen.A219692

open Finset

/-- P1 with a fixed lower endpoint; the new terms vanish by choose's support. -/
theorem p1_range (n k : ℕ) (hk : 2*k ≤ n) :
    (∑ ell ∈ range (n/2+1),
      n.choose (2*ell) * (2*ell).choose ell * ell.choose k * 2^(n-2*ell)) =
      n.choose k * (2*n-2*k).choose n := by
  rw [← p1 n k hk]
  symm
  apply Finset.sum_subset
  · intro ell hell
    have h := Finset.mem_Icc.mp hell
    apply Finset.mem_range.mpr
    omega
  · intro ell hell hnot
    have hupper := Finset.mem_range.mp hell
    have hnot' : ¬ (k ≤ ell ∧ ell ≤ n/2) := by
      simpa only [Finset.mem_Icc] using hnot
    have hlower : ell < k := by omega
    simp only [Nat.choose_eq_zero_of_lt hlower, mul_zero, zero_mul]

/-- The last central-binomial coefficient rearrangement after applying P1. -/
theorem central_choose_rearrangement (n k : ℕ) (hk : 2*k ≤ n) :
    n.choose k * (2*(n-k)).choose n =
      (2*(n-k)).choose (n-k) * (n-k).choose k := by
  have h := Nat.choose_mul (n := 2*(n-k)) (k := n) (s := n-k) (by omega)
  rw [Nat.choose_symm (by omega : k ≤ n),
    show 2*(n-k)-(n-k) = n-k by omega,
    show n-(n-k) = k by omega] at h
  simpa only [Nat.mul_comm] using h

/-- P1 in exactly the central-binomial form required by the coefficient collection in P. -/
theorem p1_range_central (n k : ℕ) (hk : 2*k ≤ n) :
    (∑ ell ∈ range (n/2+1),
      n.choose (2*ell) * (2*ell).choose ell * ell.choose k * 2^(n-2*ell)) =
      (2*(n-k)).choose (n-k) * (n-k).choose k := by
  rw [p1_range n k hk, show 2*n-2*k = 2*(n-k) by omega]
  exact central_choose_rearrangement n k hk

end OEISOpen.A219692
