import OEISOpen.A219692.Definitions

/-! The inherited map had `n-j` in this numerator. The correct factor is `n-2*j`. -/

namespace OEISOpen.A219692

/-- The original bracket identity, in crossed form, including `3*j=n`. -/
theorem original_bracket_crossed (n j : ℕ) (hn : 1 ≤ n) (hj : 3*j ≤ n) :
    (2*(n : ℤ)-3*(j : ℤ)) *
      (((2*n-3*j-1).choose n : ℤ) + ((2*n-3*j).choose n : ℤ)) =
      3*((n : ℤ)-2*(j : ℤ)) * ((2*n-3*j).choose n : ℤ) := by
  let m := 2*n-3*j
  have hnm : n ≤ m := by dsimp [m]; omega
  have hm : 1 ≤ m := by omega
  have he : m-1+1 = m := by omega
  have hh := Nat.choose_mul_succ_eq (m-1) n
  rw [he] at hh
  have hh' := congrArg (fun z : ℕ => (z : ℤ)) hh
  push_cast at hh'
  rw [Nat.cast_sub hnm] at hh'
  have hm' : (m : ℤ) = 2*(n : ℤ)-3*(j : ℤ) := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : 3*j ≤ 2*n)]
    push_cast
    rfl
  change _ * (((m-1).choose n : ℤ) + (m.choose n : ℤ)) = _ * (m.choose n : ℤ)
  rw [hm'] at hh'
  linear_combination hh'

end OEISOpen.A219692
