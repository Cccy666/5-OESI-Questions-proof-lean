import OEISOpen.A219692.Definitions
import Mathlib.Data.Nat.Choose.Central

namespace OEISOpen.A219692

private theorem central_step (m : ℕ) :
    ((m : ℚ)+1) * ((2*(m+1)).choose (m+1) : ℚ) =
      2*(2*(m : ℚ)+1) * ((2*m).choose m : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ m
  unfold Nat.centralBinom at h
  exact_mod_cast h

private theorem S_cast (n j : ℕ) (h : 3*j ≤ n) :
    (S n j : ℚ) = (3 : ℚ)^(n-3*j) * ((2*n-2*j).choose (n-j) : ℚ) *
      ((n-j).choose (2*j) : ℚ) * ((2*j).choose j : ℚ)^2 := by
  simp [S, h, positiveTerm]

private theorem shift1_supported (n j : ℕ) (hj : 3*j ≤ n) :
    6*(2*((n : ℚ)+1)-2*(j : ℚ)-1)*(S n j : ℚ) =
      ((n : ℚ)+1-3*(j : ℚ))*(S (n+1) j : ℚ) := by
  let m := n-j
  have hm : 2*j ≤ m := by dsimp [m]; omega
  have hnj : n = m+j := by dsimp [m]; omega
  have h1 : n+1-j = m+1 := by omega
  have h2 : 2*n-2*j = 2*m := by omega
  have h3 : 2*(n+1)-2*j = 2*(m+1) := by omega
  have h4 : n+1-3*j = (n-3*j)+1 := by omega
  have h5 : m+1-2*j = n-3*j+1 := by omega
  have hb := central_step m
  have hc : ((m : ℚ)+1) * (m.choose (2*j) : ℚ) =
      ((m : ℚ)+1-2*(j : ℚ)) * ((m+1).choose (2*j) : ℚ) := by
    have hh := Nat.choose_mul_succ_eq m (2*j)
    have hhq := congrArg (fun x : ℕ => (x : ℚ)) hh
    push_cast at hhq
    rw [Nat.cast_sub (by omega : 2*j ≤ m+1)] at hhq
    push_cast at hhq
    linear_combination hhq
  have core : 2*(2*(m : ℚ)+1) * ((2*m).choose m : ℚ) * (m.choose (2*j) : ℚ) =
      ((m : ℚ)+1-2*(j : ℚ)) * ((2*(m+1)).choose (m+1) : ℚ) *
        ((m+1).choose (2*j) : ℚ) := by
    linear_combination ((2*(m+1)).choose (m+1) : ℚ) * hc - (m.choose (2*j) : ℚ) * hb
  rw [S_cast n j hj, S_cast (n+1) j (by omega), h1, h2, h3, h4, pow_succ]
  change _ * (_ * _ * (m.choose (2*j) : ℚ) * _) = _
  have hnjq : (n : ℚ) = (m : ℚ)+(j : ℚ) := by exact_mod_cast hnj
  rw [hnjq]
  linear_combination 3 * (3 : ℚ)^(n-3*j) * ((2*j).choose j : ℚ)^2 * core

theorem shift1_succ (n j : ℕ) :
    6*(2*((n : ℚ)+1)-2*(j : ℚ)-1)*(S n j : ℚ) =
      ((n : ℚ)+1-3*(j : ℚ))*(S (n+1) j : ℚ) := by
  by_cases hj : 3*j ≤ n
  · exact shift1_supported n j hj
  · have hz : S n j = 0 := S_eq_zero_of_unsupported (by omega)
    by_cases hj1 : 3*j ≤ n+1
    · have he : n+1 = 3*j := by omega
      have heq : (n : ℚ)+1-3*(j : ℚ) = 0 := by
        have hh : (n : ℚ)+1 = 3*(j : ℚ) := by exact_mod_cast he
        linarith
      simp [hz, heq]
    · have hz1 : S (n+1) j = 0 := S_eq_zero_of_unsupported (by omega)
      simp [hz, hz1]

theorem shift1 (n j : ℕ) (hn : 1 ≤ n) :
    6*(2*(n : ℚ)-2*(j : ℚ)-1)*(S (n-1) j : ℚ) =
      ((n : ℚ)-3*(j : ℚ))*(S n j : ℚ) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k+1 := ⟨n-1, by omega⟩
  simpa using shift1_succ k j

theorem shift2 (n j : ℕ) (hn : 2 ≤ n) :
    36*(2*(n : ℚ)-2*(j : ℚ)-1)*(2*(n : ℚ)-2*(j : ℚ)-3)*(S (n-2) j : ℚ) =
      ((n : ℚ)-3*(j : ℚ))*((n : ℚ)-3*(j : ℚ)-1)*(S n j : ℚ) := by
  have h1 := shift1 n j (by omega)
  have h2 := shift1 (n-1) j (by omega)
  have he : n-1-1 = n-2 := by omega
  rw [he, Nat.cast_sub (by omega : 1 ≤ n)] at h2
  push_cast at h2
  linear_combination 6*(2*(n : ℚ)-2*(j : ℚ)-1)*h2 +
    ((n : ℚ)-3*(j : ℚ)-1)*h1

private theorem choose_raise2 (m j : ℕ) (hj : 2*j+2 ≤ m) :
    ((m : ℚ)+1)*(2*(j : ℚ)+1)*(2*(j : ℚ)+2)*(m.choose (2*j+2) : ℚ) =
      ((m : ℚ)+1-2*(j : ℚ))*((m : ℚ)-2*(j : ℚ))*
        ((m : ℚ)-1-2*(j : ℚ))*((m+1).choose (2*j) : ℚ) := by
  have hA := congrArg (fun z : ℕ => (z : ℚ)) (Nat.choose_mul_succ_eq m (2*j+2))
  have hB := congrArg (fun z : ℕ => (z : ℚ)) (Nat.choose_succ_right_eq (m+1) (2*j+1))
  have hC := congrArg (fun z : ℕ => (z : ℚ)) (Nat.choose_succ_right_eq (m+1) (2*j))
  push_cast at hA hB hC
  rw [Nat.cast_sub (by omega : 2*j+1 ≤ m)] at hA
  rw [Nat.cast_sub (by omega : 2*j ≤ m)] at hB
  rw [Nat.cast_sub (by omega : 2*j ≤ m+1)] at hC
  push_cast at hA hB hC
  linear_combination (2*(j : ℚ)+1)*(2*(j : ℚ)+2)*hA +
    (2*(j : ℚ)+1)*((m : ℚ)-1-2*(j : ℚ))*hB +
    ((m : ℚ)-2*(j : ℚ))*((m : ℚ)-1-2*(j : ℚ))*hC

private theorem shiftJ_core (m j : ℕ) (hj : 2*j+2 ≤ m) :
    ((j : ℚ)+1)^3*(2*(m : ℚ)+1)*((2*m).choose m : ℚ)*
        (m.choose (2*j+2) : ℚ)*((2*(j+1)).choose (j+1) : ℚ)^2 =
      (2*(j : ℚ)+1)*((m : ℚ)+1-2*(j : ℚ))*((m : ℚ)-2*(j : ℚ))*
        ((m : ℚ)-1-2*(j : ℚ))*((2*(m+1)).choose (m+1) : ℚ)*
        ((m+1).choose (2*j) : ℚ)*((2*j).choose j : ℚ)^2 := by
  have hm := central_step m
  have hc := choose_raise2 m j hj
  have hjc := central_step j
  have hsq : ((j : ℚ)+1)^2*((2*(j+1)).choose (j+1) : ℚ)^2 =
      4*(2*(j : ℚ)+1)^2*((2*j).choose j : ℚ)^2 := by
    linear_combination (((j : ℚ)+1)*((2*(j+1)).choose (j+1) : ℚ) +
      2*(2*(j : ℚ)+1)*((2*j).choose j : ℚ))*hjc
  linear_combination
    ((j : ℚ)+1)*(2*(m : ℚ)+1)*((2*m).choose m : ℚ)*(m.choose (2*j+2) : ℚ)*hsq -
    2*((j : ℚ)+1)*(2*(j : ℚ)+1)^2*(m.choose (2*j+2) : ℚ)*((2*j).choose j : ℚ)^2*hm +
    (2*(j : ℚ)+1)*((2*(m+1)).choose (m+1) : ℚ)*((2*j).choose j : ℚ)^2*hc

private theorem shiftJ_supported (n j : ℕ) (hj : 3*(j+1) ≤ n) :
    27*((j : ℚ)+1)^3*(2*(n : ℚ)-2*(j : ℚ)-1)*(S n (j+1) : ℚ) =
      (2*(j : ℚ)+1)*((n : ℚ)-3*(j : ℚ))*((n : ℚ)-3*(j : ℚ)-1)*
        ((n : ℚ)-3*(j : ℚ)-2)*(S n j : ℚ) := by
  let m := n-j-1
  have hm : 2*j+2 ≤ m := by dsimp [m]; omega
  have hnj : n = m+j+1 := by dsimp [m]; omega
  have h1 : n-(j+1) = m := by omega
  have h2 : n-j = m+1 := by omega
  have h3 : 2*n-2*(j+1) = 2*m := by omega
  have h4 : 2*n-2*j = 2*(m+1) := by omega
  have h5 : n-3*j = n-3*(j+1)+3 := by omega
  have h6 : 2*(j+1) = 2*j+2 := by omega
  have core := shiftJ_core m j hm
  rw [S_cast n (j+1) hj, S_cast n j (by omega), h1, h2, h3, h4, h5, pow_add]
  norm_num only [show (3 : ℚ)^3 = 27 by norm_num]
  have hnjq : (n : ℚ) = (m : ℚ)+(j : ℚ)+1 := by exact_mod_cast hnj
  rw [hnjq]
  rw [h6] at core ⊢
  linear_combination 27*(3 : ℚ)^(n-3*(j+1))*core

theorem shiftJ (n j : ℕ) :
    27*((j : ℚ)+1)^3*(2*(n : ℚ)-2*(j : ℚ)-1)*(S n (j+1) : ℚ) =
      (2*(j : ℚ)+1)*((n : ℚ)-3*(j : ℚ))*((n : ℚ)-3*(j : ℚ)-1)*
        ((n : ℚ)-3*(j : ℚ)-2)*(S n j : ℚ) := by
  by_cases hj : 3*(j+1) ≤ n
  · exact shiftJ_supported n j hj
  · have hz1 : S n (j+1) = 0 := S_eq_zero_of_unsupported (by omega)
    by_cases hj0 : 3*j ≤ n
    · have ht : n = 3*j ∨ n = 3*j+1 ∨ n = 3*j+2 := by omega
      rcases ht with he | he | he
      all_goals
        have heq := congrArg (fun z : ℕ => (z : ℚ)) he
        push_cast at heq
        simp only [hz1, Int.cast_zero, mul_zero]
        rw [heq]
        ring
    · have hz0 : S n j = 0 := S_eq_zero_of_unsupported (by omega)
      simp [hz0, hz1]

end OEISOpen.A219692
