import OEISOpen.A219692.LaurentTransform

/-! Central binomial constant terms in arbitrary commutative coefficient rings. -/
namespace OEISOpen.A219692

open Finset LaurentPolynomial

/-- The standard central-binomial Laurent constant term, without a characteristic hypothesis. -/
theorem laurent_ct_central {R : Type*} [CommRing R] (m : ℕ) :
    ((2 + T 1 + T (-1) : LaurentPolynomial R)^m).coeff 0 =
      ((2*m).choose m : R) := by
  have hset : Finset.Icc 0 (m/2) = Finset.range (m/2+1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  have hnat := p1 m 0 (by omega)
  rw [hset] at hnat
  simp only [Nat.choose_zero_right, Nat.sub_zero, mul_one, one_mul, mul_zero] at hnat
  have hC2 : C (2 : R) = (2 : LaurentPolynomial R) := by
    rw [show (2 : R) = 1+1 by ring, map_add, map_one]
    ring
  calc
    _ = ∑ r ∈ Finset.range (m/2+1),
        (m.choose (2*r) : R) * ((2*r).choose r : R) * (2 : R)^(m-2*r) := by
      simpa [hC2] using laurent_ct_trinomial (R := R) m 2 1 1
    _ = _ := by
      have hc := congrArg (fun z : ℕ => (z : R)) hnat
      push_cast at hc
      exact hc

/-- The even antisymmetric Laurent constant term, including k=0. -/
theorem laurent_ct_antisymmetric_even {R : Type*} [CommRing R] (k : ℕ) :
    ((T 1 - T (-1) : LaurentPolynomial R)^(2*k)).coeff 0 =
      (-1 : R)^k * ((2*k).choose k : R) := by
  have h := laurent_ct_trinomial (R := R) (2*k) 0 1 (-1)
  simp only [one_mul] at h
  have hrange : 2*k/2+1 = k+1 := by omega
  rw [hrange] at h
  have hsum :
      (∑ r ∈ Finset.range (k+1),
        ((2*k).choose (2*r) : R) * ((2*r).choose r : R) *
          (0 : R)^(2*k-2*r) * (-1 : R)^r) =
      (-1 : R)^k * ((2*k).choose k : R) := by
    rw [Finset.sum_eq_single k]
    · simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_one]
      ring
    · intro r hr hne
      have hr' : r < k+1 := Finset.mem_range.mp hr
      have hexp : 2*k-2*r ≠ 0 := by omega
      rw [zero_pow hexp, mul_zero, zero_mul]
    · intro hk
      exact False.elim (hk (Finset.mem_range.mpr (by omega)))
  simpa only [map_zero, map_one, map_neg, zero_add, one_mul, neg_one_mul,
    ← sub_eq_add_neg] using h.trans hsum

end OEISOpen.A219692
