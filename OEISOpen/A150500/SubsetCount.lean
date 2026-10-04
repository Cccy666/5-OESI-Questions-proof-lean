import Mathlib

/-! Grouping subsets of the moving positions by their cardinality. -/

namespace OEISOpen.A150500

theorem sum_subsets_by_card (n : ℕ) (f : ℕ → ℕ) :
    (∑ s : Finset (Fin n), f s.card) =
      ∑ m ∈ Finset.range (n + 1), Nat.choose n m * f m := by
  have h := Finset.sum_powerset (Finset.univ : Finset (Fin n)) (fun s => f s.card)
  simpa only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin,
    Finset.sum_powersetCard, nsmul_eq_mul, Nat.cast_id] using h

#print axioms sum_subsets_by_card

end OEISOpen.A150500
