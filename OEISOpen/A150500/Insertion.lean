import OEISOpen.A150500.Paths
import OEISOpen.A150500.SubsetCount

/-! Insertion of the common pause positions. The data are a subset of the
original time positions and one legal moving word, read in increasing order. -/
namespace OEISOpen.A150500

abbrev LegalWord (n : ℕ) := {w : Word n // Legal (List.ofFn w)}
abbrev InsertionData (n : ℕ) := Σ s : Finset (Fin n), MovingLegalWord s.card

def movingSupport {n : ℕ} (w : Word n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => w i ≠ .pause)

@[simp] theorem mem_movingSupport {n : ℕ} (w : Word n) (i : Fin n) :
    i ∈ movingSupport w ↔ w i ≠ .pause := by simp [movingSupport]

theorem filter_finRange_eq_sort {n : ℕ} (s : Finset (Fin n)) :
    (List.finRange n).filter (fun i => decide (i ∈ s)) = s.sort := by
  apply ((List.sortedLT_finRange n).pairwise.filter _).sortedLT.eq_of_mem_iff s.sortedLT_sort
  simp

theorem erase_ofFn_eq_ordered {n : ℕ} (s : Finset (Fin n)) (w : Word n)
    (hs : ∀ i, w i ≠ .pause ↔ i ∈ s) :
    erasePauses (List.ofFn w) =
      List.ofFn (fun j => w (s.orderEmbOfFin rfl j)) := by
  unfold erasePauses
  rw [List.ofFn_eq_map, List.filter_map]
  change ((List.finRange n).filter (fun i => w i != .pause)).map w = _
  have hf : (List.finRange n).filter (fun i => w i != .pause) = s.sort := by
    rw [← filter_finRange_eq_sort s]
    apply List.filter_congr
    intro i hi
    apply Bool.eq_iff_iff.mpr
    simpa using hs i
  rw [hf, ← Finset.listMap_orderEmbOfFin_finRange s rfl,
    List.map_map, ← List.ofFn_eq_map]
  rfl

noncomputable def insertWord {n : ℕ} (s : Finset (Fin n))
    (v : Fin s.card → {x : Step // x ≠ .pause}) : Word n :=
  fun i => if hi : i ∈ s then
    (v ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩)).val else .pause

@[simp] theorem insertWord_support {n : ℕ} (s : Finset (Fin n))
    (v : Fin s.card → {x : Step // x ≠ .pause}) (i : Fin n) :
    insertWord s v i ≠ .pause ↔ i ∈ s := by
  unfold insertWord
  split_ifs with h
  · exact iff_of_true (v ((s.orderIsoOfFin rfl).symm ⟨i,h⟩)).property h
  · simp [h]

@[simp] theorem insertWord_ordered {n : ℕ} (s : Finset (Fin n))
    (v : Fin s.card → {x : Step // x ≠ .pause}) (j : Fin s.card) :
    insertWord s v (s.orderEmbOfFin rfl j) = (v j).val := by
  unfold insertWord
  rw [dite_eq_left (s.orderEmbOfFin_mem rfl j)]
  congr 2
  apply (s.orderIsoOfFin rfl).injective
  simp only [OrderIso.apply_symm_apply]
  rfl

theorem erase_insertWord {n : ℕ} (s : Finset (Fin n))
    (v : Fin s.card → {x : Step // x ≠ .pause}) :
    erasePauses (List.ofFn (insertWord s v)) =
      List.ofFn (fun j => (v j).val) := by
  rw [erase_ofFn_eq_ordered s _ (insertWord_support s v)]
  congr 1
  funext j
  exact insertWord_ordered s v j

noncomputable def insertLegal {n : ℕ} (a : InsertionData n) : LegalWord n :=
  ⟨insertWord a.1 a.2.val, (legal_erasePauses_iff _).mp (by
    rw [erase_insertWord]
    exact a.2.property)⟩

theorem insertLegal_injective (n : ℕ) :
    Function.Injective (@insertLegal n) := by
  rintro ⟨s,u⟩ ⟨t,v⟩ h
  have hw : insertWord s u.val = insertWord t v.val := congrArg Subtype.val h
  have hst : s = t := by
    apply Finset.ext
    intro i
    rw [← insertWord_support s u.val i, ← insertWord_support t v.val i, hw]
  cases hst
  apply congrArg (fun q : MovingLegalWord s.card => (Sigma.mk s q : InsertionData n))
  apply Subtype.ext
  funext j
  apply Subtype.ext
  have hi := congrFun hw (s.orderEmbOfFin rfl j)
  simpa only [insertWord_ordered] using hi

theorem insertLegal_surjective (n : ℕ) :
    Function.Surjective (@insertLegal n) := by
  intro w
  let s := movingSupport w.val
  let v : Fin s.card → {x : Step // x ≠ .pause} := fun j =>
    ⟨w.val (s.orderEmbOfFin rfl j),
      (mem_movingSupport w.val _).mp (s.orderEmbOfFin_mem rfl j)⟩
  have hv : Legal (List.ofFn (fun j => (v j).val)) := by
    have h := (legal_erasePauses_iff (List.ofFn w.val)).mpr w.property
    rw [erase_ofFn_eq_ordered s w.val (fun i => (mem_movingSupport w.val i).symm)] at h
    exact h
  refine ⟨⟨s,⟨v,hv⟩⟩, ?_⟩
  apply Subtype.ext
  funext i
  change insertWord s v i = w.val i
  unfold insertWord
  split_ifs with hi
  · change w.val (s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨i,hi⟩)) = w.val i
    exact congrArg w.val (congrArg Subtype.val
      ((s.orderIsoOfFin rfl).apply_symm_apply ⟨i,hi⟩))
  · have hpi : w.val i = .pause := by simpa [s] using hi
    exact hpi.symm

/-- The full common-position insertion equivalence, with all prefix constraints. -/
noncomputable def insertionEquiv (n : ℕ) : InsertionData n ≃ LegalWord n :=
  Equiv.ofBijective insertLegal ⟨insertLegal_injective n, insertLegal_surjective n⟩

theorem pathCount_eq_sum_supports (n : ℕ) :
    pathCount n = ∑ s : Finset (Fin n), movingPathCount s.card := by
  rw [pathCount_eq_card]
  rw [← Fintype.card_congr (insertionEquiv n)]
  simp only [InsertionData, Fintype.card_sigma, movingPathCount]

/-- The original path count is the binomial insertion transform of the
pause-free legal path count. No one-dimensional counting formula is needed. -/
theorem pathCount_eq_sum_moving (n : ℕ) :
    pathCount n = ∑ m ∈ Finset.range (n+1), Nat.choose n m * movingPathCount m := by
  rw [pathCount_eq_sum_supports, sum_subsets_by_card]

end OEISOpen.A150500
