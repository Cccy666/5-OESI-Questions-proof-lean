import Mathlib

/-!
# Original prefix-constrained paths for OEIS A150500

The alphabet has exactly the five triples in the problem. Coordinates are integers.
`Legal` checks every prefix, including the empty and full prefixes. `pathCount`
counts finite words in this original alphabet; it is not defined by a recurrence
or by the conjectured binomial formula.
-/

namespace OEISOpen.A150500

inductive Step where
  | downDown
  | downUp
  | pause
  | upDown
  | upUp
  deriving DecidableEq

instance : Fintype Step where
  elems := {.downDown, .downUp, .pause, .upDown, .upUp}
  complete := by intro s; cases s <;> simp

def Step.x : Step → ℤ
  | .downDown | .downUp => -1
  | .pause => 0
  | .upDown | .upUp => 1

def Step.y : Step → ℤ
  | .downDown | .downUp => -1
  | .pause | .upDown | .upUp => 1

def Step.z : Step → ℤ
  | .downDown | .upDown => -1
  | .pause => 0
  | .downUp | .upUp => 1

def Step.triple (s : Step) : ℤ × ℤ × ℤ := (s.x, s.y, s.z)

def Step.project (s : Step) : ℤ × ℤ := (s.x, s.z)

theorem step_triple_mem (s : Step) :
    s.triple ∈ ({(-1, -1, -1), (-1, -1, 1), (0, 1, 0),
      (1, 1, -1), (1, 1, 1)} : Finset (ℤ × ℤ × ℤ)) := by
  cases s <;> norm_num [Step.triple, Step.x, Step.y, Step.z]

theorem step_triple_range :
    Finset.univ.image Step.triple =
      ({(-1, -1, -1), (-1, -1, 1), (0, 1, 0),
        (1, 1, -1), (1, 1, 1)} : Finset (ℤ × ℤ × ℤ)) := by
  decide

theorem step_project_injective : Function.Injective Step.project := by
  intro s t h
  cases s <;> cases t <;> simp_all [Step.project, Step.x, Step.z]

def X (w : List Step) : ℤ := (w.map Step.x).sum
def Y (w : List Step) : ℤ := (w.map Step.y).sum
def Z (w : List Step) : ℤ := (w.map Step.z).sum

/-- Number of occurrences of the original step `(0,1,0)`. -/
def pauses (w : List Step) : ℕ := w.count .pause

theorem y_sub_x_eq_pauses (w : List Step) : Y w - X w = (pauses w : ℤ) := by
  induction w with
  | nil => simp [Y, X, pauses]
  | cons s w ih =>
    cases s <;> simp_all [Y, X, pauses, Step.x, Step.y]
    omega

theorem x_le_y (w : List Step) : X w ≤ Y w := by
  have := y_sub_x_eq_pauses w
  have : (0 : ℤ) ≤ pauses w := Int.natCast_nonneg _
  omega

def InOctant (w : List Step) : Prop := 0 ≤ X w ∧ 0 ≤ Y w ∧ 0 ≤ Z w
def InQuadrant (w : List Step) : Prop := 0 ≤ X w ∧ 0 ≤ Z w

instance (w : List Step) : Decidable (InOctant w) := inferInstanceAs
  (Decidable (0 ≤ X w ∧ 0 ≤ Y w ∧ 0 ≤ Z w))
instance (w : List Step) : Decidable (InQuadrant w) := inferInstanceAs
  (Decidable (0 ≤ X w ∧ 0 ≤ Z w))

theorem inOctant_iff_inQuadrant (w : List Step) : InOctant w ↔ InQuadrant w := by
  have hxy := x_le_y w
  simp only [InOctant, InQuadrant]
  omega

def Legal (w : List Step) : Prop := ∀ p ∈ w.inits, InOctant p
def ProjectedLegal (w : List Step) : Prop := ∀ p ∈ w.inits, InQuadrant p

instance (w : List Step) : Decidable (Legal w) := inferInstanceAs
  (Decidable (∀ p ∈ w.inits, InOctant p))
instance (w : List Step) : Decidable (ProjectedLegal w) := inferInstanceAs
  (Decidable (∀ p ∈ w.inits, InQuadrant p))

theorem legal_iff_projectedLegal (w : List Step) : Legal w ↔ ProjectedLegal w := by
  simp only [Legal, ProjectedLegal, inOctant_iff_inQuadrant]

theorem legal_iff_prefixes (w : List Step) :
    Legal w ↔ ∀ p, p <+: w → InOctant p := by
  simp only [Legal, List.mem_inits]

theorem legal_iff_take (w : List Step) :
    Legal w ↔ ∀ j ≤ w.length, InOctant (w.take j) := by
  rw [legal_iff_prefixes]
  constructor
  · intro h j _
    exact h _ (List.take_prefix j w)
  · intro h p hp
    rw [List.prefix_iff_eq_take.mp hp]
    exact h p.length hp.length_le

theorem prefix_y_sub_x_eq_pauses (w : List Step) (j : ℕ) :
    Y (w.take j) - X (w.take j) = (pauses (w.take j) : ℤ) :=
  y_sub_x_eq_pauses _

theorem project_word_injective :
    Function.Injective (List.map Step.project) :=
  List.map_injective_iff.mpr step_project_injective

/-- Delete precisely the common zero steps after projection to `(x,z)`. -/
def erasePauses (w : List Step) : List Step := w.filter (· != .pause)

theorem length_erasePauses_add_pauses (w : List Step) :
    (erasePauses w).length + pauses w = w.length := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases s <;> simp_all [erasePauses, pauses] <;> omega

theorem length_erasePauses (w : List Step) :
    (erasePauses w).length = w.length - pauses w := by
  have := length_erasePauses_add_pauses w
  omega

@[simp] theorem X_erasePauses (w : List Step) : X (erasePauses w) = X w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases s <;> simp_all [erasePauses, X, Step.x]

@[simp] theorem Z_erasePauses (w : List Step) : Z (erasePauses w) = Z w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    cases s <;> simp_all [erasePauses, Z, Step.z]

@[simp] theorem inQuadrant_erasePauses (w : List Step) :
    InQuadrant (erasePauses w) ↔ InQuadrant w := by
  simp [InQuadrant]

/-- Every original prefix projects to a prefix of the compressed word, and
every compressed prefix is obtained in this way. Thus deleting the common
pauses preserves *all* prefix inequalities, in both directions. -/
theorem legal_erasePauses_iff (w : List Step) : Legal (erasePauses w) ↔ Legal w := by
  simp only [legal_iff_projectedLegal, ProjectedLegal, List.mem_inits]
  constructor
  · intro h p hp
    exact (inQuadrant_erasePauses p).mp
      (h _ (hp.filter (fun s : Step => s != Step.pause)))
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := List.prefix_filter_iff.mp hp
    exact (inQuadrant_erasePauses q).mpr (h q hq)

theorem erasePauses_letters (w : List Step) (s : Step) (hs : s ∈ erasePauses w) :
    (s.x = -1 ∨ s.x = 1) ∧ (s.z = -1 ∨ s.z = 1) := by
  have hne : s ≠ .pause := by simpa [erasePauses] using (List.mem_filter.mp hs).2
  cases s <;> simp_all [Step.x, Step.z]

def sign (b : Bool) : ℤ := if b then 1 else -1

/-- The four moving steps are the full Cartesian product of two signs. -/
def ofSigns : Bool × Bool → Step
  | (false, false) => .downDown
  | (false, true) => .downUp
  | (true, false) => .upDown
  | (true, true) => .upUp

def toSigns (s : Step) : Bool × Bool := (decide (s.x = 1), decide (s.z = 1))

@[simp] theorem ofSigns_x (b : Bool × Bool) : (ofSigns b).x = sign b.1 := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;> rfl

@[simp] theorem ofSigns_z (b : Bool × Bool) : (ofSigns b).z = sign b.2 := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;> rfl

@[simp] theorem ofSigns_ne_pause (b : Bool × Bool) : ofSigns b ≠ .pause := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;> decide

@[simp] theorem toSigns_ofSigns (b : Bool × Bool) : toSigns (ofSigns b) = b := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;> rfl

theorem ofSigns_toSigns (s : Step) (hs : s ≠ .pause) : ofSigns (toSigns s) = s := by
  cases s <;> simp_all [toSigns, ofSigns, Step.x, Step.z]

def nonPauseEquivSigns : {s : Step // s ≠ .pause} ≃ (Bool × Bool) where
  toFun s := toSigns s.val
  invFun b := ⟨ofSigns b, ofSigns_ne_pause b⟩
  left_inv s := Subtype.ext (ofSigns_toSigns s.val s.property)
  right_inv := toSigns_ofSigns

def nonPauseWordEquiv (n : ℕ) :
    (Fin n → {s : Step // s ≠ .pause}) ≃ ((Fin n → Bool) × (Fin n → Bool)) where
  toFun w := (fun i => (toSigns (w i).val).1, fun i => (toSigns (w i).val).2)
  invFun uv i := ⟨ofSigns (uv.1 i, uv.2 i), ofSigns_ne_pause _⟩
  left_inv w := by
    funext i
    exact Subtype.ext (ofSigns_toSigns (w i).val (w i).property)
  right_inv uv := by
    rcases uv with ⟨u, v⟩
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst (toSigns_ofSigns (u i, v i))
    · exact congrArg Prod.snd (toSigns_ofSigns (u i, v i))

/-- A one-dimensional nonnegative sign walk, with unrestricted endpoint. -/
def MeanderLegal {n : ℕ} (u : Fin n → Bool) : Prop :=
  ∀ j : Fin (n + 1), 0 ≤ (((List.ofFn u).take j).map sign).sum

instance {n : ℕ} (u : Fin n → Bool) : Decidable (MeanderLegal u) :=
  inferInstanceAs (Decidable (∀ j : Fin (n + 1),
    0 ≤ (((List.ofFn u).take j).map sign).sum))

def synchronousWord {n : ℕ} (u v : Fin n → Bool) : List Step :=
  List.ofFn fun i => ofSigns (u i, v i)

@[simp] theorem synchronousWord_length {n : ℕ} (u v : Fin n → Bool) :
    (synchronousWord u v).length = n := by
  simp [synchronousWord]

theorem X_synchronousWord_take {n : ℕ} (u v : Fin n → Bool) (j : ℕ) :
    X ((synchronousWord u v).take j) = (((List.ofFn u).take j).map sign).sum := by
  simp only [X, synchronousWord, List.map_take, List.map_ofFn]
  simp only [Function.comp_def, ofSigns_x]

theorem Z_synchronousWord_take {n : ℕ} (u v : Fin n → Bool) (j : ℕ) :
    Z ((synchronousWord u v).take j) = (((List.ofFn v).take j).map sign).sum := by
  simp only [Z, synchronousWord, List.map_take, List.map_ofFn]
  simp only [Function.comp_def, ofSigns_z]

/-- The two compressed coordinate walks can be chosen independently. Both
coordinates share the same moving positions because they are zipped here. -/
theorem legal_synchronousWord_iff {n : ℕ} (u v : Fin n → Bool) :
    Legal (synchronousWord u v) ↔ MeanderLegal u ∧ MeanderLegal v := by
  rw [legal_iff_take]
  simp only [inOctant_iff_inQuadrant, InQuadrant, X_synchronousWord_take,
    Z_synchronousWord_take, synchronousWord_length]
  constructor
  · intro h
    constructor
    · intro j
      exact (h j (by omega)).1
    · intro j
      exact (h j (by omega)).2
  · rintro ⟨hu, hv⟩ j hj
    exact ⟨hu ⟨j, by omega⟩, hv ⟨j, by omega⟩⟩

theorem synchronousWord_toSigns {n : ℕ} (w : Fin n → {s : Step // s ≠ .pause}) :
    synchronousWord (fun i => (toSigns (w i).val).1)
      (fun i => (toSigns (w i).val).2) = List.ofFn (fun i => (w i).val) := by
  unfold synchronousWord
  apply congrArg List.ofFn
  funext i
  exact ofSigns_toSigns (w i).val (w i).property

abbrev Meander (n : ℕ) := {u : Fin n → Bool // MeanderLegal u}

abbrev MovingLegalWord (n : ℕ) :=
  {w : Fin n → {s : Step // s ≠ .pause} // Legal (List.ofFn fun i => (w i).val)}

/-- A complete finite equivalence for the pause-free part of the decomposition. -/
def movingLegalWordEquiv (n : ℕ) : MovingLegalWord n ≃ (Meander n × Meander n) where
  toFun w := by
    let u := fun i => (toSigns (w.val i).val).1
    let v := fun i => (toSigns (w.val i).val).2
    have h : Legal (synchronousWord u v) := by
      rw [synchronousWord_toSigns]
      exact w.property
    exact (⟨u, (legal_synchronousWord_iff u v).mp h |>.1⟩,
      ⟨v, (legal_synchronousWord_iff u v).mp h |>.2⟩)
  invFun uv := ⟨fun i => ⟨ofSigns (uv.1.val i, uv.2.val i), ofSigns_ne_pause _⟩,
    (legal_synchronousWord_iff uv.1.val uv.2.val).mpr ⟨uv.1.property, uv.2.property⟩⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    exact Subtype.ext (ofSigns_toSigns (w.val i).val (w.val i).property)
  right_inv uv := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      exact congrArg Prod.fst (toSigns_ofSigns (uv.1.val i, uv.2.val i))
    · apply Subtype.ext
      funext i
      exact congrArg Prod.snd (toSigns_ofSigns (uv.1.val i, uv.2.val i))

def meanderCount (n : ℕ) : ℕ := Fintype.card (Meander n)
def movingPathCount (n : ℕ) : ℕ := Fintype.card (MovingLegalWord n)

theorem movingPathCount_eq_square (n : ℕ) : movingPathCount n = meanderCount n ^ 2 := by
  simpa [movingPathCount, meanderCount, Fintype.card_prod, pow_two] using
    Fintype.card_congr (movingLegalWordEquiv n)

/-- Original length-`n` words; all five letters are available at every position. -/
abbrev Word (n : ℕ) := Fin n → Step

def pathCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Word n => Legal (List.ofFn w)).card

theorem pathCount_eq_card (n : ℕ) :
    pathCount n = Fintype.card {w : Word n // Legal (List.ofFn w)} := by
  exact (Fintype.card_subtype (fun w : Word n => Legal (List.ofFn w))).symm

set_option maxRecDepth 10000 in
theorem pathCount_zero : pathCount 0 = 1 := by decide

set_option maxRecDepth 10000 in
theorem pathCount_one : pathCount 1 = 2 := by decide

set_option maxRecDepth 10000 in
theorem pathCount_two : pathCount 2 = 7 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem pathCount_three : pathCount 3 = 25 := by decide

#print axioms step_triple_mem
#print axioms step_triple_range
#print axioms step_project_injective
#print axioms y_sub_x_eq_pauses
#print axioms x_le_y
#print axioms inOctant_iff_inQuadrant
#print axioms legal_iff_prefixes
#print axioms legal_iff_take
#print axioms legal_iff_projectedLegal
#print axioms prefix_y_sub_x_eq_pauses
#print axioms project_word_injective
#print axioms length_erasePauses_add_pauses
#print axioms length_erasePauses
#print axioms X_erasePauses
#print axioms Z_erasePauses
#print axioms inQuadrant_erasePauses
#print axioms legal_erasePauses_iff
#print axioms erasePauses_letters
#print axioms ofSigns_x
#print axioms ofSigns_z
#print axioms ofSigns_ne_pause
#print axioms toSigns_ofSigns
#print axioms ofSigns_toSigns
#print axioms nonPauseEquivSigns
#print axioms nonPauseWordEquiv
#print axioms synchronousWord_length
#print axioms X_synchronousWord_take
#print axioms Z_synchronousWord_take
#print axioms legal_synchronousWord_iff
#print axioms synchronousWord_toSigns
#print axioms movingLegalWordEquiv
#print axioms movingPathCount_eq_square
#print axioms pathCount_eq_card
#print axioms pathCount_zero
#print axioms pathCount_one
#print axioms pathCount_two
#print axioms pathCount_three

end OEISOpen.A150500
