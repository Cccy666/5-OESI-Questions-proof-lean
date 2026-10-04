import OEISOpen.A150500.Paths

/-!
# One-dimensional meanders

This file develops the counting bridge for `MeanderLegal` as defined in
`Paths.lean`. In particular, appending a final sign checks exactly one new
inequality. No counting formula is used in the definition.
-/

namespace OEISOpen.A150500

def endpoint {n : ℕ} (u : Fin n → Bool) : ℤ := ((List.ofFn u).map sign).sum

theorem meanderLegal_iff_take {n : ℕ} (u : Fin n → Bool) :
    MeanderLegal u ↔ ∀ j ≤ n, 0 ≤ (((List.ofFn u).take j).map sign).sum := by
  constructor
  · intro h j hj
    exact h ⟨j, by omega⟩
  · intro h j
    exact h j (by omega)

theorem endpoint_nonneg {n : ℕ} (u : Meander n) : 0 ≤ endpoint u.val := by
  have h := u.property (Fin.last n)
  change 0 ≤ (((List.ofFn u.val).take n).map sign).sum at h
  rw [List.take_of_length_le (by simp only [List.length_ofFn, le_refl])] at h
  exact h

@[simp] theorem ofFn_snoc_bool {n : ℕ} (u : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc u b) = List.ofFn u ++ [b] := by
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

@[simp] theorem endpoint_snoc {n : ℕ} (u : Fin n → Bool) (b : Bool) :
    endpoint (Fin.snoc u b) = endpoint u + sign b := by
  unfold endpoint
  rw [ofFn_snoc_bool, List.map_append, List.sum_append]
  simp only [List.map_singleton, List.sum_singleton]

theorem meanderLegal_snoc {n : ℕ} (u : Fin n → Bool) (b : Bool) :
    MeanderLegal (Fin.snoc u b) ↔ MeanderLegal u ∧ 0 ≤ endpoint u + sign b := by
  have ht (j : ℕ) (hj : j ≤ n) :
      (List.ofFn (Fin.snoc u b)).take j = (List.ofFn u).take j := by
    rw [ofFn_snoc_bool, List.take_append_of_le_length]
    simpa using hj
  rw [meanderLegal_iff_take, meanderLegal_iff_take]
  constructor
  · intro h
    constructor
    · intro j hj
      have hh := h j (by omega)
      rw [ht j hj] at hh
      exact hh
    · have he := h (n + 1) (by omega)
      rw [List.take_of_length_le (by simp only [List.length_ofFn, le_refl])] at he
      change 0 ≤ endpoint (Fin.snoc u b) at he
      rwa [endpoint_snoc] at he
  · rintro ⟨hu, hb⟩ j hj
    by_cases hjn : j ≤ n
    · rw [ht j hjn]
      exact hu j hjn
    · have heq : j = n + 1 := by omega
      subst j
      rw [List.take_of_length_le (by simp only [List.length_ofFn, le_refl])]
      change 0 ≤ endpoint (Fin.snoc u b)
      rwa [endpoint_snoc]

def upExtension {n : ℕ} (u : Meander n) : Meander (n + 1) :=
  ⟨Fin.snoc u.val true, (meanderLegal_snoc _ _).mpr ⟨u.property, by
    have := endpoint_nonneg u
    simp only [sign, ↓reduceIte]
    omega⟩⟩

def downExtension {n : ℕ} (u : {u : Meander n // endpoint u.val ≠ 0}) :
    Meander (n + 1) :=
  ⟨Fin.snoc u.val.val false, (meanderLegal_snoc _ _).mpr ⟨u.val.property, by
    have := endpoint_nonneg u.val
    have := u.property
    simp only [sign, Bool.false_eq_true, ↓reduceIte]
    omega⟩⟩

def initMeander {n : ℕ} (w : Meander (n + 1)) : Meander n :=
  ⟨Fin.init w.val, (meanderLegal_snoc (Fin.init w.val) (w.val (Fin.last n))).mp
    (by simpa using w.property) |>.1⟩

theorem initMeander_endpoint_ne_zero {n : ℕ} (w : Meander (n + 1))
    (hb : w.val (Fin.last n) = false) : endpoint (initMeander w).val ≠ 0 := by
  have h := (meanderLegal_snoc (Fin.init w.val) (w.val (Fin.last n))).mp
    (by simpa using w.property) |>.2
  simp only [hb, sign, Bool.false_eq_true, ↓reduceIte] at h
  change endpoint (Fin.init w.val) ≠ 0
  omega

def meanderSuccEquiv (n : ℕ) :
    Meander (n + 1) ≃ (Meander n ⊕ {u : Meander n // endpoint u.val ≠ 0}) where
  toFun w := if h : w.val (Fin.last n) = false then
    Sum.inr ⟨initMeander w, initMeander_endpoint_ne_zero w h⟩
    else Sum.inl (initMeander w)
  invFun := Sum.elim upExtension downExtension
  left_inv w := by
    dsimp only
    split
    · rename_i h
      apply Subtype.ext
      change Fin.snoc (Fin.init w.val) false = w.val
      rw [← h, Fin.snoc_init_self]
    · rename_i h
      have ht : w.val (Fin.last n) = true := by cases hb : w.val (Fin.last n) <;> simp_all
      apply Subtype.ext
      change Fin.snoc (Fin.init w.val) true = w.val
      rw [← ht, Fin.snoc_init_self]
  right_inv w := by
    cases w with
    | inl u =>
      simp only [Sum.elim_inl, upExtension, Fin.snoc_last, Bool.true_eq_false,
        ↓reduceDIte]
      congr 1
      apply Subtype.ext
      change Fin.init (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) u.val true) = u.val
      simp only [Fin.init_snoc]
    | inr u =>
      simp only [Sum.elim_inr, downExtension, Fin.snoc_last, ↓reduceDIte]
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      change Fin.init (Fin.snoc (α := fun _ : Fin (n + 1) => Bool) u.val.val false) = u.val.val
      simp only [Fin.init_snoc]

def zeroMeanderCount (n : ℕ) : ℕ :=
  Fintype.card {u : Meander n // endpoint u.val = 0}

theorem meanderCount_succ_add_zero (n : ℕ) :
    meanderCount (n + 1) + zeroMeanderCount n = 2 * meanderCount n := by
  have hs := Fintype.card_congr (meanderSuccEquiv n)
  have hc := Fintype.card_congr (Equiv.sumCompl (fun u : Meander n => endpoint u.val = 0))
  simp only [Fintype.card_sum, ne_eq] at hs hc
  unfold meanderCount zeroMeanderCount
  omega

theorem sum_sign_eq_counts (w : List Bool) :
    (w.map sign).sum = (w.count true : ℤ) - (w.count false : ℤ) := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp_all [sign] <;> omega

theorem meanderLegal_iff_all_take {n : ℕ} (u : Fin n → Bool) :
    MeanderLegal u ↔ ∀ j, 0 ≤ (((List.ofFn u).take j).map sign).sum := by
  rw [meanderLegal_iff_take]
  constructor
  · intro h j
    by_cases hj : j ≤ n
    · exact h j hj
    · have hn := h n le_rfl
      rw [List.take_of_length_le (by simp only [List.length_ofFn]; omega)]
      rw [List.take_of_length_le (by simp only [List.length_ofFn, le_refl])] at hn
      exact hn
  · intro h j _
    exact h j

def boolToDyck (b : Bool) : DyckStep := if b then .U else .D
def dyckToBool : DyckStep → Bool
  | .U => true
  | .D => false

@[simp] theorem dyckToBool_boolToDyck (b : Bool) : dyckToBool (boolToDyck b) = b := by
  cases b <;> rfl

@[simp] theorem boolToDyck_dyckToBool (d : DyckStep) : boolToDyck (dyckToBool d) = d := by
  cases d <;> rfl

@[simp] theorem count_boolToDyck_U (w : List Bool) :
    (w.map boolToDyck).count .U = w.count true := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp_all [boolToDyck]

@[simp] theorem count_boolToDyck_D (w : List Bool) :
    (w.map boolToDyck).count .D = w.count false := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp_all [boolToDyck]

theorem sum_sign_dyckToBool (w : List DyckStep) :
    ((w.map dyckToBool).map sign).sum = (w.count .U : ℤ) - (w.count .D : ℤ) := by
  induction w with
  | nil => simp
  | cons d w ih => cases d <;> simp_all [dyckToBool, sign] <;> omega

def zeroMeanderToDyck {n : ℕ} (u : {u : Meander n // endpoint u.val = 0}) : DyckWord where
  toList := (List.ofFn u.val.val).map boolToDyck
  count_U_eq_count_D := by
    simp only [count_boolToDyck_U, count_boolToDyck_D]
    have h := u.property
    rw [endpoint, sum_sign_eq_counts] at h
    omega
  count_D_le_count_U j := by
    rw [← List.map_take, count_boolToDyck_D, count_boolToDyck_U]
    have h := (meanderLegal_iff_all_take u.val.val).mp u.val.property j
    rw [sum_sign_eq_counts] at h
    omega

@[simp] theorem zeroMeanderToDyck_length {n : ℕ}
    (u : {u : Meander n // endpoint u.val = 0}) : (zeroMeanderToDyck u).toList.length = n := by
  simp [zeroMeanderToDyck]

def wordOfList {n : ℕ} (w : List Bool) (h : w.length = n) : Fin n → Bool :=
  fun i => w.get ⟨i.val, by omega⟩

@[simp] theorem ofFn_wordOfList {n : ℕ} (w : List Bool) (h : w.length = n) :
    List.ofFn (wordOfList w h) = w := by
  subst n
  exact List.ofFn_get w

def wordFromDyck {n : ℕ} (p : DyckWord) (h : p.toList.length = n) : Fin n → Bool :=
  wordOfList (p.toList.map dyckToBool) (by simpa using h)

@[simp] theorem ofFn_wordFromDyck {n : ℕ} (p : DyckWord) (h : p.toList.length = n) :
    List.ofFn (wordFromDyck p h) = p.toList.map dyckToBool :=
  ofFn_wordOfList _ _

theorem wordFromDyck_legal {n : ℕ} (p : DyckWord) (h : p.toList.length = n) :
    MeanderLegal (wordFromDyck p h) := by
  intro j
  rw [ofFn_wordFromDyck, ← List.map_take, sum_sign_dyckToBool]
  have := p.count_D_le_count_U j
  omega

theorem wordFromDyck_endpoint {n : ℕ} (p : DyckWord) (h : p.toList.length = n) :
    endpoint (wordFromDyck p h) = 0 := by
  rw [endpoint, ofFn_wordFromDyck, sum_sign_dyckToBool, p.count_U_eq_count_D, sub_self]

def zeroMeanderEquivDyck (n : ℕ) :
    {u : Meander n // endpoint u.val = 0} ≃ {p : DyckWord // p.toList.length = n} where
  toFun u := ⟨zeroMeanderToDyck u, zeroMeanderToDyck_length u⟩
  invFun p := ⟨⟨wordFromDyck p.val p.property, wordFromDyck_legal p.val p.property⟩,
    wordFromDyck_endpoint p.val p.property⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply List.ofFn_injective
    change List.ofFn (wordFromDyck (zeroMeanderToDyck u) (zeroMeanderToDyck_length u)) =
      List.ofFn u.val.val
    rw [ofFn_wordFromDyck]
    change ((List.ofFn u.val.val).map boolToDyck).map dyckToBool = _
    simp only [List.map_map, Function.comp_def, dyckToBool_boolToDyck]
    exact List.map_id' _
  right_inv p := by
    apply Subtype.ext
    apply DyckWord.ext
    change (List.ofFn (wordFromDyck p.val p.property)).map boolToDyck = p.val.toList
    rw [ofFn_wordFromDyck]
    simp only [List.map_map, Function.comp_def, boolToDyck_dyckToBool]
    exact List.map_id' _

def zeroMeanderEquivDyckSemilength (k : ℕ) :
    {u : Meander (2 * k) // endpoint u.val = 0} ≃ {p : DyckWord // p.semilength = k} :=
  (zeroMeanderEquivDyck (2 * k)).trans (Equiv.subtypeEquivRight fun p => by
    have := p.two_mul_semilength_eq_length
    omega)

theorem zeroMeanderCount_even (k : ℕ) : zeroMeanderCount (2 * k) = catalan k := by
  unfold zeroMeanderCount
  rw [Fintype.card_congr (zeroMeanderEquivDyckSemilength k)]
  exact DyckWord.card_dyckWord_semilength_eq_catalan k

theorem zeroMeanderCount_odd (k : ℕ) : zeroMeanderCount (2 * k + 1) = 0 := by
  have hi : IsEmpty {u : Meander (2 * k + 1) // endpoint u.val = 0} := ⟨by
    intro u
    have h := (zeroMeanderToDyck u).two_mul_semilength_eq_length
    rw [zeroMeanderToDyck_length] at h
    omega⟩
  exact Fintype.card_eq_zero

theorem odd_choose_add_catalan (k : ℕ) :
    Nat.choose (2 * k + 1) k + catalan k = 2 * Nat.centralBinom k := by
  have hb := Nat.add_one_mul_choose_eq (2 * k) k
  rw [Nat.choose_symm_half] at hb
  have hc := succ_mul_catalan_eq_centralBinom k
  apply Nat.eq_of_mul_eq_mul_left (show 0 < k + 1 by omega)
  rw [Nat.centralBinom] at hc ⊢
  nlinarith

theorem centralBinom_succ_eq_twice_odd_choose (k : ℕ) :
    Nat.centralBinom (k + 1) = 2 * Nat.choose (2 * k + 1) k := by
  rw [Nat.centralBinom, show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
    Nat.choose_succ_succ', Nat.choose_symm_half]
  omega

theorem meanderCount_zero : meanderCount 0 = 1 := by decide

theorem meanderCount_odd_of_even (k : ℕ)
    (he : meanderCount (2 * k) = Nat.centralBinom k) :
    meanderCount (2 * k + 1) = Nat.choose (2 * k + 1) k := by
  have hs := meanderCount_succ_add_zero (2 * k)
  rw [zeroMeanderCount_even, he] at hs
  have hc := odd_choose_add_catalan k
  omega

theorem meanderCount_even (k : ℕ) : meanderCount (2 * k) = Nat.centralBinom k := by
  induction k with
  | zero => simpa using meanderCount_zero
  | succ k ih =>
    have ho := meanderCount_odd_of_even k ih
    have hs := meanderCount_succ_add_zero (2 * k + 1)
    rw [zeroMeanderCount_odd, ho] at hs
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega] at hs
    rw [centralBinom_succ_eq_twice_odd_choose]
    omega

theorem meanderCount_odd (k : ℕ) :
    meanderCount (2 * k + 1) = Nat.choose (2 * k + 1) k :=
  meanderCount_odd_of_even k (meanderCount_even k)

/-- The unrestricted-endpoint, nonnegative sign-walk count. -/
theorem meanderCount_eq_choose (n : ℕ) : meanderCount n = Nat.choose n (n / 2) := by
  have hd := Nat.mod_add_div n 2
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hn : n = 2 * (n / 2) := by omega
    conv_lhs => rw [hn, meanderCount_even, Nat.centralBinom]
    rw [← hn]
  · have hn : n = 2 * (n / 2) + 1 := by omega
    conv_lhs => rw [hn, meanderCount_odd]
    rw [← hn]

theorem movingPathCount_eq_choose_square (n : ℕ) :
    movingPathCount n = Nat.choose n (n / 2) ^ 2 := by
  rw [movingPathCount_eq_square, meanderCount_eq_choose]

#print axioms meanderLegal_iff_take
#print axioms endpoint_nonneg
#print axioms ofFn_snoc_bool
#print axioms endpoint_snoc
#print axioms meanderLegal_snoc
#print axioms upExtension
#print axioms downExtension
#print axioms initMeander
#print axioms initMeander_endpoint_ne_zero
#print axioms meanderSuccEquiv
#print axioms meanderCount_succ_add_zero
#print axioms sum_sign_eq_counts
#print axioms meanderLegal_iff_all_take
#print axioms dyckToBool_boolToDyck
#print axioms boolToDyck_dyckToBool
#print axioms count_boolToDyck_U
#print axioms count_boolToDyck_D
#print axioms sum_sign_dyckToBool
#print axioms zeroMeanderToDyck
#print axioms zeroMeanderToDyck_length
#print axioms ofFn_wordOfList
#print axioms ofFn_wordFromDyck
#print axioms wordFromDyck_legal
#print axioms wordFromDyck_endpoint
#print axioms zeroMeanderEquivDyck
#print axioms zeroMeanderEquivDyckSemilength
#print axioms zeroMeanderCount_even
#print axioms zeroMeanderCount_odd
#print axioms odd_choose_add_catalan
#print axioms centralBinom_succ_eq_twice_odd_choose
#print axioms meanderCount_zero
#print axioms meanderCount_odd_of_even
#print axioms meanderCount_even
#print axioms meanderCount_odd
#print axioms meanderCount_eq_choose
#print axioms movingPathCount_eq_choose_square

end OEISOpen.A150500
