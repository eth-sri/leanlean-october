module

public import ADR11.Basic

@[expose] public section

namespace ADR11

open Finset

/-! ### Bitmask codes of clusters -/

/-- The cluster on `Fin n` with bitmask `c`: the `i < n` such that bit `i` of `c` is set. -/
def decC (n c : ℕ) : Finset (Fin n) := univ.filter fun i => c.testBit i

/-- The family of clusters with the bitmasks in the list `l`. -/
def decF (n : ℕ) (l : List ℕ) : Finset (Finset (Fin n)) := (l.map (decC n)).toFinset

/-- All codes in `l` are bitmasks of subsets of `Fin n`. -/
def Valid (n : ℕ) (l : List ℕ) : Prop := ∀ c ∈ l, c < 2 ^ n

instance (n : ℕ) (l : List ℕ) : Decidable (Valid n l) :=
  inferInstanceAs (Decidable (∀ c ∈ l, c < 2 ^ n))

theorem mem_decC {n c : ℕ} {i : Fin n} : i ∈ decC n c ↔ c.testBit i = true := by
  simp [decC]

theorem testBit_eq_false_of_lt {n c : ℕ} (hc : c < 2 ^ n) {i : ℕ} (hi : n ≤ i) :
    c.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hi))

theorem decC_inj {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    decC n a = decC n b ↔ a = b := by
  refine ⟨fun h => Nat.eq_of_testBit_eq fun i => ?_, fun h => h ▸ rfl⟩
  by_cases hi : i < n
  · have h' := congrArg (fun A => (⟨i, hi⟩ : Fin n) ∈ A) h
    simp only [mem_decC, eq_iff_iff] at h'
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rw [testBit_eq_false_of_lt ha (not_lt.1 hi), testBit_eq_false_of_lt hb (not_lt.1 hi)]

theorem decC_or (n a b : ℕ) : decC n (a ||| b) = decC n a ∪ decC n b := by
  ext i; simp [mem_decC]

theorem decC_subset_iff {n a b : ℕ} (ha : a < 2 ^ n) :
    decC n a ⊆ decC n b ↔ a &&& b = a := by
  refine ⟨fun h => Nat.eq_of_testBit_eq fun i => ?_, fun h i hi => ?_⟩
  · rw [Nat.testBit_and]
    by_cases hi : i < n
    · cases ha' : a.testBit i
      · simp
      · simp [mem_decC.1 (h (mem_decC.2 ha' : (⟨i, hi⟩ : Fin n) ∈ decC n a))]
    · simp [testBit_eq_false_of_lt ha (not_lt.1 hi)]
  · rw [mem_decC] at hi ⊢
    simpa only [Nat.testBit_and, hi, Bool.true_and] using congrArg (·.testBit i) h

theorem decC_nonempty_iff {n a : ℕ} (ha : a < 2 ^ n) : (decC n a).Nonempty ↔ a ≠ 0 :=
  ⟨by rintro ⟨i, hi⟩ rfl; simp [mem_decC] at hi, fun h => by
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    exact ⟨⟨i, not_le.1 fun hn => by simp [testBit_eq_false_of_lt ha hn] at hi⟩, mem_decC.2 hi⟩⟩

theorem decC_disjoint_iff {n a b : ℕ} (ha : a < 2 ^ n) :
    Disjoint (decC n a) (decC n b) ↔ a &&& b = 0 := by
  refine ⟨fun h => Nat.eq_of_testBit_eq fun i => ?_, fun h => Finset.disjoint_left.2 fun i hia hib => ?_⟩
  · rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < n
    · cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp
      exact Finset.disjoint_left.1 h (mem_decC.2 ha' : (⟨i, hi⟩ : Fin n) ∈ decC n a) (mem_decC.2 hb')
    · simp [testBit_eq_false_of_lt ha (not_lt.1 hi)]
  · have := congrArg (·.testBit i) h
    simp [Nat.testBit_and, mem_decC.1 hia, mem_decC.1 hib] at this

theorem decC_compl {n a : ℕ} : (decC n a)ᶜ = decC n ((2 ^ n - 1) ^^^ a) := by
  ext i; simp [mem_decC, Nat.testBit_xor, i.2]

theorem decC_full (n : ℕ) : decC n (2 ^ n - 1) = univ := by
  ext i; simp [mem_decC, i.2]

theorem decC_mod (n a : ℕ) : decC n (a % 2 ^ n) = decC n a := by
  ext i; simp [mem_decC, Nat.testBit_mod_two_pow, i.2]

theorem decC_eq_univ_iff {n a : ℕ} (ha : a < 2 ^ n) : decC n a = univ ↔ a = 2 ^ n - 1 := by
  rw [← decC_full n, decC_inj ha (by have := Nat.one_le_two_pow (n := n); omega)]

theorem decC_two_pow {n i : ℕ} (hi : i < n) : decC n (2 ^ i) = {⟨i, hi⟩} := by
  ext j
  simp only [mem_decC, Nat.testBit_two_pow, decide_eq_true_eq, mem_singleton, Fin.ext_iff]
  exact eq_comm

theorem mem_decF {n : ℕ} {l : List ℕ} {A : Finset (Fin n)} :
    A ∈ decF n l ↔ ∃ c ∈ l, decC n c = A := by
  simp [decF]

theorem decC_mem_decF {n : ℕ} {l : List ℕ} {c : ℕ} (h : c ∈ l) : decC n c ∈ decF n l :=
  mem_decF.2 ⟨c, h, rfl⟩

theorem decF_cons (n c : ℕ) (l : List ℕ) : decF n (c :: l) = insert (decC n c) (decF n l) := by
  simp [decF]

theorem decF_append (n : ℕ) (l₁ l₂ : List ℕ) : decF n (l₁ ++ l₂) = decF n l₁ ∪ decF n l₂ := by
  simp [decF]

theorem decF_union (n : ℕ) (l₁ l₂ : List ℕ) : decF n (l₁ ∪ l₂) = decF n l₁ ∪ decF n l₂ := by
  ext A; simp [mem_decF, List.mem_union_iff, or_and_right, exists_or]

theorem card_decF {n : ℕ} {l : List ℕ} (hl : Valid n l) (hnd : l.Nodup) : #(decF n l) = l.length := by
  rw [decF, List.toFinset_card_of_nodup (hnd.map_on fun a ha b hb e => (decC_inj (hl a ha) (hl b hb)).1 e),
    List.length_map]

def rootsL (F : List ℕ) : List ℕ := F.filter fun c => F.all fun d => !(c &&& d == c) || d == c

theorem mem_rootsL {F : List ℕ} {c : ℕ} :
    c ∈ rootsL F ↔ c ∈ F ∧ ∀ d ∈ F, c &&& d = c → d = c := by
  simp only [rootsL, List.mem_filter, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, beq_iff_eq]
  exact ⟨fun ⟨hc, h⟩ => ⟨hc, fun d hd hcd => (h d hd).resolve_left (not_not.2 hcd)⟩,
    fun ⟨hc, h⟩ => ⟨hc, fun d hd => (eq_or_ne (c &&& d) c).imp_left (h d hd) |>.symm⟩⟩

theorem valid_rootsL {n : ℕ} {F : List ℕ} (hv : Valid n F) : Valid n (rootsL F) :=
  fun c hc => hv c (mem_rootsL.1 hc).1

theorem nodup_rootsL {F : List ℕ} (hnd : F.Nodup) : (rootsL F).Nodup := hnd.filter _

theorem decF_rootsL {n : ℕ} {F : List ℕ} (hv : Valid n F) :
    decF n (rootsL F) = roots (decF n F) := by
  ext A; simp only [roots, mem_filter]
  refine ⟨fun hA => ?_, fun ⟨hA, h⟩ => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA
    rw [mem_rootsL] at hc
    refine ⟨decC_mem_decF hc.1, fun B hB hsub => ?_⟩
    obtain ⟨d, hd, rfl⟩ := mem_decF.1 hB
    rw [hc.2 d hd ((decC_subset_iff (hv c hc.1)).1 hsub)]
  · obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA
    exact decC_mem_decF (mem_rootsL.2 ⟨hc, fun d hd hcd => (decC_inj (hv d hd) (hv c hc)).1
      (h _ (decC_mem_decF hd) ((decC_subset_iff (hv c hc)).2 hcd))⟩)

theorem card_roots_decF {n : ℕ} {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup) :
    #(roots (decF n F)) = (rootsL F).length := by
  rw [← decF_rootsL hv, card_decF (valid_rootsL hv) (nodup_rootsL hnd)]

def pairsL : List ℕ → List (ℕ × ℕ)
  | [] => []
  | a :: l => l.map (fun b => (a, b)) ++ pairsL l

theorem length_pairsL : ∀ l : List ℕ, (pairsL l).length = l.length.choose 2
  | [] => rfl
  | a :: l => by
    simp only [pairsL, List.length_append, List.length_map, length_pairsL l, List.length_cons,
      Nat.choose_succ_succ, Nat.choose_one_right]

theorem mem_pairsL {l : List ℕ} {p : ℕ × ℕ} (h : p ∈ pairsL l) : p.1 ∈ l ∧ p.2 ∈ l := by
  induction l with
  | nil => simp [pairsL] at h
  | cons a l ih =>
    simp only [pairsL, List.mem_append, List.mem_map] at h
    rcases h with ⟨b, hb, rfl⟩ | h
    · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ hb⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, List.mem_cons_of_mem _ (ih h).2⟩

theorem ne_of_mem_pairsL {l : List ℕ} (hnd : l.Nodup) {p : ℕ × ℕ} (h : p ∈ pairsL l) :
    p.1 ≠ p.2 := by
  induction l with
  | nil => simp [pairsL] at h
  | cons a l ih =>
    simp only [pairsL, List.mem_append, List.mem_map] at h
    rw [List.nodup_cons] at hnd
    rcases h with ⟨b, hb, rfl⟩ | h
    · show a ≠ b; rintro rfl; exact hnd.1 hb
    · exact ih hnd.2 h

theorem mem_pairsL_of_ne {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    (a, b) ∈ pairsL l ∨ (b, a) ∈ pairsL l := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    simp only [pairsL, List.mem_append, List.mem_map, Prod.mk.injEq]
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hab
    · exact Or.inl (Or.inl ⟨b, hb', rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨a, ha', rfl, rfl⟩)
    · exact (ih ha' hb').imp Or.inr Or.inr

theorem decF_merge (n : ℕ) (F : List ℕ) (a b : ℕ) :
    decF n ((a ||| b) :: F) = insert (decC n a ∪ decC n b) (decF n F) := by
  rw [decF_cons, decC_or]

theorem nodup_of_card_toFinset {α : Type*} [DecidableEq α] {l : List α}
    (h : #l.toFinset = l.length) : l.Nodup :=
  List.dedup_eq_self.1 ((List.dedup_sublist l).eq_of_length (List.card_toFinset l ▸ h))

theorem roots_pair_of_mem_pairsL {n : ℕ} {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup)
    {p : ℕ × ℕ} (hp : p ∈ pairsL (rootsL F)) :
    decC n p.1 ∈ roots (decF n F) ∧ decC n p.2 ∈ roots (decF n F) ∧ decC n p.1 ≠ decC n p.2 := by
  have h12 := mem_pairsL hp
  rw [← decF_rootsL hv]
  exact ⟨decC_mem_decF h12.1, decC_mem_decF h12.2, fun h =>
    ne_of_mem_pairsL (nodup_rootsL hnd) hp
      ((decC_inj (valid_rootsL hv _ h12.1) (valid_rootsL hv _ h12.2)).1 h)⟩

theorem sum_merges_decF {n : ℕ} {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup)
    (hF : IsForest (decF n F)) {M : Type*} [AddCommMonoid M] (g : Finset (Finset (Fin n)) → M) :
    ∑ F' ∈ merges (decF n F), g F' =
      ((pairsL (rootsL F)).map fun p => g (decF n ((p.1 ||| p.2) :: F))).sum := by
  have hm : merges (decF n F) =
      ((pairsL (rootsL F)).map fun p => decF n ((p.1 ||| p.2) :: F)).toFinset := by
    ext F'
    simp only [merges, mem_image, mem_filter, mem_product, List.mem_toFinset, List.mem_map,
      Prod.exists]
    constructor
    · rintro ⟨A, B, ⟨⟨hA, hB⟩, hAB⟩, rfl⟩
      rw [← decF_rootsL hv] at hA hB
      obtain ⟨a, ha, rfl⟩ := mem_decF.1 hA
      obtain ⟨b, hb, rfl⟩ := mem_decF.1 hB
      rcases mem_pairsL_of_ne ha hb (fun h => hAB (h ▸ rfl)) with h | h
      · exact ⟨a, b, h, decF_merge n F a b⟩
      · exact ⟨b, a, h, by rw [decF_merge, union_comm]⟩
    · rintro ⟨a, b, hp, rfl⟩
      obtain ⟨ha, hb, hne⟩ := roots_pair_of_mem_pairsL hv hnd hp
      exact ⟨decC n a, decC n b, ⟨⟨ha, hb⟩, hne⟩, (decF_merge n F a b).symm⟩
  have hcard := hF.card_merges
  rw [hm] at hcard ⊢
  rw [List.sum_toFinset _ (nodup_of_card_toFinset
    (by rw [List.length_map, length_pairsL, ← card_roots_decF hv hnd, ← hcard])), List.map_map]
  rfl

theorem sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (l : List α) (f : α → List β)
    (g : β → M) : ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

def jumpL : ℕ → List ℕ → List (ℚ × List ℕ)
  | 0, F => [(1, F)]
  | j + 1, F => if (rootsL F).length ≤ 1 then [(1, F)] else
      (pairsL (rootsL F)).flatMap fun p => (jumpL j ((p.1 ||| p.2) :: F)).map fun q =>
        ((((rootsL F).length.choose 2 : ℕ) : ℚ)⁻¹ * q.1, q.2)

theorem jumpMatrix_pow_decF {n : ℕ} : ∀ (j : ℕ) (F : List ℕ), Valid n F → F.Nodup →
    IsForest (decF n F) → ∀ G : Finset (Finset (Fin n)),
    (jumpMatrix ^ j) (decF n F) G = ((jumpL j F).map fun q => if decF n q.2 = G then (q.1 : ℝ) else 0).sum
  | 0, F, _, _, _, G => by simp [jumpL, Matrix.one_apply, eq_comm]
  | j + 1, F, hv, hnd, hF, G => by
    by_cases hk : (rootsL F).length ≤ 1
    · rw [jumpMatrix_pow_of_card_roots_le_one (by rw [card_roots_decF hv hnd]; exact hk)]
      simp [jumpL, hk, eq_comm]
    · rw [jumpMatrix_pow_succ_apply (by rw [card_roots_decF hv hnd]; omega),
        sum_merges_decF hv hnd hF, card_roots_decF hv hnd,
        jumpL, ite_eq_right hk, sum_map_flatMap, ← List.sum_map_mul_left]
      congr 1; refine List.map_congr_left fun p hp => ?_
      obtain ⟨ha, hb, hne⟩ := roots_pair_of_mem_pairsL hv hnd hp
      have hv' : Valid n ((p.1 ||| p.2) :: F) := fun c hc =>
        (List.mem_cons.1 hc).elim (fun h => h ▸ Nat.or_lt_two_pow
          (valid_rootsL hv _ (mem_pairsL hp).1) (valid_rootsL hv _ (mem_pairsL hp).2)) (hv c)
      have hnd' : ((p.1 ||| p.2) :: F).Nodup :=
        List.nodup_cons.2 ⟨fun h => union_not_mem_of_mem_roots ha hb hne
          (decC_or n p.1 p.2 ▸ decC_mem_decF h), hnd⟩
      rw [jumpMatrix_pow_decF j _ hv' hnd' (by rw [decF_merge]; exact hF.isForest_merge ha hb) G,
        ← List.sum_map_mul_left, List.map_map]
      congr 1; refine List.map_congr_left fun q _ => ?_
      simp only [Function.comp_apply]; split_ifs <;> push_cast <;> ring

theorem sum_range_eq_list {M : Type*} [AddCommMonoid M] (k : ℕ) (f : ℕ → M) :
    ∑ j ∈ range k, f j = ((List.range k).map f).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

theorem sum_mul_sum_list {α β : Type*} (A : List α) (B : List β) (f : α → ℝ) (g : β → ℝ) :
    (A.map f).sum * (B.map g).sum = (A.map fun a => (B.map fun b => f a * g b).sum).sum := by
  rw [← List.sum_map_mul_right]
  congr 1; exact List.map_congr_left fun _ _ => (List.sum_map_mul_left ..).symm

def isForestB (F : List ℕ) : Bool :=
  F.all (· != 0) && F.all fun c => F.all fun d => (c &&& d == c) || (c &&& d == d) || (c &&& d == 0)

theorem isForest_of_isForestB {n : ℕ} {F : List ℕ} (hv : Valid n F) (h : isForestB F = true) :
    IsForest (decF n F) := by
  simp only [isForestB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.or_eq_true, beq_iff_eq] at h
  refine ⟨fun A hA => let ⟨c, hc, hAc⟩ := mem_decF.1 hA; hAc ▸ (decC_nonempty_iff (hv c hc)).2 (h.1 c hc),
    fun A hA B hB => ?_⟩
  obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA
  obtain ⟨d, hd, rfl⟩ := mem_decF.1 hB
  rcases h.2 c hc d hd with (h1 | h2) | h3
  · exact Or.inl ((decC_subset_iff (hv c hc)).2 h1)
  · exact Or.inr (Or.inl ((decC_subset_iff (hv d hd)).2 (Nat.and_comm d c ▸ h2)))
  · exact Or.inr (Or.inr ((decC_disjoint_iff (hv c hc)).2 h3))

def checkF (n : ℕ) (F : List ℕ) : Bool := decide (Valid n F) && decide F.Nodup && isForestB F

theorem of_checkF {n : ℕ} {F : List ℕ} (h : checkF n F = true) :
    Valid n F ∧ F.Nodup ∧ IsForest (decF n F) := by
  simp only [checkF, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, isForest_of_isForestB h.1.1 h.2⟩

def unrootL (m : ℕ) (F : List ℕ) : List ℕ :=
  (F.filter (· % 2 ^ m != 2 ^ m - 1)) ++ (F.filter (· % 2 ^ m != 2 ^ m - 1)).map ((2 ^ m - 1) ^^^ ·)

theorem decF_unrootL (m : ℕ) (F : List ℕ) :
    decF m (unrootL m F) = unroot (decF m F) := by
  have hu (c) : c % 2 ^ m = 2 ^ m - 1 ↔ decC m c = univ := by
    rw [← decC_mod m c, decC_eq_univ_iff (Nat.mod_lt _ (by positivity))]
  have h1 : decF m (F.filter (· % 2 ^ m != 2 ^ m - 1)) = (decF m F).erase univ := by
    ext A; simp only [mem_decF, List.mem_filter, bne_iff_ne, ne_eq, hu, mem_erase]; aesop
  have h2 (l) : decF m (l.map ((2 ^ m - 1) ^^^ ·)) = (decF m l).image compl := by
    induction l <;> simp [decF_cons, ← decC_compl, *]; rfl
  rw [unrootL, decF_append, h1, h2, h1, unroot]

def sampledL (n a : ℕ) : List ℕ :=
  ((List.finRange n).filter fun l : Fin n => a.testBit l).map (2 ^ ·.val)

theorem decF_sampledL (n a : ℕ) :
    decF n (sampledL n a) = sampledForest id (decC n a) := by
  ext A
  simp only [mem_decF, sampledL, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    sampledForest, mem_image, mem_filter, mem_univ, mem_decC, id_eq]
  exact ⟨fun ⟨_, ⟨l, hl, rfl⟩, hA⟩ => ⟨l, hl, hA ▸ (decC_two_pow l.2).symm⟩,
    fun ⟨l, hl, hA⟩ => ⟨_, ⟨l, hl, rfl⟩, hA ▸ decC_two_pow l.2⟩⟩

def flatMapO {α β : Type*} (f : α → Option (List β)) : List α → Option (List β)
  | [] => some []
  | a :: l => match f a, flatMapO f l with
    | some x, some y => some (x ++ y)
    | _, _ => none

theorem sum_flatMapO {α β : Type*} {f : α → Option (List β)} {l : List α} {M : List β}
    (h : flatMapO f l = some M) (w : β → ℝ) (v : α → ℝ)
    (hv : ∀ a ∈ l, ∀ x, f a = some x → (x.map w).sum = v a) :
    (M.map w).sum = (l.map v).sum := by
  induction l generalizing M with
  | nil => simp only [flatMapO, Option.some.injEq] at h; subst h; simp
  | cons a l ih =>
    simp only [flatMapO] at h
    split at h
    · rename_i x y hx hy
      cases h
      rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        hv a (List.mem_cons_self ..) x hx,
        ih hy fun b hb => hv b (List.mem_cons_of_mem _ hb)]
    · simp at h



variable {X : Type*} [Fintype X] [DecidableEq X] {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The image of a family of clusters under a bijection. -/
def relabelFamily (e : X ≃ Y) (F : Finset (Finset X)) : Finset (Finset Y) :=
  F.image fun A => A.map e.toEmbedding

lemma msc_map_symm_map (e : X ≃ Y) (A : Finset X) :
    (A.map e.toEmbedding).map e.symm.toEmbedding = A := by
  ext x; simp

theorem msc_map_compl (e : X ≃ Y) (A : Finset X) :
    (A.map e.toEmbedding)ᶜ = Aᶜ.map e.toEmbedding := by
  ext y; simp [Finset.mem_map_equiv]

private lemma msc_map_eq_univ_iff (e : X ≃ Y) (A : Finset X) :
    A.map e.toEmbedding = univ ↔ A = univ := by
  rw [← Finset.map_univ_equiv e, Finset.map_inj]

theorem relabelFamily_injective (e : X ≃ Y) : Function.Injective (relabelFamily e) :=
  Finset.image_injective (Finset.map_injective e.toEmbedding)

theorem relabelFamily_symm (e : X ≃ Y) (F : Finset (Finset X)) :
    relabelFamily e.symm (relabelFamily e F) = F := by
  unfold relabelFamily
  rw [image_image]
  conv_rhs => rw [← image_id (s := F)]
  exact congrArg (image · F) (funext (msc_map_symm_map e))

theorem unroot_relabelFamily (e : X ≃ Y) (F : Finset (Finset X)) :
    unroot (relabelFamily e F) = relabelFamily e (unroot F) := by
  have herase : (relabelFamily e F).erase univ = relabelFamily e (F.erase univ) := by
    unfold relabelFamily
    rw [Finset.image_erase (Finset.map_injective e.toEmbedding), Finset.map_univ_equiv]
  unfold unroot; rw [herase]; unfold relabelFamily
  rw [image_union, image_image, image_image]
  congr 2; exact funext (msc_map_compl e)

def relabelFamilyEquiv (e : X ≃ Y) : Finset (Finset X) ≃ Finset (Finset Y) where
  toFun := relabelFamily e
  invFun := relabelFamily e.symm
  left_inv := relabelFamily_symm e
  right_inv F := by simpa using relabelFamily_symm e.symm F

@[simp] theorem relabelFamilyEquiv_apply (e : X ≃ Y) (F : Finset (Finset X)) :
    relabelFamilyEquiv e F = relabelFamily e F := rfl

theorem mem_relabelFamily {e : X ≃ Y} {F : Finset (Finset X)} {B : Finset Y} :
    B ∈ relabelFamily e F ↔ B.map e.symm.toEmbedding ∈ F := by
  unfold relabelFamily; rw [mem_image]
  exact ⟨by rintro ⟨A, hA, rfl⟩; rwa [msc_map_symm_map],
    fun h => ⟨_, h, by simpa using msc_map_symm_map e.symm B⟩⟩

theorem map_mem_relabelFamily {e : X ≃ Y} {F : Finset (Finset X)} {A : Finset X} :
    A.map e.toEmbedding ∈ relabelFamily e F ↔ A ∈ F := by
  rw [mem_relabelFamily, msc_map_symm_map]

theorem roots_relabelFamily (e : X ≃ Y) (F : Finset (Finset X)) :
    roots (relabelFamily e F) = relabelFamily e (roots F) := by
  unfold roots relabelFamily
  rw [filter_image]
  congr 1
  refine filter_congr fun A _ => ?_
  rw [Finset.forall_mem_image]
  exact ⟨fun h B hB hAB => Finset.map_injective _ (h hB (Finset.map_subset_map.2 hAB)),
    fun h B hB hAB => by rw [h B hB (Finset.map_subset_map.1 hAB)]⟩

theorem kingmanGenerator_relabelFamily (e : X ≃ Y) (F G : Finset (Finset X)) :
    kingmanGenerator (relabelFamily e F) (relabelFamily e G) = kingmanGenerator F G := by
  unfold kingmanGenerator
  rw [roots_relabelFamily, show #(relabelFamily e (roots F)) = #(roots F) from
    card_image_of_injective _ (Finset.map_injective e.toEmbedding)]
  by_cases hGF : G = F
  · subst hGF; simp
  · rw [ite_eq_right (fun h => hGF (relabelFamily_injective e h)), ite_eq_right hGF]
    refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro ⟨A', hA', B', hB', hAB', hF⟩
      obtain ⟨A, hA, rfl⟩ := mem_image.1 hA'
      obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
      refine ⟨A, hA, B, hB, fun h => hAB' (h ▸ rfl), relabelFamily_injective e ?_⟩
      rw [hF]; unfold relabelFamily; rw [image_insert, Finset.map_union]
    · rintro ⟨A, hA, B, hB, hAB, rfl⟩
      refine ⟨A.map e.toEmbedding, mem_image_of_mem _ hA, B.map e.toEmbedding,
        mem_image_of_mem _ hB, fun h => hAB (Finset.map_injective _ h), ?_⟩
      unfold relabelFamily; rw [image_insert, Finset.map_union]

theorem kingmanTransition_relabelFamily (e : X ≃ Y) (t : ℝ) (F G : Finset (Finset X)) :
    kingmanTransition t (relabelFamily e F) (relabelFamily e G) = kingmanTransition t F G := by
  let π := relabelFamilyEquiv e
  let A := t • kingmanGenerator (L := Y)
  have hQ : A.submatrix π π = t • kingmanGenerator (L := X) := by
    ext F' G'; exact congrArg (t * ·) (kingmanGenerator_relabelFamily e F' G')
  have hpow (k : ℕ) : (A.submatrix π π) ^ k = (A ^ k).submatrix π π := by
    induction k with
    | zero => simp [Matrix.submatrix_one_equiv]
    | succ k ih => rw [pow_succ, ih, Matrix.submatrix_mul_equiv, pow_succ]
  unfold kingmanTransition
  rw [← hQ]
  exact (fact_hasSum_exp_apply A (relabelFamily e F) (relabelFamily e G)).unique
    (by simpa only [hpow, Matrix.submatrix_apply, π, relabelFamilyEquiv_apply] using
      fact_hasSum_exp_apply (A.submatrix π π) F G)

theorem childClusters_relabelFamily (e : X ≃ Y) (H : Finset (Finset X)) (A : Finset X) :
    childClusters (relabelFamily e H) (A.map e.toEmbedding) =
      relabelFamily e (childClusters H A) := by
  unfold childClusters relabelFamily
  rw [filter_image]
  congr 1
  exact filter_congr fun B _ => by simp only [Finset.map_ssubset_map, Finset.forall_mem_image]

theorem sampledForest_relabel (e : X ≃ Y) (A : Finset X) :
    sampledForest id (A.map e.toEmbedding) = relabelFamily e (sampledForest id A) := by
  ext C; simp only [mem_sampledForest, id_eq, mem_relabelFamily, Finset.mem_map_equiv]
  exact ⟨by rintro ⟨y, hy, rfl⟩; exact ⟨e.symm y, hy, by simp⟩,
    by rintro ⟨x, hx, hC⟩; exact ⟨e x, by simpa using hx,
      by rw [← msc_map_symm_map e.symm C, Equiv.symm_symm, ← hC]; simp⟩⟩

def SpeciesTree.relabel (σ : SpeciesTree X) (e : X ≃ Y) : SpeciesTree Y where
  clusters := relabelFamily e σ.clusters
  univ_mem := mem_image.2 ⟨univ, σ.univ_mem, Finset.map_univ_equiv e⟩
  singleton_mem y := mem_image.2 ⟨{e.symm y}, σ.singleton_mem _, by simp⟩
  nonempty_of_mem B hB := by
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    exact Finset.map_nonempty.2 (σ.nonempty_of_mem A hA)
  laminar B hB C hC := by
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    obtain ⟨A', hA', rfl⟩ := mem_image.1 hC
    rw [Finset.map_subset_map, Finset.map_subset_map, Finset.disjoint_map]
    exact σ.laminar A hA A' hA'
  length B := σ.length (B.map e.symm.toEmbedding)
  length_pos B hB hBu := by
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    rw [msc_map_symm_map]
    exact σ.length_pos A hA fun h => hBu ((msc_map_eq_univ_iff e A).2 h)

@[simp] theorem SpeciesTree.relabel_clusters (σ : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).clusters = relabelFamily e σ.clusters := rfl

@[simp] theorem SpeciesTree.relabel_length_map (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).length (A.map e.toEmbedding) = σ.length A :=
  congrArg σ.length (msc_map_symm_map e A)

theorem forestDist_relabel (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X)
    (G : Finset (Finset X)) :
    forestDist (relabelFamily e σ.clusters) (σ.relabel e).length id
      (A.map e.toEmbedding) (relabelFamily e G) =
      forestDist σ.clusters σ.length id A G := by
  induction A using Finset.strongInduction generalizing G with
  | H A ih =>
  rw [forestDist.eq_1 (relabelFamily e σ.clusters), forestDist.eq_1 σ.clusters]
  let ψ : childClusters σ.clusters A ≃
      childClusters (relabelFamily e σ.clusters) (A.map e.toEmbedding) :=
    (Equiv.finsetCongr e).subtypeEquiv fun B => by
      rw [childClusters_relabelFamily, Equiv.finsetCongr_apply, map_mem_relabelFamily]
  let Φ := ψ.arrowCongr (relabelFamilyEquiv e)
  rw [← Φ.sum_comp]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hΦ (B : childClusters σ.clusters A) : Φ f (ψ B) = relabelFamily e (f B) := by
    simp [Φ, Equiv.arrowCongr_apply]
  congr 1
  · rw [← ψ.prod_comp]
    exact Finset.prod_congr rfl fun B _ => by
      rw [hΦ]; exact ih B (mem_childClusters.1 B.2).2.1 (f B)
  · have hsup : univ.sup (Φ f) = relabelFamily e (univ.sup f) := by
      rw [Finset.apply_sup_eq_sup_comp (relabelFamily e) (fun _ _ => image_union _ _) (image_empty _),
        ← Finset.map_univ_equiv ψ, Finset.sup_map]
      exact Finset.sup_congr rfl fun B _ => hΦ B
    rw [hsup, sampledForest_relabel, show relabelFamily e (univ.sup f) ∪
      relabelFamily e (sampledForest id A) = relabelFamily e (univ.sup f ∪ sampledForest id A) from
      (image_union _ _).symm]
    unfold populationKernel
    by_cases hA : A = univ
    · rw [ite_eq_left ((msc_map_eq_univ_iff e A).2 hA), ite_eq_left hA]
      unfold kingmanAbsorption; simp_rw [kingmanTransition_relabelFamily]
    · rw [ite_eq_right (mt (msc_map_eq_univ_iff e A).1 hA), ite_eq_right hA,
        σ.relabel_length_map, kingmanTransition_relabelFamily]

theorem SpeciesTree.isBinary_relabel {σ : SpeciesTree X} (e : X ≃ Y) (h : σ.IsBinary) :
    (σ.relabel e).IsBinary := by
  intro B hB hB2
  obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
  rw [Finset.card_map] at hB2
  obtain ⟨C, hC, D, hD, hCD, hCDA⟩ := h A hA hB2
  refine ⟨C.map e.toEmbedding, mem_image_of_mem _ hC, D.map e.toEmbedding, mem_image_of_mem _ hD,
    (Finset.disjoint_map _).2 hCD, ?_⟩
  rw [← Finset.map_union, hCDA]

theorem SpeciesTree.unrootedDist_relabel (σ : SpeciesTree X) (e : X ≃ Y)
    (T : Finset (Finset X)) :
    (σ.relabel e).unrootedDist id (relabelFamily e T) = σ.unrootedDist id T := by
  unfold SpeciesTree.unrootedDist
  rw [← (relabelFamilyEquiv e).sum_comp]
  refine Finset.sum_congr rfl fun G _ => ?_
  have hr : (σ.relabel e).rootedDist id (relabelFamily e G) = σ.rootedDist id G := by
    simpa [SpeciesTree.rootedDist, Finset.map_univ_equiv] using forestDist_relabel σ e univ G
  simp only [relabelFamilyEquiv_apply, unroot_relabelFamily, (relabelFamily_injective e).eq_iff, hr]

theorem SpeciesTree.unrootedDist_relabel_eq_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).unrootedDist id = (σ'.relabel e).unrootedDist id ↔
      σ.unrootedDist id = σ'.unrootedDist id := by
  constructor
  · intro h
    funext T
    have := congrFun h (relabelFamily e T)
    rwa [SpeciesTree.unrootedDist_relabel, SpeciesTree.unrootedDist_relabel] at this
  · intro h
    funext T
    obtain ⟨T₀, rfl⟩ := (relabelFamilyEquiv e).surjective T
    rw [relabelFamilyEquiv_apply, SpeciesTree.unrootedDist_relabel,
      SpeciesTree.unrootedDist_relabel, h]

theorem SpeciesTree.sameRootedMetricTree_relabel_iff (σ σ' : SpeciesTree X) (e : X ≃ Y) :
    (σ.relabel e).SameRootedMetricTree (σ'.relabel e) ↔ σ.SameRootedMetricTree σ' := by
  unfold SpeciesTree.SameRootedMetricTree
  refine and_congr (relabelFamily_injective e).eq_iff ⟨fun h A hA hA2 hAu => ?_,
    fun h B hB hB2 hBu => ?_⟩
  · have := h (A.map e.toEmbedding) (map_mem_relabelFamily.2 hA) (by rwa [Finset.card_map])
      fun h' => hAu ((msc_map_eq_univ_iff e A).1 h')
    rwa [SpeciesTree.relabel_length_map, SpeciesTree.relabel_length_map] at this
  · obtain ⟨A, hA, rfl⟩ := mem_image.1 hB
    rw [SpeciesTree.relabel_length_map, SpeciesTree.relabel_length_map]
    exact h A hA (by rwa [Finset.card_map] at hB2) fun h' => hBu ((msc_map_eq_univ_iff e A).2 h')

theorem SpeciesTree.unrootedLength_relabel (σ : SpeciesTree X) (e : X ≃ Y) (A : Finset X) :
    (σ.relabel e).unrootedLength (A.map e.toEmbedding) = σ.unrootedLength A := by
  unfold SpeciesTree.unrootedLength
  rw [SpeciesTree.relabel_clusters]
  unfold relabelFamily
  rw [filter_image, sum_image fun x _ y _ h => Finset.map_injective _ h]
  refine Finset.sum_congr (filter_congr fun C _ => ?_) fun C _ =>
    SpeciesTree.relabel_length_map σ e C
  simp only [ne_eq, msc_map_eq_univ_iff, Finset.map_inj, msc_map_compl]

abbrev h4 (cs : List ℕ) : Finset (Finset (Fin 4)) := hierarchyOf (decF 4 cs)
abbrev h5 (cs : List ℕ) : Finset (Finset (Fin 5)) := hierarchyOf (decF 5 cs)

def U4 : ℕ → Finset (Finset (Fin 4))
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

def U5 : ℕ → Finset (Finset (Fin 5))
  | 2 => treeOfClusters {{0, 1}, {3, 4}}
  | 1 => treeOfClusters {{0, 1}}
  | _ => treeOfClusters ∅

def rootings4 : ℕ → Finset (Finset (Finset (Fin 4)))
  | 1 => {h4 [3, 7], h4 [3, 11], h4 [12, 13], h4 [12, 14], h4 [3, 12], h4 [3], h4 [12]}
  | _ => {h4 [], h4 [7], h4 [11], h4 [13], h4 [14]}

def rootings5 : ℕ → Finset (Finset (Finset (Fin 5)))
  | 2 => {h5 [3, 7, 15], h5 [3, 7, 23], h5 [24, 28, 30], h5 [24, 28, 29], h5 [3, 24, 27],
          h5 [24, 3, 7], h5 [3, 24, 28], h5 [3, 24], h5 [3, 7], h5 [24, 28]}
  | 1 => {h5 [3], h5 [28], h5 [3, 28], h5 [28, 30], h5 [28, 29], h5 [3, 27], h5 [3, 23],
          h5 [3, 15]}
  | _ => {h5 [], h5 [30], h5 [29], h5 [27], h5 [23], h5 [15]}

theorem classify_card_of_mem_unroot (σ : SpeciesTree X) {A : Finset X}
    (h : A ∈ unroot σ.clusters) : 1 ≤ #A ∧ #A < Fintype.card X := by
  rcases mem_unroot.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨(σ.nonempty_of_mem A h1).card_pos, (card_lt_iff_ne_univ A).2 h2⟩
  · have h3 := (σ.nonempty_of_mem _ h1).card_pos
    have h4 := (card_lt_iff_ne_univ _).2 h2
    rw [card_compl] at h3 h4
    have := card_le_univ A; omega

theorem classify_singleton_mem_unroot (hX : 2 ≤ Fintype.card X) (σ : SpeciesTree X) (x : X) :
    {x} ∈ unroot σ.clusters := by
  refine mem_unroot.2 (Or.inl ⟨σ.singleton_mem x, fun h => ?_⟩)
  have := congrArg card h; rw [card_singleton, card_univ] at this; omega

theorem classify_mem_unroot_iff (hX : Fintype.card X = 4 ∨ Fintype.card X = 5)
    (σ : SpeciesTree X) (A : Finset X) :
    A ∈ unroot σ.clusters ↔ #A = 1 ∨ #A = Fintype.card X - 1 ∨
      A ∈ (unroot σ.clusters).filter (fun B => #B = 2) ∨
      Aᶜ ∈ (unroot σ.clusters).filter (fun B => #B = 2) := by
  have h2 : 2 ≤ Fintype.card X := by omega
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := classify_card_of_mem_unroot σ h
    have hc := card_compl A
    rcases (by omega : #A = 1 ∨ #A = Fintype.card X - 1 ∨ #A = 2 ∨ #Aᶜ = 2) with
      h3 | h3 | h3 | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr (Or.inl (mem_filter.2 ⟨h, h3⟩)))
    · exact Or.inr (Or.inr (Or.inr (mem_filter.2 ⟨compl_mem_unroot.2 h, h3⟩)))
  · rintro (h | h | h | h)
    · obtain ⟨x, rfl⟩ := card_eq_one.1 h; exact classify_singleton_mem_unroot h2 σ x
    · obtain ⟨x, hx⟩ := card_eq_one.1 (show #Aᶜ = 1 by rw [card_compl]; omega)
      rw [← compl_mem_unroot, hx]; exact classify_singleton_mem_unroot h2 σ x
    · exact (mem_filter.1 h).1
    · exact compl_mem_unroot.1 (mem_filter.1 h).1

theorem classify_unroot_relabel_eq {n : ℕ} (hX : Fintype.card X = n) (σ : SpeciesTree X)
    (e : Fin n ≃ X) (U T : Finset (Finset (Fin n)))
    (hP : (unroot σ.clusters).filter (fun B => #B = 2) = relabelFamily e T)
    (hU : ∀ A ∈ (univ : Finset (Finset (Fin n))),
      A ∈ U ↔ #A = 1 ∨ #A = n - 1 ∨ A ∈ T ∨ Aᶜ ∈ T := by decide +kernel)
    (hn : n = 4 ∨ n = 5 := by decide) :
    unroot (σ.relabel e.symm).clusters = U := by
  show unroot (relabelFamily e.symm σ.clusters) = U
  rw [unroot_relabelFamily]
  ext A
  rw [mem_relabelFamily, Equiv.symm_symm, classify_mem_unroot_iff (by omega) σ,
    hU A (mem_univ A), hP, card_map, hX, mem_relabelFamily, mem_relabelFamily,
    ← msc_map_compl, msc_map_symm_map]

theorem classify_disjoint_of_card_two (hX : Fintype.card X = 5) (σ : SpeciesTree X)
    {A B : Finset X} (hA : A ∈ unroot σ.clusters) (hB : B ∈ unroot σ.clusters) (hA2 : #A = 2)
    (hB2 : #B = 2) (hAB : A ≠ B) : Disjoint A B := by
  have hAc : #Aᶜ = 3 := by rw [card_compl, hX, hA2]
  rcases laminar_of_mem_unroot σ hA hB with h | h | h | h
  · exact (hAB (eq_of_subset_of_card_le h (by omega))).elim
  · exact (hAB (eq_of_subset_of_card_le h (by omega)).symm).elim
  · exact h
  · have := card_le_card h; omega

theorem classify_card_pairs_le (hX : Fintype.card X = 5) (σ : SpeciesTree X) :
    #((unroot σ.clusters).filter (fun A => #A = 2)) ≤ 2 := by
  by_contra h
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.1 (not_le.1 h)
  rw [mem_filter] at ha hb hc
  have hd {A B} (hA : A ∈ unroot σ.clusters ∧ #A = 2) (hB : B ∈ unroot σ.clusters ∧ #B = 2) :=
    classify_disjoint_of_card_two hX σ hA.1 hB.1 hA.2 hB.2
  have h6 : #(a ∪ b ∪ c) = 6 := by
    rw [card_union_of_disjoint (disjoint_union_left.2 ⟨hd ha hc hac, hd hb hc hbc⟩),
      card_union_of_disjoint (hd ha hb hab), ha.2, hb.2, hc.2]
  have := card_le_univ (a ∪ b ∪ c); omega

theorem classify_eq_or_eq_compl_of_card_two (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    {A B : Finset X} (hA : A ∈ unroot σ.clusters) (hB : B ∈ unroot σ.clusters) (hA2 : #A = 2)
    (hB2 : #B = 2) : B = A ∨ B = Aᶜ := by
  have hAc : #Aᶜ = 2 := by rw [card_compl, hX, hA2]
  rcases laminar_of_mem_unroot σ hA hB with h | h | h | h
  · exact Or.inl (eq_of_subset_of_card_le h (by omega)).symm
  · exact Or.inl (eq_of_subset_of_card_le h (by omega))
  · exact Or.inr (eq_of_subset_of_card_le (subset_compl_iff_disjoint_left.2 h) (by omega))
  · exact Or.inr (eq_of_subset_of_card_le h (by omega)).symm

theorem classify_exists_equiv {n : ℕ} (hX : Fintype.card X = n) (f : Fin n → X)
    (hf : Function.Injective f := by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all) :
    ∃ e : Fin n ≃ X, ∀ i, e i = f i :=
  ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp [hX]⟩),
    fun _ => rfl⟩

theorem classify_eq_hierarchyOf {H : Finset (Finset X)} (hH : IsHierarchy H) :
    H = hierarchyOf (H.filter fun A => 2 ≤ #A ∧ A ≠ univ) := by
  ext A
  simp only [hierarchyOf, mem_insert, mem_union, mem_image, mem_univ, true_and, mem_filter]
  refine ⟨fun hA => (eq_or_ne A univ).imp_right fun hu => ?_, ?_⟩
  · by_cases h2 : 2 ≤ #A
    · exact Or.inl ⟨hA, h2, hu⟩
    · obtain ⟨x, rfl⟩ := card_eq_one.1 (show #A = 1 by have := (hH.2.2.1 A hA).card_pos; omega)
      exact Or.inr ⟨x, rfl⟩
  · rintro (rfl | ⟨hA, -⟩ | ⟨x, rfl⟩); exacts [hH.1, hA, hH.2.1 x]

theorem classify_mem_of_forall {τ : SpeciesTree X} {U : Finset (Finset X)}
    {R : Finset (Finset (Finset X))}
    (hdec : ∀ N ∈ (U.filter fun A => 2 ≤ #A).powerset,
      (∀ A ∈ N, ∀ B ∈ N, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) →
      (∀ A ∈ U, 2 ≤ #A → 2 ≤ #Aᶜ → A ∈ N ∨ Aᶜ ∈ N) → hierarchyOf N ∈ R)
    (h : unroot τ.clusters = U) : τ.clusters ∈ R := by
  rw [classify_eq_hierarchyOf τ.isHierarchy]
  refine hdec _ (mem_powerset.2 fun A hA => ?_)
    (fun A hA B hB => τ.laminar A (mem_filter.1 hA).1 B (mem_filter.1 hB).1)
    fun A hAU h2 h2c => ?_
  · obtain ⟨h1, h2, h3⟩ := mem_filter.1 hA
    exact mem_filter.2 ⟨h ▸ mem_unroot.2 (Or.inl ⟨h1, h3⟩), h2⟩
  · rcases mem_unroot.1 (h ▸ hAU) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
    · exact Or.inl (mem_filter.2 ⟨h1, h2, h1'⟩)
    · exact Or.inr (mem_filter.2 ⟨h1, h2c, h1'⟩)

section Decide

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype
set_option synthInstance.maxSize 10000

theorem classify_mem_rootings5 (τ : SpeciesTree (Fin 5)) (k : ℕ)
    (hk : k ∈ ({0, 1, 2} : Finset ℕ)) (h : unroot τ.clusters = U5 k) :
    τ.clusters ∈ rootings5 k := by
  refine classify_mem_of_forall ?_ h; clear h τ; revert k hk; decide +kernel

theorem mem_rootings4 (τ : SpeciesTree (Fin 4)) (k : ℕ) (hk : k ∈ ({0, 1} : Finset ℕ))
    (h : unroot τ.clusters = U4 k) : τ.clusters ∈ rootings4 k := by
  refine classify_mem_of_forall ?_ h; clear h τ; revert k hk; decide +kernel

theorem exists_equiv_unroot_eq_U4 (hX : Fintype.card X = 4) (σ : SpeciesTree X) :
    ∃ e : Fin 4 ≃ X, ∃ k ∈ ({0, 1} : Finset ℕ), unroot (σ.relabel e.symm).clusters = U4 k := by
  set P := (unroot σ.clusters).filter (fun A => #A = 2) with hPdef
  rcases P.eq_empty_or_nonempty with hP | ⟨A, hA⟩
  · exact ⟨(Fintype.equivFinOfCardEq hX).symm, 0, by simp,
      classify_unroot_relabel_eq hX σ _ _ ∅ (by rw [← hPdef, hP]; simp [relabelFamily])⟩
  · rw [mem_filter] at hA
    have hAc2 : #Aᶜ = 2 := by rw [card_compl, hX, hA.2]
    have hP : P = {A, Aᶜ} := by
      ext B; rw [mem_filter, mem_insert, mem_singleton]
      exact ⟨fun ⟨hB, hB2⟩ => classify_eq_or_eq_compl_of_card_two hX σ hA.1 hB hA.2 hB2,
        by rintro (rfl | rfl); exacts [hA, ⟨compl_mem_unroot.2 hA.1, hAc2⟩]⟩
    obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.1 hA.2
    obtain ⟨r, s, hrs, hrsA⟩ := card_eq_two.1 hAc2
    have : Disjoint {p, q} {r, s} := hrsA ▸ disjoint_compl_right
    obtain ⟨e, he⟩ := classify_exists_equiv hX ![p, q, r, s]
    exact ⟨e, 1, by simp, classify_unroot_relabel_eq hX σ e _ {{0, 1}, {2, 3}}
      (by rw [← hPdef, hP, hrsA]; simp [relabelFamily, he])⟩

theorem exists_equiv_unroot_eq_U5 (hX : Fintype.card X = 5) (σ : SpeciesTree X) :
    ∃ e : Fin 5 ≃ X, ∃ k ∈ ({0, 1, 2} : Finset ℕ),
      unroot (σ.relabel e.symm).clusters = U5 k := by
  have hle := classify_card_pairs_le hX σ
  set P := (unroot σ.clusters).filter (fun A => #A = 2) with hPdef
  have hPmem (A) (hA : A ∈ P) : A ∈ unroot σ.clusters ∧ #A = 2 := mem_filter.1 hA
  rcases (by omega : #P = 0 ∨ #P = 1 ∨ #P = 2) with hc | hc | hc
  · exact ⟨(Fintype.equivFinOfCardEq hX).symm, 0, by simp,
      classify_unroot_relabel_eq hX σ _ _ ∅ (by rw [← hPdef, card_eq_zero.1 hc]; simp [relabelFamily])⟩
  · obtain ⟨A, hA⟩ := card_eq_one.1 hc
    obtain ⟨-, hA2⟩ := hPmem A (hA ▸ mem_singleton_self A)
    obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.1 hA2
    obtain ⟨a, b, c, hab, hac, hbc, habc⟩ := card_eq_three.1 (show #({p, q} : Finset X)ᶜ = 3 by rw [card_compl, hX, hA2])
    have : Disjoint {p, q} {a, b, c} := habc ▸ disjoint_compl_right
    obtain ⟨e, he⟩ := classify_exists_equiv hX ![p, q, a, b, c]
    exact ⟨e, 1, by simp, classify_unroot_relabel_eq hX σ e _ {{0, 1}}
      (by rw [← hPdef, hA]; simp [relabelFamily, he])⟩
  · obtain ⟨A, B, hAB, hP⟩ := card_eq_two.1 hc
    have hA := hPmem A (by rw [hP]; simp)
    have hB := hPmem B (by rw [hP]; simp)
    have hd := classify_disjoint_of_card_two hX σ hA.1 hB.1 hA.2 hB.2 hAB
    obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.1 hA.2
    obtain ⟨r, s, hrs, rfl⟩ := card_eq_two.1 hB.2
    obtain ⟨m, hm⟩ := card_eq_one.1 (show #({p, q} ∪ {r, s} : Finset X)ᶜ = 1 by
      rw [card_compl, card_union_of_disjoint hd, hA.2, hB.2, hX])
    have : m ∉ ({p, q} ∪ {r, s} : Finset X) := by rw [← mem_compl, hm]; simp
    obtain ⟨e, he⟩ := classify_exists_equiv hX ![p, q, m, r, s]
    exact ⟨e, 2, by simp, classify_unroot_relabel_eq hX σ e _ {{0, 1}, {3, 4}}
      (by rw [← hPdef, hP]; simp [relabelFamily, he])⟩

end Decide

end ADR11
