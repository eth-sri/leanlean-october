module

public import ADR11.MSC.Basic

@[expose] public section

namespace ADR11

open Finset Real

variable {n : ℕ}

def decC (n c : ℕ) : Finset (Fin n) := univ.filter fun i => c.testBit i

def decF (n : ℕ) (l : List ℕ) : Finset (Finset (Fin n)) := (l.map (decC n)).toFinset

def Valid (n : ℕ) (l : List ℕ) : Prop := ∀ c ∈ l, c < 2 ^ n

instance (n : ℕ) (l : List ℕ) : Decidable (Valid n l) :=
  inferInstanceAs (Decidable (∀ c ∈ l, c < 2 ^ n))

theorem mem_decC {c : ℕ} {i : Fin n} : i ∈ decC n c ↔ c.testBit i = true := by
  simp [decC]

theorem testBit_iff_mem_decC {a : ℕ} (ha : a < 2 ^ n) (i : ℕ) :
    a.testBit i = true ↔ ∃ hi : i < n, (⟨i, hi⟩ : Fin n) ∈ decC n a := by
  simp only [mem_decC]
  refine ⟨fun h => ⟨by_contra fun hi => ?_, h⟩, fun ⟨_, h⟩ => h⟩
  have := Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)))
  simp [this] at h

theorem decC_inj {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    decC n a = decC n b ↔ a = b := by
  refine ⟨fun h => Nat.eq_of_testBit_eq fun i => Bool.eq_iff_iff.2 ?_, fun h => h ▸ rfl⟩
  rw [testBit_iff_mem_decC ha, testBit_iff_mem_decC hb, h]

theorem decC_or (n a b : ℕ) : decC n (a ||| b) = decC n a ∪ decC n b := by
  ext i; simp [mem_decC]

theorem decC_subset_iff {a b : ℕ} (ha : a < 2 ^ n) :
    decC n a ⊆ decC n b ↔ a &&& b = a := by
  refine ⟨fun h => Nat.eq_of_testBit_eq fun i => Bool.eq_iff_iff.2 ?_, fun h i hi => ?_⟩
  · simp only [Nat.testBit_and, Bool.and_eq_true, and_iff_left_iff_imp, testBit_iff_mem_decC ha]
    rintro ⟨hi, hia⟩; exact mem_decC.1 (h hia)
  · simpa [mem_decC, Nat.testBit_and, mem_decC.1 hi] using congrArg (·.testBit i) h

theorem decC_nonempty_of_ne_zero {a : ℕ} (ha : a < 2 ^ n) (h : a ≠ 0) :
    (decC n a).Nonempty := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
  obtain ⟨hin, hia⟩ := (testBit_iff_mem_decC ha i).1 hi
  exact ⟨⟨i, hin⟩, hia⟩

theorem decC_disjoint_of_and_eq_zero {a b : ℕ} (h : a &&& b = 0) :
    Disjoint (decC n a) (decC n b) :=
  disjoint_left.2 fun i hia hib => by
    simpa [Nat.testBit_and, mem_decC.1 hia, mem_decC.1 hib] using congrArg (·.testBit i) h

theorem decC_compl {a : ℕ} : (decC n a)ᶜ = decC n ((2 ^ n - 1) ^^^ a) := by
  ext i; simp [mem_decC, Nat.testBit_xor, i.2]

theorem decC_full (n : ℕ) : decC n (2 ^ n - 1) = univ := by
  ext i; simp [mem_decC, i.2]

theorem decC_eq_univ_iff {a : ℕ} (ha : a < 2 ^ n) : decC n a = univ ↔ a = 2 ^ n - 1 := by
  rw [← decC_full n, decC_inj ha (by have := Nat.one_le_two_pow (n := n); omega)]

theorem decC_two_pow {i : ℕ} (hi : i < n) : decC n (2 ^ i) = {⟨i, hi⟩} := by
  ext j; simp [mem_decC, Nat.testBit_two_pow, Fin.ext_iff, eq_comm]

theorem mem_decF {l : List ℕ} {A : Finset (Fin n)} :
    A ∈ decF n l ↔ ∃ c ∈ l, decC n c = A := by
  simp [decF]

theorem decC_mem_decF {l : List ℕ} {c : ℕ} (h : c ∈ l) : decC n c ∈ decF n l :=
  mem_decF.2 ⟨c, h, rfl⟩

theorem decF_cons (n c : ℕ) (l : List ℕ) : decF n (c :: l) = insert (decC n c) (decF n l) := by
  simp [decF]

theorem decF_append (n : ℕ) (l₁ l₂ : List ℕ) : decF n (l₁ ++ l₂) = decF n l₁ ∪ decF n l₂ := by
  simp [decF]

theorem decF_union (n : ℕ) (l₁ l₂ : List ℕ) : decF n (l₁ ∪ l₂) = decF n l₁ ∪ decF n l₂ := by
  ext A; simp [mem_decF, List.mem_union_iff, or_and_right, exists_or]

theorem decC_mem_decF_iff {l : List ℕ} (hl : Valid n l) {c : ℕ} (hc : c < 2 ^ n) :
    decC n c ∈ decF n l ↔ c ∈ l :=
  ⟨fun h => let ⟨d, hd, hdc⟩ := mem_decF.1 h; (decC_inj (hl d hd) hc).1 hdc ▸ hd, decC_mem_decF⟩

theorem decF_eq_iff {l₁ l₂ : List ℕ} (h₁ : Valid n l₁) (h₂ : Valid n l₂) :
    decF n l₁ = decF n l₂ ↔ (∀ c ∈ l₁, c ∈ l₂) ∧ ∀ c ∈ l₂, c ∈ l₁ := by
  refine ⟨fun h => ⟨fun c hc => ?_, fun c hc => ?_⟩, fun ⟨h, h'⟩ => ?_⟩
  · rw [← decC_mem_decF_iff h₂ (h₁ c hc), ← h]; exact decC_mem_decF hc
  · rw [← decC_mem_decF_iff h₁ (h₂ c hc), h]; exact decC_mem_decF hc
  · ext A; simp only [mem_decF]
    exact ⟨fun ⟨c, hc, e⟩ => ⟨c, h c hc, e⟩, fun ⟨c, hc, e⟩ => ⟨c, h' c hc, e⟩⟩

theorem card_decF {l : List ℕ} (hl : Valid n l) (hnd : l.Nodup) :
    #(decF n l) = l.length := by
  rw [decF, List.toFinset_card_of_nodup
    (hnd.map_on fun a ha b hb e => (decC_inj (hl a ha) (hl b hb)).1 e), List.length_map]

def rootsL (F : List ℕ) : List ℕ := F.filter fun c => F.all fun d => !(c &&& d == c) || d == c

theorem mem_rootsL {F : List ℕ} {c : ℕ} :
    c ∈ rootsL F ↔ c ∈ F ∧ ∀ d ∈ F, c &&& d = c → d = c := by
  simp only [rootsL, List.mem_filter, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, beq_iff_eq]
  exact ⟨fun ⟨hc, h⟩ => ⟨hc, fun d hd hcd => (h d hd).resolve_left (not_not.2 hcd)⟩,
    fun ⟨hc, h⟩ => ⟨hc, fun d hd => if hcd : c &&& d = c then Or.inr (h d hd hcd) else Or.inl hcd⟩⟩

theorem valid_rootsL {F : List ℕ} (hv : Valid n F) : Valid n (rootsL F) :=
  fun c hc => hv c (mem_rootsL.1 hc).1

theorem nodup_rootsL {F : List ℕ} (hnd : F.Nodup) : (rootsL F).Nodup := hnd.filter _

theorem decF_rootsL {F : List ℕ} (hv : Valid n F) :
    decF n (rootsL F) = roots (decF n F) := by
  ext A; simp only [roots, mem_filter]
  constructor
  · intro hA
    obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA
    rw [mem_rootsL] at hc
    refine ⟨decC_mem_decF hc.1, fun B hB hsub => ?_⟩
    obtain ⟨d, hd, rfl⟩ := mem_decF.1 hB
    rw [hc.2 d hd ((decC_subset_iff (hv c hc.1)).1 hsub)]
  · rintro ⟨hA, h⟩
    obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA
    exact decC_mem_decF (mem_rootsL.2 ⟨hc, fun d hd hcd => (decC_inj (hv d hd) (hv c hc)).1
      (h (decC n d) (decC_mem_decF hd) ((decC_subset_iff (hv c hc)).2 hcd))⟩)

theorem card_roots_decF {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup) :
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
    · rintro (rfl : a = b); exact hnd.1 hb
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

theorem roots_pair_of_mem_pairsL {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup)
    {p : ℕ × ℕ} (hp : p ∈ pairsL (rootsL F)) :
    decC n p.1 ∈ roots (decF n F) ∧ decC n p.2 ∈ roots (decF n F) ∧ decC n p.1 ≠ decC n p.2 := by
  have h12 := mem_pairsL hp
  rw [← decF_rootsL hv]
  exact ⟨decC_mem_decF h12.1, decC_mem_decF h12.2, fun h => ne_of_mem_pairsL (nodup_rootsL hnd) hp
    ((decC_inj (valid_rootsL hv _ h12.1) (valid_rootsL hv _ h12.2)).1 h)⟩

theorem sum_merges_decF {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup)
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
  have hlen : #((pairsL (rootsL F)).map fun p => decF n ((p.1 ||| p.2) :: F)).toFinset =
      ((pairsL (rootsL F)).map fun p => decF n ((p.1 ||| p.2) :: F)).length := by
    rw [List.length_map, length_pairsL, ← card_roots_decF hv hnd, ← hcard]
  rw [List.card_toFinset] at hlen
  rw [List.sum_toFinset _ (List.dedup_eq_self.1 ((List.dedup_sublist _).eq_of_length hlen)),
    List.map_map]
  rfl

theorem valid_merge {F : List ℕ} (hv : Valid n F) {p : ℕ × ℕ}
    (hp : p ∈ pairsL (rootsL F)) : Valid n ((p.1 ||| p.2) :: F) := by
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact Nat.or_lt_two_pow (valid_rootsL hv _ (mem_pairsL hp).1)
      (valid_rootsL hv _ (mem_pairsL hp).2)
  · exact hv c hc

theorem nodup_merge {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup)
    {p : ℕ × ℕ} (hp : p ∈ pairsL (rootsL F)) :
    ((p.1 ||| p.2) :: F).Nodup := by
  refine List.nodup_cons.2 ⟨fun h => ?_, hnd⟩
  obtain ⟨ha, hb, hne⟩ := roots_pair_of_mem_pairsL hv hnd hp
  exact union_not_mem_of_mem_roots ha hb hne (decC_or n p.1 p.2 ▸ decC_mem_decF h)

theorem isForest_merge {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup)
    (hF : IsForest (decF n F)) {p : ℕ × ℕ} (hp : p ∈ pairsL (rootsL F)) :
    IsForest (decF n ((p.1 ||| p.2) :: F)) := by
  obtain ⟨ha, hb, _⟩ := roots_pair_of_mem_pairsL hv hnd hp
  rw [decF_merge]; exact hF.isForest_merge ha hb

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

theorem jumpMatrix_pow_decF : ∀ (j : ℕ) (F : List ℕ), Valid n F → F.Nodup →
    IsForest (decF n F) → ∀ G : Finset (Finset (Fin n)),
    (jumpMatrix ^ j) (decF n F) G = ((jumpL j F).map fun q => if decF n q.2 = G then (q.1 : ℝ) else 0).sum
  | 0, F, _, _, _, G => by
    rcases eq_or_ne (decF n F) G with rfl | h <;> simp [jumpL, *]
  | j + 1, F, hv, hnd, hF, G => by
    by_cases hk : (rootsL F).length ≤ 1
    · rw [jumpMatrix_pow_of_card_roots_le_one (by rw [card_roots_decF hv hnd]; exact hk)]
      rcases eq_or_ne (decF n F) G with rfl | h <;> simp [jumpL, *, Ne.symm]
    · rw [jumpMatrix_pow_succ_apply (by rw [card_roots_decF hv hnd]; omega),
        sum_merges_decF hv hnd hF, card_roots_decF hv hnd, jumpL, ite_eq_right hk,
        sum_map_flatMap, ← List.sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro p hp
      rw [jumpMatrix_pow_decF j _ (valid_merge hv hp) (nodup_merge hv hnd hp)
        (isForest_merge hv hnd hF hp) G, ← List.sum_map_mul_left, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q _
      simp only [Function.comp_apply]
      split_ifs <;> push_cast <;> ring

theorem sum_range_eq_list {M : Type*} [AddCommMonoid M] (k : ℕ) (f : ℕ → M) :
    ∑ j ∈ range k, f j = ((List.range k).map f).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

theorem sum_mul_sum_list {α β : Type*} (A : List α) (B : List β) (f : α → ℝ) (g : β → ℝ) :
    (A.map f).sum * (B.map g).sum = (A.map fun a => (B.map fun b => f a * g b).sum).sum := by
  rw [← List.sum_map_mul_right]
  congr 1
  exact List.map_congr_left fun a _ => (List.sum_map_mul_left ..).symm

def isForestB (F : List ℕ) : Bool :=
  F.all (· != 0) && F.all fun c => F.all fun d => (c &&& d == c) || (c &&& d == d) || (c &&& d == 0)

theorem isForest_of_isForestB {F : List ℕ} (hv : Valid n F) (h : isForestB F = true) :
    IsForest (decF n F) := by
  simp only [isForestB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.or_eq_true, beq_iff_eq] at h
  refine ⟨fun A hA => ?_, fun A hA B hB => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA
    exact decC_nonempty_of_ne_zero (hv c hc) (h.1 c hc)
  · obtain ⟨c, hc, rfl⟩ := mem_decF.1 hA
    obtain ⟨d, hd, rfl⟩ := mem_decF.1 hB
    rcases h.2 c hc d hd with (h1 | h2) | h3
    · exact Or.inl ((decC_subset_iff (hv c hc)).2 h1)
    · exact Or.inr (Or.inl ((decC_subset_iff (hv d hd)).2 (Nat.and_comm d c ▸ h2)))
    · exact Or.inr (Or.inr (decC_disjoint_of_and_eq_zero h3))

def checkF (n : ℕ) (F : List ℕ) : Bool := decide (Valid n F) && decide F.Nodup && isForestB F

theorem of_checkF {F : List ℕ} (h : checkF n F = true) :
    Valid n F ∧ F.Nodup ∧ IsForest (decF n F) := by
  simp only [checkF, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, isForest_of_isForestB h.1.1 h.2⟩

def unrootL (n : ℕ) (F : List ℕ) : List ℕ :=
  (F.filter (· != 2 ^ n - 1)) ++ (F.filter (· != 2 ^ n - 1)).map ((2 ^ n - 1) ^^^ ·)

theorem decF_unrootL {F : List ℕ} (hv : Valid n F) :
    decF n (unrootL n F) = unroot (decF n F) := by
  have h1 : decF n (F.filter (· != 2 ^ n - 1)) = (decF n F).erase univ := by
    ext A; simp only [mem_decF, List.mem_filter, bne_iff_ne, ne_eq, mem_erase]
    exact ⟨fun ⟨c, ⟨hc, hne⟩, e⟩ => ⟨e ▸ mt (decC_eq_univ_iff (hv c hc)).1 hne, c, hc, e⟩,
      fun ⟨hne, c, hc, e⟩ => ⟨c, ⟨hc, mt (decC_eq_univ_iff (hv c hc)).2 (e ▸ hne)⟩, e⟩⟩
  have h2 : ∀ l : List ℕ, decF n (l.map ((2 ^ n - 1) ^^^ ·)) = (decF n l).image compl := by
    intro l; ext A; simp only [mem_decF, List.mem_map, mem_image]
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩; exact ⟨decC n c, ⟨c, hc, rfl⟩, decC_compl⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩; exact ⟨_, ⟨c, hc, rfl⟩, decC_compl.symm⟩
  rw [unrootL, decF_append, h1, h2, h1, unroot]

def coversB (n : ℕ) (F : List ℕ) : Bool := F.foldr (· ||| ·) 0 == 2 ^ n - 1

theorem lineages_decF (n : ℕ) (F : List ℕ) :
    lineages (decF n F) = decC n (F.foldr (· ||| ·) 0) := by
  induction F with
  | nil => ext i; simp [lineages, decF, mem_decC]
  | cons c F ih => rw [decF_cons, lineages_insert, ih, List.foldr_cons, decC_or]

theorem lineages_eq_univ_of_coversB {F : List ℕ} (h : coversB n F = true) :
    lineages (decF n F) = univ := by
  rw [lineages_decF, beq_iff_eq.1 h, decC_full]

def sampledL (n a : ℕ) : List ℕ :=
  ((List.finRange n).filter fun l : Fin n => a.testBit l).map fun l => 2 ^ l.val

theorem decF_sampledL (a : ℕ) :
    decF n (sampledL n a) = sampledForest id (decC n a) := by
  ext A
  simp [mem_decF, sampledL, sampledForest, List.mem_finRange, mem_decC, decC_two_pow]

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
      simp only [Option.some.injEq] at h; subst h
      rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        hv a (List.mem_cons_self ..) x hx, ih hy fun b hb => hv b (List.mem_cons_of_mem _ hb)]
    · simp at h

theorem kingmanTransition_eq_sum_range {L : Type*} [Fintype L] [DecidableEq L]
    {F : Finset (Finset L)} (hF : IsForest F) (hk : 1 ≤ #(roots F)) (t : ℝ)
    (G : Finset (Finset L)) :
    kingmanTransition t F G =
      ∑ j ∈ range #(roots F), deathProb #(roots F) (#(roots F) - j) t * (jumpMatrix ^ j) F G := by
  rw [kingmanTransition_apply hF]
  have hsupp : ∀ j, (jumpMatrix ^ j) F G ≠ 0 →
      #(roots G) = if j < #(roots F) then #(roots F) - j else min (#(roots F)) 1 :=
    fun j h => (jumpMatrix_pow_support hF h).2.2.2
  have hzero : ∀ j ∈ range #(roots F), #(roots F) - j ≠ #(roots G) →
      (jumpMatrix ^ j) F G = 0 := fun j hj hne => by
    by_contra h; have := hsupp j h; rw [ite_eq_left (mem_range.1 hj)] at this; exact hne this.symm
  by_cases hr : 1 ≤ #(roots G) ∧ #(roots G) ≤ #(roots F)
  · rw [Finset.sum_eq_single (#(roots F) - #(roots G))]
    · congr 2; omega
    · intro j hj hne; rw [hzero j hj (by omega), mul_zero]
    · intro h; exfalso; rw [mem_range] at h; omega
  · have hL : deathProb (#(roots F)) (#(roots G)) t *
        (jumpMatrix ^ (#(roots F) - #(roots G))) F G = 0 := by
      by_cases hgt : #(roots F) < #(roots G)
      · rw [deathProb_eq_zero_of_lt hgt, zero_mul]
      · rw [show (jumpMatrix ^ (#(roots F) - #(roots G))) F G = 0 from by_contra fun h => by
          have := hsupp _ h; split_ifs at this <;> omega, mul_zero]
    rw [hL]
    exact (Finset.sum_eq_zero fun j hj => by
      rw [hzero j hj (by rw [mem_range] at hj; omega), mul_zero]).symm

def gPoly : ℕ → ℕ → List (ℚ × ℕ)
  | 1, 1 => [(1, 0)]
  | 2, 1 => [(1, 0), (-1, 1)]
  | 2, 2 => [(1, 1)]
  | 3, 1 => [(1, 0), (-3/2, 1), (1/2, 3)]
  | 3, 2 => [(3/2, 1), (-3/2, 3)]
  | 3, 3 => [(1, 3)]
  | 4, 1 => [(1, 0), (-9/5, 1), (1, 3), (-1/5, 6)]
  | 4, 2 => [(9/5, 1), (-3, 3), (6/5, 6)]
  | 4, 3 => [(2, 3), (-2, 6)]
  | 4, 4 => [(1, 6)]
  | _, _ => []

theorem deathProb_eq_gPoly {k j : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (t : ℝ) :
    deathProb k j t = ((gPoly k j).map fun ce => (ce.1 : ℝ) * Real.exp (-t) ^ ce.2).sum := by
  obtain ⟨-, h11, h21, h22, h31, h32, h33, h41, h42, h43, h44⟩ := deathProb_small t
  interval_cases k <;> interval_cases j <;>
    simp only [gPoly, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h11, h21, h22, h31,
      h32, h33, h41, h42, h43, h44] <;> push_cast <;> ring

structure CTerm where
  coef : ℚ
  key : List (ℕ × ℕ)
  forest : List ℕ

variable {H : Finset (Finset (Fin n))} (len : Finset (Fin n) → ℝ)

noncomputable def monoVal (k : List (ℕ × ℕ)) : ℝ :=
  (k.map fun ae => Real.exp (-len (decC n ae.1)) ^ ae.2).prod

noncomputable def CTerm.val (τ : CTerm) : ℝ :=
  τ.coef * monoVal len τ.key

@[simp] theorem monoVal_nil : monoVal len [] = 1 := rfl

@[simp] theorem monoVal_cons (ae : ℕ × ℕ) (k : List (ℕ × ℕ)) :
    monoVal len (ae :: k) = Real.exp (-len (decC n ae.1)) ^ ae.2 * monoVal len k := by
  simp [monoVal]

theorem monoVal_append (k₁ k₂ : List (ℕ × ℕ)) :
    monoVal len (k₁ ++ k₂) = monoVal len k₁ * monoVal len k₂ := by
  simp [monoVal, List.prod_append]

def kernelL (n a : ℕ) (τ : CTerm) : Option (List CTerm) :=
  let k := (rootsL τ.forest).length
  if checkF n τ.forest && decide (1 ≤ k ∧ k ≤ 4) then
    some ((List.range k).flatMap fun j => (gPoly k (k - j)).flatMap fun ce =>
      (jumpL j τ.forest).map fun q =>
        ⟨τ.coef * ce.1 * q.1, if ce.2 = 0 then τ.key else τ.key ++ [(a, ce.2)], q.2⟩)
  else none

theorem kernelL_spec {a : ℕ} {τ : CTerm} {K : List CTerm}
    (h : kernelL n a τ = some K) (G : Finset (Finset (Fin n))) :
    τ.val len * kingmanTransition (len (decC n a)) (decF n τ.forest) G =
      (K.map fun τ' => if decF n τ'.forest = G then τ'.val len else 0).sum := by
  unfold kernelL at h; dsimp only at h
  split_ifs at h with hc; cases h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hv, hnd, hF⟩ := of_checkF hc.1
  have hk := card_roots_decF hv hnd
  rw [kingmanTransition_eq_sum_range hF (by omega), hk, sum_range_eq_list,
    ← List.sum_map_mul_left, sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [sum_map_flatMap, deathProb_eq_gPoly hc.2.1 hc.2.2 (by omega) (by omega),
    jumpMatrix_pow_decF j _ hv hnd hF G, sum_mul_sum_list, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro ce _
  rw [← List.sum_map_mul_left, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q _
  by_cases h0 : ce.2 = 0 <;>
    simp only [h0, ↓reduceIte, Function.comp_apply, CTerm.val, monoVal_append, monoVal_cons,
      monoVal_nil, pow_zero] <;>
    split_ifs <;> push_cast <;> ring

def stopB (n : ℕ) (F : List ℕ) : Bool :=
  decide (1 ≤ (rootsL F).length ∧ (rootsL F).length ≤ 3) && coversB n F

def outcomeL (n : ℕ) : ℕ → List ℕ → Option (List (ℚ × List ℕ))
  | 0, F => if stopB n F then some [(1, unrootL n F)] else none
  | fuel + 1, F => if stopB n F then some [(1, unrootL n F)]
      else if 2 ≤ (rootsL F).length then
        flatMapO (fun p => (outcomeL n fuel ((p.1 ||| p.2) :: F)).map
          (List.map fun q => ((((rootsL F).length.choose 2 : ℕ) : ℚ)⁻¹ * q.1, q.2)))
          (pairsL (rootsL F))
      else none

theorem unrootedOutcome_of_stopB {F : List ℕ} (hv : Valid n F) (hnd : F.Nodup)
    (hF : IsForest (decF n F)) (h : stopB n F = true) (U : Finset (Finset (Fin n))) :
    unrootedOutcome (decF n F) U = if decF n (unrootL n F) = U then 1 else 0 := by
  have hk := card_roots_decF hv hnd
  simp only [stopB, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [decF_unrootL hv]
  exact unrootedOutcome_of_card_roots_le_three hF (lineages_eq_univ_of_coversB h.2)
    (hk ▸ h.1.1) (hk ▸ h.1.2) U

theorem outcomeL_spec : ∀ (fuel : ℕ) (F : List ℕ), Valid n F → F.Nodup →
    IsForest (decF n F) → ∀ P, outcomeL n fuel F = some P → ∀ U : Finset (Finset (Fin n)),
    unrootedOutcome (decF n F) U = (P.map fun q => if decF n q.2 = U then (q.1 : ℝ) else 0).sum
  | 0, F, hv, hnd, hF, P, h, U => by
    unfold outcomeL at h; split_ifs at h with hs; cases h
    simp [unrootedOutcome_of_stopB hv hnd hF hs]
  | fuel + 1, F, hv, hnd, hF, P, h, U => by
    unfold outcomeL at h
    split_ifs at h with hs h2
    · cases h; simp [unrootedOutcome_of_stopB hv hnd hF hs]
    · have hk := card_roots_decF hv hnd
      rw [unrootedOutcome_first_step hF (hk ▸ h2), sum_merges_decF hv hnd hF, hk,
        ← List.sum_map_mul_left]
      symm
      apply sum_flatMapO h
      intro p hp x hx
      obtain ⟨P', hP', rfl⟩ := Option.map_eq_some_iff.1 hx
      rw [outcomeL_spec fuel _ (valid_merge hv hp) (nodup_merge hv hnd hp)
        (isForest_merge hv hnd hF hp) P' hP' U, ← List.sum_map_mul_left, List.map_map]
      congr 1
      apply List.map_congr_left
      intro q _
      simp only [Function.comp_apply]
      split_ifs <;> push_cast <;> ring

noncomputable def iterSum {ι β : Type*} [Fintype β] [DecidableEq β] (μ : ι → Finset β → ℝ) :
    List ι → Finset β → (Finset β → ℝ) → ℝ
  | [], S, φ => φ S
  | B :: l, S, φ => ∑ F, μ B F * iterSum μ l (F ∪ S) φ

def piInsertEquiv {ι γ : Type*} [DecidableEq ι] {B : ι} {C : Finset ι} (hB : B ∉ C) :
    (↥(insert B C) → γ) ≃ γ × (↥C → γ) where
  toFun f := (f ⟨B, mem_insert_self B C⟩, fun i => f ⟨i.1, mem_insert_of_mem i.2⟩)
  invFun p i := if h : i.1 = B then p.1 else p.2 ⟨i.1, (mem_insert.1 i.2).resolve_left h⟩
  left_inv f := funext fun ⟨i, hi⟩ => by by_cases h : i = B <;> simp [h]
  right_inv := fun ⟨x, f⟩ => Prod.ext (by simp) (funext fun ⟨i, hi⟩ => by
    simp [show i ≠ B from fun h => hB (h ▸ hi)])

theorem prod_coe_insert {ι M : Type*} [DecidableEq ι] [CommMonoid M] {B : ι} {C : Finset ι}
    (hB : B ∉ C) (h : ↥(insert B C) → M) :
    ∏ i : ↥(insert B C), h i =
      h ⟨B, mem_insert_self B C⟩ * ∏ i : ↥C, h ⟨i.1, mem_insert_of_mem i.2⟩ := by
  rw [univ_eq_attach, attach_insert, prod_insert, prod_image, ← univ_eq_attach]
  · intro x _ y _ hxy; exact Subtype.ext (congrArg Subtype.val hxy :)
  · simp [Subtype.ext_iff, hB]

theorem sup_coe_insert {ι β : Type*} [DecidableEq ι] [DecidableEq β] {B : ι} {C : Finset ι}
    (h : ↥(insert B C) → Finset β) :
    univ.sup h = h ⟨B, mem_insert_self B C⟩ ∪ univ.sup fun i : ↥C => h ⟨i.1, mem_insert_of_mem i.2⟩ := by
  rw [univ_eq_attach, attach_insert, sup_insert, sup_image, ← univ_eq_attach]; rfl

theorem sum_pi_eq_iterSum {ι β : Type*} [DecidableEq ι] [Fintype β] [DecidableEq β]
    (μ : ι → Finset β → ℝ) (φ : Finset β → ℝ) : ∀ (l : List ι), l.Nodup →
    ∀ (C : Finset ι), C = l.toFinset → ∀ S : Finset β,
    ∑ f : ↥C → Finset β, (∏ B : ↥C, μ B (f B)) * φ (univ.sup f ∪ S) = iterSum μ l S φ
  | [], _, C, hC, S => by
    rw [List.toFinset_nil] at hC; subst hC; rw [iterSum, Fintype.sum_unique]; simp
  | B :: l, hnd, C, hC, S => by
    rw [List.toFinset_cons] at hC; subst hC; rw [List.nodup_cons] at hnd
    have hB : B ∉ l.toFinset := by simpa using hnd.1
    rw [iterSum, Fintype.sum_equiv (piInsertEquiv hB) _
      (fun p => μ B p.1 * ((∏ i : ↥l.toFinset, μ i (p.2 i)) * φ (univ.sup p.2 ∪ (p.1 ∪ S))))]
    · rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun x _ => ?_
      dsimp only
      rw [← Finset.mul_sum, sum_pi_eq_iterSum μ φ l hnd.2 _ rfl (x ∪ S)]
    · intro f
      rw [prod_coe_insert hB, sup_coe_insert]
      simp only [piInsertEquiv, Equiv.coe_fn_mk, mul_assoc, union_assoc, union_left_comm]

theorem forestDist_eq_iterSum {X L : Type*} [Fintype X] [DecidableEq X] [Fintype L]
    [DecidableEq L] {H : Finset (Finset X)} {len : Finset X → ℝ} {s : L → X} {A : Finset X}
    {l : List (Finset X)} (hC : childClusters H A = l.toFinset) (hl : l.Nodup)
    (G : Finset (Finset L)) :
    forestDist H len s A G =
      iterSum (forestDist H len s) l (sampledForest s A) (fun F => populationKernel len A F G) := by
  rw [forestDist]
  exact sum_pi_eq_iterSum (forestDist H len s) (fun F => populationKernel len A F G) l hl _ hC _

theorem sum_collapse {β γ : Type*} [Fintype γ] [DecidableEq γ] (M : List β) (key : β → γ)
    (v : β → ℝ) (ψ : γ → ℝ) :
    ∑ x, (M.map fun b => if key b = x then v b else 0).sum * ψ x =
      (M.map fun b => v b * ψ (key b)).sum := by
  induction M with
  | nil => simp
  | cons b M ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih, ite_mul,
      zero_mul, Finset.sum_ite_eq, mem_univ, ite_true]

theorem sum_ite_list_sum {β γ : Type*} [Fintype γ] (E : List β) (p : γ → Prop) [DecidablePred p]
    (f : β → γ → ℝ) :
    ∑ x, (if p x then (E.map fun b => f b x).sum else 0) =
      (E.map fun b => ∑ x, if p x then f b x else 0).sum := by
  induction E with
  | nil => simp
  | cons b E ih =>
    simp only [List.map_cons, List.sum_cons, ← ih, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun x _ => by split_ifs <;> simp

def CTerm.mul (τ τ' : CTerm) : CTerm := ⟨τ.coef * τ'.coef, τ.key ++ τ'.key, τ'.forest⟩

def chL (all : List ℕ) (a : ℕ) : List ℕ :=
  let sub := all.filter fun b => b != a && (b &&& a == b)
  sub.filter fun b => sub.all fun c => !(b &&& c == b) || c == b

def allOf (n : ℕ) (cs : List ℕ) : List ℕ := cs ++ (List.range n).map (2 ^ ·)

def wfCsB (n : ℕ) (H : Finset (Finset (Fin n))) (cs : List ℕ) : Bool :=
  let all := allOf n cs
  ((2 ^ n - 1) :: all).all fun a =>
    decide (a < 2 ^ n) &&
      decide (childClusters H (decC n a) = ((chL all a).map (decC n)).toFinset) &&
      decide ((chL all a).map (decC n)).Nodup &&
      (chL all a).all fun b => decide (b ∈ all) && b != 2 ^ n - 1

def combL (f : ℕ → Option (List CTerm)) : List ℕ → List ℕ → Option (List CTerm)
  | [], S => some [⟨1, [], S⟩]
  | c :: cs, S => match f c with
    | some M => flatMapO (fun τ => (combL f cs (τ.forest ∪ S)).map (List.map τ.mul)) M
    | none => none

def outL (n : ℕ) (all : List ℕ) : ℕ → ℕ → Option (List CTerm)
  | 0, _ => none
  | fuel + 1, a => match combL (outL n all fuel) (chL all a) (sampledL n a) with
    | some E => flatMapO (kernelL n a) E
    | none => none

def unrootedL (n : ℕ) (cs : List ℕ) : Option (List CTerm) :=
  let all := allOf n cs
  match combL (outL n all n) (chL all (2 ^ n - 1)) (sampledL n (2 ^ n - 1)) with
  | some E => flatMapO (fun τ => (if checkF n τ.forest then outcomeL n n τ.forest else none).map
      (List.map fun q => ⟨τ.coef * q.1, τ.key, q.2⟩)) E
  | none => none

theorem of_wfCsB {cs : List ℕ}
    (hwf : wfCsB n H cs = true) {a : ℕ} (ha : a ∈ (2 ^ n - 1) :: allOf n cs) :
    a < 2 ^ n ∧
      childClusters H (decC n a) = ((chL (allOf n cs) a).map (decC n)).toFinset ∧
      ((chL (allOf n cs) a).map (decC n)).Nodup ∧
      ∀ b ∈ chL (allOf n cs) a, b ∈ allOf n cs ∧ b ≠ 2 ^ n - 1 := by
  have h := List.all_eq_true.1 hwf a ha
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem combL_spec (f : ℕ → Option (List CTerm)) (cs : List ℕ)
    (hf : ∀ c ∈ cs, ∀ M, f c = some M → ∀ G,
      forestDist H len id (decC n c) G =
        (M.map fun τ => if decF n τ.forest = G then τ.val len else 0).sum) :
    ∀ S M, combL f cs S = some M → ∀ φ,
      iterSum (forestDist H len id) (cs.map (decC n)) (decF n S) φ =
        (M.map fun τ => τ.val len * φ (decF n τ.forest)).sum
  | S, M, hM, φ => by
    induction cs generalizing S M with
    | nil => simp only [combL, Option.some.injEq] at hM; subst hM; simp [iterSum, CTerm.val]
    | cons c cs ih =>
      simp only [combL] at hM
      split at hM
      · rename_i Mc hMc
        simp only [List.map_cons, iterSum]
        simp_rw [hf c List.mem_cons_self Mc hMc]
        rw [sum_collapse]
        symm
        apply sum_flatMapO hM
        intro τ _ x hx
        obtain ⟨Mτ, hMτ, rfl⟩ := Option.map_eq_some_iff.1 hx
        rw [← decF_union, ih (fun c' hc' => hf c' (List.mem_cons_of_mem _ hc')) _ Mτ hMτ,
          List.map_map, ← List.sum_map_mul_left]
        congr 1
        apply List.map_congr_left
        intro τ' _
        simp only [Function.comp_apply, CTerm.val, CTerm.mul, monoVal_append]
        push_cast; ring
      · simp at hM

theorem outL_spec {cs : List ℕ} (hwf : wfCsB n H cs = true) :
    ∀ (fuel a : ℕ), a ∈ allOf n cs → a ≠ 2 ^ n - 1 → ∀ M, outL n (allOf n cs) fuel a = some M → ∀ G,
      forestDist H len id (decC n a) G =
        (M.map fun τ => if decF n τ.forest = G then τ.val len else 0).sum
  | 0, _, _, _, _, hM, _ => by simp [outL] at hM
  | fuel + 1, a, ha, hne, M, hM, G => by
    obtain ⟨hlt, hC, hnd, hch⟩ := of_wfCsB hwf (List.mem_cons_of_mem _ ha)
    simp only [outL] at hM
    split at hM
    · rename_i E hE
      rw [forestDist_eq_iterSum hC hnd G, populationKernel,
        ite_eq_right (fun h => hne ((decC_eq_univ_iff hlt).1 h)), ← decF_sampledL,
        combL_spec len _ _
          (fun b hb => outL_spec hwf fuel b (hch b hb).1 (hch b hb).2) _ E hE]
      exact (sum_flatMapO hM _ _ fun τ _ K hK => (kernelL_spec len hK G).symm).symm
    · simp at hM

theorem unrootedL_spec {cs : List ℕ} (hwf : wfCsB n H cs = true)
    (M : List CTerm) (hM : unrootedL n cs = some M) (U : Finset (Finset (Fin n))) :
    (∑ G, if unroot G = U then forestDist H len id univ G else 0) =
      (M.map fun τ => if decF n τ.forest = U then τ.val len else 0).sum := by
  obtain ⟨_, hC, hnd, hch⟩ := of_wfCsB hwf List.mem_cons_self
  simp only [unrootedL] at hM
  split at hM
  · rename_i E hE
    have hfd : ∀ G, forestDist H len id univ G =
        (E.map fun τ => τ.val len * kingmanAbsorption (decF n τ.forest) G).sum := fun G => by
      rw [decC_full] at hC
      rw [forestDist_eq_iterSum hC hnd G, populationKernel, ite_eq_left rfl, ← decC_full n,
        ← decF_sampledL]
      exact combL_spec len _ _
        (fun b hb => outL_spec len hwf n b (hch b hb).1 (hch b hb).2) _ E hE _
    simp_rw [hfd, sum_ite_list_sum]
    symm
    apply sum_flatMapO hM
    intro τ _ x hx
    obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.1 hx
    split_ifs at hP with hc
    obtain ⟨hv, hnd', hF⟩ := of_checkF hc
    have hout := outcomeL_spec n _ hv hnd' hF P hP U
    have h1 : (∑ x, if unroot x = U then τ.val len * kingmanAbsorption (decF n τ.forest) x
        else 0) = τ.val len * unrootedOutcome (decF n τ.forest) U := by
      rw [unrootedOutcome, Finset.mul_sum]
      exact sum_congr rfl fun x _ => by split_ifs <;> simp
    show _ = ∑ x, if unroot x = U then τ.val len * kingmanAbsorption (decF n τ.forest) x else 0
    rw [h1, hout, List.map_map, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro q _
    simp only [Function.comp_apply, CTerm.val]
    split_ifs <;> push_cast <;> ring
  · simp at hM

noncomputable def evalPoly (P : List (ℚ × List (ℕ × ℕ))) : ℝ :=
  (P.map fun p => (p.1 : ℝ) * monoVal len p.2).sum

@[simp] theorem evalPoly_nil : evalPoly len [] = 0 := rfl

@[simp] theorem evalPoly_cons (p : ℚ × List (ℕ × ℕ)) (P : List (ℚ × List (ℕ × ℕ))) :
    evalPoly len (p :: P) = (p.1 : ℝ) * monoVal len p.2 + evalPoly len P := rfl

def root_famMask (l : List ℕ) : ℕ := l.foldr (fun c acc => 2 ^ c ||| acc) 0

theorem root_testBit_famMask (l : List ℕ) (c : ℕ) :
    (root_famMask l).testBit c = decide (c ∈ l) := by
  induction l with
  | nil => simp [root_famMask]
  | cons a l ih =>
    simp only [root_famMask, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_or, ih, Nat.testBit_two_pow]
    by_cases h : a = c
    · subst h; simp
    · simp [h, Ne.symm h]

theorem root_decF_eq_iff {a b : List ℕ} (ha : Valid n a) (hb : Valid n b) :
    decF n a = decF n b ↔ (root_famMask a == root_famMask b) = true := by
  rw [decF_eq_iff ha hb, beq_iff_eq]
  refine ⟨fun ⟨h1, h2⟩ => Nat.eq_of_testBit_eq fun c => ?_, fun h => ?_⟩
  · rw [root_testBit_famMask, root_testBit_famMask, decide_eq_decide]
    exact ⟨h1 c, h2 c⟩
  · have hm : ∀ c, c ∈ a ↔ c ∈ b := fun c => by
      simpa [root_testBit_famMask] using congrArg (·.testBit c) h
    exact ⟨fun c => (hm c).1, fun c => (hm c).2⟩

def root_collect (M : List CTerm) (u : List ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  (M.filter fun τ => root_famMask τ.forest == root_famMask u).map fun τ =>
    (τ.coef, τ.key)

theorem sum_eq_evalPoly_collect (M : List CTerm) (u : List ℕ) (hM : ∀ τ ∈ M, Valid n τ.forest)
    (hu : Valid n u) :
    (M.map fun τ => if decF n τ.forest = decF n u then τ.val len else 0).sum =
      evalPoly len (root_collect M u) := by
  induction M with
  | nil => rfl
  | cons τ M ih =>
    rw [List.map_cons, List.sum_cons, ih fun τ' h => hM τ' (List.mem_cons_of_mem _ h)]
    have hiff := root_decF_eq_iff (hM τ List.mem_cons_self) hu
    by_cases h : (root_famMask τ.forest == root_famMask u) = true
    · rw [ite_eq_left (hiff.2 h)]; simp [root_collect, h, CTerm.val]
    · rw [ite_eq_right (mt hiff.1 h)]; simp [root_collect, h]

def root_hier5 (a b : ℕ) : List ℕ := [a, b, 1, 2, 4, 8, 16, 31]

def root_T5code : ℕ → List ℕ
  | 1 => unrootL 5 (root_hier5 3 7)
  | 4 => unrootL 5 (root_hier5 5 7)
  | 5 => unrootL 5 (root_hier5 5 13)
  | 6 => unrootL 5 (root_hier5 5 21)
  | 7 => unrootL 5 (root_hier5 9 11)
  | _ => []

def root_Q4code (a : ℕ) : List ℕ := unrootL 4 [a, 1, 2, 4, 8, 15]

def root_addTerm (t : ℚ × List (ℕ × ℕ)) : List (ℚ × List (ℕ × ℕ)) → List (ℚ × List (ℕ × ℕ))
  | [] => [t]
  | s :: l => if s.2 = t.2 then (s.1 + t.1, s.2) :: l else s :: root_addTerm t l

theorem root_evalPoly_addTerm (t : ℚ × List (ℕ × ℕ)) :
    ∀ l, evalPoly len (root_addTerm t l) = t.1 * monoVal len t.2 + evalPoly len l
  | [] => by simp [root_addTerm]
  | s :: l => by
    unfold root_addTerm
    split_ifs with h
    · simp only [evalPoly_cons, h]; push_cast; ring
    · simp only [evalPoly_cons, root_evalPoly_addTerm t l]; ring

def root_normPoly (P : List (ℚ × List (ℕ × ℕ))) : List (ℚ × List (ℕ × ℕ)) :=
  P.foldr root_addTerm []

theorem root_evalPoly_normPoly : ∀ P, evalPoly len (root_normPoly P) = evalPoly len P
  | [] => rfl
  | t :: P => by
    rw [root_normPoly, List.foldr_cons, ← root_normPoly, root_evalPoly_addTerm,
      root_evalPoly_normPoly P, evalPoly_cons]

def root_polyEqB (P Q : List (ℚ × List (ℕ × ℕ))) : Bool :=
  (root_normPoly (P ++ Q.map fun t => (-t.1, t.2))).all fun t => t.1 == 0

theorem root_evalPoly_eq_of_polyEqB {P Q : List (ℚ × List (ℕ × ℕ))}
    (h : root_polyEqB P Q = true) : evalPoly len P = evalPoly len Q := by
  have e : evalPoly len (root_normPoly (P ++ Q.map fun t => (-t.1, t.2))) = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      simp [beq_iff_eq.1 (List.all_eq_true.1 h t ht)]
  have hneg : ∀ Q, evalPoly len (Q.map fun t => (-t.1, t.2)) = -evalPoly len Q := fun Q => by
    induction Q with | nil => simp | cons t Q ih => simp [ih]; ring
  rw [root_evalPoly_normPoly, evalPoly, List.map_append, List.sum_append, ← evalPoly, ← evalPoly,
    hneg] at e
  linarith

def root_certsB (n : ℕ) (R : Option (List CTerm))
    (targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))) : Bool :=
  match R with
  | some M => M.all (fun τ => decide (Valid n τ.forest)) &&
      targets.all fun t => decide (Valid n t.1) && root_polyEqB (root_collect M t.1) t.2
  | none => false

theorem root_unrootedDist_eq_evalPoly (σ : SpeciesTree (Fin n))
    {H : Finset (Finset (Fin n))} (hσ : σ.clusters = H) (cs : List ℕ)
    (hwf : wfCsB n H cs = true)
    {targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))}
    (hc : root_certsB n (unrootedL n cs) targets = true)
    {t : List ℕ × List (ℚ × List (ℕ × ℕ))} (ht : t ∈ targets) {U : Finset (Finset (Fin n))}
    (hu : decF n t.1 = U) : σ.unrootedDist id U = evalPoly σ.length t.2 := by
  cases hM : unrootedL n cs with
  | none => simp [hM, root_certsB] at hc
  | some M =>
    rw [hM] at hc
    simp only [root_certsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
    unfold SpeciesTree.unrootedDist SpeciesTree.rootedDist
    rw [hσ, unrootedL_spec σ.length hwf M hM U, ← hu,
      sum_eq_evalPoly_collect σ.length M t.1 hc.1 (hc.2 t ht).1,
      root_evalPoly_eq_of_polyEqB σ.length (hc.2 t ht).2]

/-! ### Five taxa -/

def constP (m : List (ℕ × ℕ)) : List (ℚ × List (ℕ × ℕ)) := [(1 / 15, m)]
def loP (m : List (ℕ × ℕ)) (c : ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  [(1 / 90, m ++ [(c, 6)]), (1 / 18, m)]
def hiP (m : List (ℕ × ℕ)) (c : ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  [(-2 / 45, m ++ [(c, 6)]), (1 / 9, m)]
def p6Hi (m : List (ℕ × ℕ)) (b : ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  [(-1 / 10, m ++ [(b, 3)]), (1 / 6, m ++ [(b, 1)])]
def cat0Hi (m : List (ℕ × ℕ)) (b c : ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  [(1 / 90, m ++ [(b, 3), (c, 6)]), (-1 / 9, m ++ [(b, 3)]), (1 / 6, m ++ [(b, 1)])]
def cat1Hi (m : List (ℕ × ℕ)) (b c : ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  [(-2 / 45, m ++ [(b, 3), (c, 6)]), (-1 / 18, m ++ [(b, 3)]), (1 / 6, m ++ [(b, 1)])]

theorem monoVal_pos (m : List (ℕ × ℕ)) : 0 < monoVal len m :=
  List.prod_pos fun x hx => by
    obtain ⟨ae, _, rfl⟩ := List.mem_map.1 hx
    positivity

theorem eval_constP (len : Finset (Fin 5) → ℝ) (m : List (ℕ × ℕ)) :
    evalPoly len (constP m) = 1 / 15 * monoVal len m := by
  simp [constP]

theorem eval_loP (len : Finset (Fin 5) → ℝ) (m : List (ℕ × ℕ)) (c : ℕ) :
    evalPoly len (loP m c) =
      1 / 90 * monoVal len m * exp (-len (decC 5 c)) ^ 6 + 1 / 18 * monoVal len m := by
  simp [loP, monoVal_append]; ring

theorem root_u5_pair (τ : SpeciesTree (Fin 5)) {H : Finset (Finset (Fin 5))} (hτ : τ.clusters = H)
    (cs : List ℕ) (i j : ℕ) (Pᵢ Pⱼ : List (ℚ × List (ℕ × ℕ)))
    (hi : decF 5 (root_T5code i) = T5 i := by decide +kernel)
    (hj : decF 5 (root_T5code j) = T5 j := by decide +kernel)
    (hwf : wfCsB 5 H cs = true := by decide +kernel)
    (hc : root_certsB 5 (unrootedL 5 cs)
      [(root_T5code i, Pᵢ), (root_T5code j, Pⱼ)] = true := by decide +kernel) :
    u τ i = evalPoly τ.length Pᵢ ∧ u τ j = evalPoly τ.length Pⱼ :=
  ⟨root_unrootedDist_eq_evalPoly τ hτ cs hwf hc List.mem_cons_self hi,
    root_unrootedDist_eq_evalPoly τ hτ cs hwf hc
      (List.mem_cons_of_mem _ List.mem_cons_self) hj⟩

theorem root_u5_1456 (τ : SpeciesTree (Fin 5)) {H : Finset (Finset (Fin 5))} (hτ : τ.clusters = H)
    (cs : List ℕ) (P₁ P₄ P₅ P₆ : List (ℚ × List (ℕ × ℕ)))
    (h1 : decF 5 (root_T5code 1) = T5 1 := by decide +kernel)
    (h4 : decF 5 (root_T5code 4) = T5 4 := by decide +kernel)
    (h5 : decF 5 (root_T5code 5) = T5 5 := by decide +kernel)
    (h6 : decF 5 (root_T5code 6) = T5 6 := by decide +kernel)
    (hwf : wfCsB 5 H cs = true := by decide +kernel)
    (hc : root_certsB 5 (unrootedL 5 cs)
      [(root_T5code 1, P₁), (root_T5code 4, P₄), (root_T5code 5, P₅),
       (root_T5code 6, P₆)] = true := by decide +kernel) :
    u τ 1 = evalPoly τ.length P₁ ∧ u τ 4 = evalPoly τ.length P₄ ∧
    u τ 5 = evalPoly τ.length P₅ ∧ u τ 6 = evalPoly τ.length P₆ :=
  ⟨root_unrootedDist_eq_evalPoly τ hτ cs hwf hc List.mem_cons_self h1,
    root_unrootedDist_eq_evalPoly τ hτ cs hwf hc
      (List.mem_cons_of_mem _ List.mem_cons_self) h4,
    root_unrootedDist_eq_evalPoly τ hτ cs hwf hc
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) h5,
    root_unrootedDist_eq_evalPoly τ hτ cs hwf hc
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      h6⟩

end ADR11
