module

public import Chazelle.Separator.Clusters
public import Mathlib.Data.Nat.Size

/-!
# WP-I, part 18: the work stack of pieces

The recursive separation of `Separator/Clusters.lean` (`exists_split`), run with a stack of
pieces stored *in place*: a piece is a segment `p = (lo, hi)` of positions of an item array
`act`, its items are `act lo, …, act (hi - 1)`.  Splitting a piece rewrites `act` inside its
segment only, the three classes becoming consecutive sub-segments.

`SInv` (the invariant): the *live* segments (on the stack `stk`, all large; or finished, in
`fin`, all small) have pairwise disjoint position ranges and item sets, partition the vertices
outside `H` and the separator set `D`, each lies in one slab, every edge between vertices outside
`H ∪ D` lies in a live segment, and the potential `s |D| + Σ_{stack} 3k (2 |P| - s) ≤ 6 k μ`
holds (`sum_split_bound`).  A ghost counter `nsp` of splits satisfies
`nsp · s + Σ_{stack} (2 |P| - s) ≤ 2 μ` (so there are at most `2 μ / s` splits).

* `SInv.split`: the top segment is replaced by its large classes, its small nonempty classes are
  finished, after removing a separator of at most `3k` of its items (`SplitOK`);
* `SInv.final`: with an empty stack, the finished segments are clusters of at most `s`
  vertices, every edge outside `H ∪ D` stays in one cluster, and `s |D| ≤ 6 k μ`;
* `split_size_pot`: the potential `Σ |P| · size |P|` pays `|P|` for every split.
-/

namespace Chazelle.Core.Cluster

@[expose] public section

open Finset

/-- The items of the segment `p`. -/
def items (act : ℕ → ℕ) (p : ℕ × ℕ) : Finset ℕ := (Finset.Ico p.1 p.2).image act

/-- The length of a segment. -/
def len (p : ℕ × ℕ) : ℕ := p.2 - p.1

theorem items_card {act : ℕ → ℕ} {p : ℕ × ℕ} (h : Set.InjOn act (Finset.Ico p.1 p.2)) :
    (items act p).card = len p := by
  unfold items len
  rw [Finset.card_image_of_injOn h, Nat.card_Ico]

theorem mem_items {act : ℕ → ℕ} {p : ℕ × ℕ} {v : ℕ} :
    v ∈ items act p ↔ ∃ i, p.1 ≤ i ∧ i < p.2 ∧ act i = v := by
  unfold items
  simp only [Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨i, ⟨a, b⟩, c⟩; exact ⟨i, a, b, c⟩
  · rintro ⟨i, a, b, c⟩; exact ⟨i, ⟨a, b⟩, c⟩

/-- Items only depend on the array inside the segment. -/
theorem items_congr {act act' : ℕ → ℕ} {p : ℕ × ℕ}
    (h : ∀ i, p.1 ≤ i → i < p.2 → act' i = act i) : items act' p = items act p := by
  ext v
  simp only [mem_items]
  constructor
  · rintro ⟨i, a, b, c⟩; exact ⟨i, a, b, by rw [← h i a b]; exact c⟩
  · rintro ⟨i, a, b, c⟩; exact ⟨i, a, b, by rw [h i a b]; exact c⟩

section stack

variable (μ k s : ℕ) (H : Finset ℕ) (slab : ℕ → ℕ) (Adj : ℕ → ℕ → Prop)

/-- A live segment: on the stack or finished. -/
def Lv (stk : List (ℕ × ℕ)) (fin : Finset (ℕ × ℕ)) (p : ℕ × ℕ) : Prop := p ∈ stk ∨ p ∈ fin

/-- Disjoint position ranges (empty ranges are disjoint from everything). -/
def RDisj (p q : ℕ × ℕ) : Prop := p.2 ≤ q.1 ∨ q.2 ≤ p.1 ∨ p.2 ≤ p.1 ∨ q.2 ≤ q.1

/-- **The invariant of the work stack.** -/
structure SInv (act : ℕ → ℕ) (stk : List (ℕ × ℕ)) (fin : Finset (ℕ × ℕ)) (D : Finset ℕ)
    (nsp : ℕ) : Prop where
  wf : ∀ p, Lv stk fin p → p.1 ≤ p.2
  inj : ∀ p, Lv stk fin p → Set.InjOn act (Finset.Ico p.1 p.2)
  lt : ∀ p, Lv stk fin p → ∀ v ∈ items act p, v < μ
  nodup : stk.Nodup
  sf : ∀ p ∈ stk, p ∉ fin
  rdisj : ∀ p q, Lv stk fin p → Lv stk fin q → p ≠ q → RDisj p q
  disj : ∀ p q, Lv stk fin p → Lv stk fin q → p ≠ q → Disjoint (items act p) (items act q)
  big : ∀ p ∈ stk, s < len p
  small : ∀ p ∈ fin, len p ≤ s
  cover : ∀ v, v < μ → v ∉ H → v ∉ D → ∃ p, Lv stk fin p ∧ v ∈ items act p
  off : ∀ p, Lv stk fin p → ∀ v ∈ items act p, v ∉ D ∧ v ∉ H
  inslab : ∀ p, Lv stk fin p → ∀ v ∈ items act p, ∀ w ∈ items act p, slab v = slab w
  edge : ∀ x y, Adj x y → x ∉ H → x ∉ D → y ∉ H → y ∉ D →
    ∃ p, Lv stk fin p ∧ x ∈ items act p ∧ y ∈ items act p
  hD : Disjoint D H
  pot : s * D.card + ∑ p ∈ stk.toFinset, 3 * k * (2 * len p - s) ≤ 6 * k * μ
  pot2 : nsp * s + ∑ p ∈ stk.toFinset, (2 * len p - s) ≤ 2 * μ

variable {μ k s H slab Adj}

/-- **A valid split** of the segment `p = (lo, hi)` in place: the array changes only inside
`[lo, hi)`; the classes are the consecutive segments `(e t, e (t + 1))`, `t < 3`, inside
`[lo, hi)`, the new array is injective on their union, they hold exactly the items of `p` off
the separator `sep ⊆ items p`, at most half of them each, and no edge joins two classes;
`|sep| ≤ 3k`. -/
structure SplitOK (act act' : ℕ → ℕ) (p : ℕ × ℕ) (e : ℕ → ℕ) (sep : Finset ℕ) : Prop where
  out : ∀ i, (i < p.1 ∨ p.2 ≤ i) → i < μ → act' i = act i
  e0 : p.1 ≤ e 0
  mono : ∀ t, t < 3 → e t ≤ e (t + 1)
  e3 : e 3 ≤ p.2
  inj : Set.InjOn act' (Finset.Ico (e 0) (e 3))
  sub : sep ⊆ items act p
  parts : ∀ v, v ∈ items act p → v ∉ sep → ∃ t, t < 3 ∧ v ∈ items act' (e t, e (t + 1))
  inparts : ∀ t, t < 3 → ∀ v ∈ items act' (e t, e (t + 1)), v ∈ items act p ∧ v ∉ sep
  half : ∀ t, t < 3 → 2 * len (e t, e (t + 1)) ≤ len p
  noedge : ∀ x y, Adj x y → ∀ t t', t < 3 → t' < 3 → x ∈ items act' (e t, e (t + 1)) →
    y ∈ items act' (e t', e (t' + 1)) → t = t'
  card : sep.card ≤ 3 * k

/-- The class `t` of a split. -/
def scls (e : ℕ → ℕ) (t : ℕ) : ℕ × ℕ := (e t, e (t + 1))

theorem SplitOK.e_mono {act act' : ℕ → ℕ} {p : ℕ × ℕ} {e : ℕ → ℕ} {sep : Finset ℕ}
    (hS : SplitOK (μ := μ) (k := k) (Adj := Adj) act act' p e sep) {t t' : ℕ} (htt : t ≤ t')
    (ht' : t' ≤ 3) : e t ≤ e t' := by
  induction t' with
  | zero => rw [show t = 0 by omega]
  | succ n ih =>
    rcases Nat.lt_or_ge t (n + 1) with h | h
    · exact le_trans (ih (by omega) (by omega)) (hS.mono n (by omega))
    · rw [show t = n + 1 by omega]

theorem SplitOK.scls_in {act act' : ℕ → ℕ} {p : ℕ × ℕ} {e : ℕ → ℕ} {sep : Finset ℕ}
    (hS : SplitOK (μ := μ) (k := k) (Adj := Adj) act act' p e sep) {t : ℕ} (ht : t < 3) :
    p.1 ≤ e t ∧ e t ≤ e (t + 1) ∧ e (t + 1) ≤ p.2 := by
  refine ⟨le_trans hS.e0 (hS.e_mono (Nat.zero_le _) (by omega)), hS.mono t ht,
    le_trans (hS.e_mono (by omega) le_rfl) hS.e3⟩

theorem SplitOK.scls_inj {act act' : ℕ → ℕ} {p : ℕ × ℕ} {e : ℕ → ℕ} {sep : Finset ℕ}
    (hS : SplitOK (μ := μ) (k := k) (Adj := Adj) act act' p e sep) {t : ℕ} (ht : t < 3) :
    Set.InjOn act' (Finset.Ico (e t) (e (t + 1))) := by
  have a := hS.e_mono (Nat.zero_le t) (by omega)
  have b := hS.e_mono (show t + 1 ≤ 3 by omega) le_rfl
  intro x hx y hy hxy
  simp only [Finset.coe_Ico, Set.mem_Ico] at hx hy
  exact hS.inj (by simp only [Finset.coe_Ico, Set.mem_Ico]; omega)
    (by simp only [Finset.coe_Ico, Set.mem_Ico]; omega) hxy

/-- Distinct classes are disjoint. -/
theorem SplitOK.scls_disj {act act' : ℕ → ℕ} {p : ℕ × ℕ} {e : ℕ → ℕ} {sep : Finset ℕ}
    (hS : SplitOK (μ := μ) (k := k) (Adj := Adj) act act' p e sep) {t t' : ℕ} (ht : t < 3) (ht' : t' < 3)
    (hne : t ≠ t') : Disjoint (items act' (scls e t)) (items act' (scls e t')) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨i, a, b, c⟩ := mem_items.mp hv
  obtain ⟨i', a', b', c'⟩ := mem_items.mp hv'
  simp only [scls] at a b a' b'
  have h0 := hS.e_mono (Nat.zero_le t) (by omega)
  have h0' := hS.e_mono (Nat.zero_le t') (by omega)
  have h3 := hS.e_mono (show t + 1 ≤ 3 by omega) le_rfl
  have h3' := hS.e_mono (show t' + 1 ≤ 3 by omega) le_rfl
  have := hS.inj (by simp only [Finset.coe_Ico, Set.mem_Ico]; omega)
    (by simp only [Finset.coe_Ico, Set.mem_Ico]; omega) (c.trans c'.symm)
  subst this
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := hS.e_mono (show t + 1 ≤ t' by omega) (by omega); omega
  · have := hS.e_mono (show t' + 1 ≤ t by omega) (by omega); omega

/-- **Split the top segment.**  The large classes are pushed (`news`), the small nonempty ones
finished. -/
theorem SInv.split {act act' : ℕ → ℕ} {p : ℕ × ℕ} {rest news : List (ℕ × ℕ)}
    {fin : Finset (ℕ × ℕ)} {D sep : Finset ℕ} {nsp : ℕ} {e : ℕ → ℕ}
    (hI : SInv μ k s H slab Adj act (p :: rest) fin D nsp)
    (hS : SplitOK (μ := μ) (k := k) (Adj := Adj) act act' p e sep)
    (hnews : ∀ q, q ∈ news ↔ ∃ t, t < 3 ∧ q = scls e t ∧ s < len q) (hnd : news.Nodup)
    (hrng : ∀ q, Lv (p :: rest) fin q → q.2 ≤ μ) :
    SInv μ k s H slab Adj act' (news ++ rest)
      (fin ∪ ((Finset.range 3).image (scls e)).filter (fun q => 0 < len q ∧ len q ≤ s))
      (D ∪ sep) (nsp + 1) := by
  classical
  set fin' := fin ∪ ((Finset.range 3).image (scls e)).filter (fun q => 0 < len q ∧ len q ≤ s)
  have hLp : Lv (p :: rest) fin p := Or.inl (List.mem_cons_self)
  have hbig := hI.big p List.mem_cons_self
  have hpwf := hI.wf p hLp
  have hoffp := hI.off p hLp
  -- the old live segments other than `p` are untouched
  have hold : ∀ q, Lv (p :: rest) fin q → q ≠ p → items act' q = items act q := by
    intro q hq hqp
    refine items_congr (fun i a b => hS.out i ?_ (by have := hrng q hq; omega))
    rcases hI.rdisj q p hq hLp hqp with h | h | h | h
    · left; omega
    · right; omega
    · omega
    · unfold len at hbig; omega
  -- classification of the new live segments
  have hlive : ∀ q, Lv (news ++ rest) fin' q →
      (Lv (p :: rest) fin q ∧ q ≠ p) ∨ (∃ t, t < 3 ∧ q = scls e t ∧ 0 < len q) := by
    intro q hq
    rcases hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨t, ht, rfl, hb⟩ := (hnews q).mp hq
        exact Or.inr ⟨t, ht, rfl, by omega⟩
      · refine Or.inl ⟨Or.inl (List.mem_cons_of_mem _ hq), fun h => ?_⟩
        subst h
        exact (List.nodup_cons.mp hI.nodup).1 hq
    · rcases Finset.mem_union.mp hq with hq | hq
      · refine Or.inl ⟨Or.inr hq, fun h => ?_⟩
        subst h; exact hI.sf q List.mem_cons_self hq
      · obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq1
        exact Or.inr ⟨t, Finset.mem_range.mp ht, rfl, hq2.1⟩
  have hcls_live : ∀ t, t < 3 → 0 < len (scls e t) → Lv (news ++ rest) fin' (scls e t) := by
    intro t ht hpos
    by_cases hb : s < len (scls e t)
    · exact Or.inl (List.mem_append_left _ ((hnews _).mpr ⟨t, ht, rfl, hb⟩))
    · refine Or.inr (Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, rfl⟩, hpos, by omega⟩))
  have hold_live : ∀ q, Lv (p :: rest) fin q → q ≠ p → Lv (news ++ rest) fin' q := by
    intro q hq hqp
    rcases hq with hq | hq
    · rcases List.mem_cons.mp hq with h | h
      · exact absurd h hqp
      · exact Or.inl (List.mem_append_right _ h)
    · exact Or.inr (Finset.mem_union_left _ hq)
  have hclsp : ∀ t, t < 3 → scls e t ≠ p ∧ len (scls e t) < len p := by
    intro t ht
    have := hS.half t ht
    have hl : len (scls e t) < len p := by unfold len at *; simp only [scls] at *; omega
    exact ⟨fun h => by rw [h] at hl; omega, hl⟩
  have hnew_items : ∀ t, t < 3 → ∀ v ∈ items act' (scls e t), v ∈ items act p ∧ v ∉ sep :=
    fun t ht => hS.inparts t ht
  have hsep_off : ∀ v ∈ sep, v ∉ D ∧ v ∉ H := fun v hv => hoffp v (hS.sub hv)
  -- range disjointness of a class and an old segment
  have hrd_cls_old : ∀ t, t < 3 → ∀ q, Lv (p :: rest) fin q → q ≠ p → RDisj (scls e t) q := by
    intro t ht q hq hqp
    obtain ⟨a, b, c⟩ := hS.scls_in ht
    rcases hI.rdisj q p hq hLp hqp with h | h | h | h
    · right; left; simp only [scls]; omega
    · left; simp only [scls]; omega
    · right; right; right; omega
    · unfold len at hbig; omega
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq v hv => ?_, ?_, fun q hq hqf => ?_,
    fun q q' hq hq' hne => ?_, fun q q' hq hq' hne => ?_, fun q hq => ?_, fun q hq => ?_,
    fun v hv h1 h2 => ?_, fun q hq v hv => ?_, fun q hq v hv w hw => ?_,
    fun x y hxy a b c d => ?_, ?_, ?_, ?_⟩
  · -- well formed
    rcases hlive q hq with ⟨h1, _⟩ | ⟨t, ht, rfl, _⟩
    · exact hI.wf q h1
    · exact hS.mono t ht
  · -- injective
    rcases hlive q hq with ⟨h1, h2⟩ | ⟨t, ht, rfl, _⟩
    · intro i hi j hj hij
      simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
      have ho : ∀ i, q.1 ≤ i → i < q.2 → act' i = act i := by
        intro i a b
        refine hS.out i ?_ (by have := hrng q h1; omega)
        rcases hI.rdisj q p h1 hLp h2 with h | h | h | h
        · left; omega
        · right; omega
        · omega
        · unfold len at hbig; omega
      rw [ho i hi.1 hi.2, ho j hj.1 hj.2] at hij
      exact hI.inj q h1 (by simp [hi.1, hi.2]) (by simp [hj.1, hj.2]) hij
    · exact hS.scls_inj ht
  · -- vertices
    rcases hlive q hq with ⟨h1, h2⟩ | ⟨t, ht, rfl, _⟩
    · rw [hold q h1 h2] at hv; exact hI.lt q h1 v hv
    · exact hI.lt p hLp v (hnew_items t ht v hv).1
  · -- nodup
    refine List.Nodup.append hnd (List.nodup_cons.mp hI.nodup).2 ?_
    intro q hq1 hq2
    obtain ⟨t, ht, rfl, hb⟩ := (hnews q).mp hq1
    have hq2' : Lv (p :: rest) fin (scls e t) := Or.inl (List.mem_cons_of_mem _ hq2)
    have hne := (hclsp t ht).1
    have hrd := hI.rdisj _ p hq2' hLp hne
    obtain ⟨a, b, c⟩ := hS.scls_in ht
    unfold len at hb hbig
    simp only [scls] at hrd hb
    rcases hrd with h | h | h | h <;> omega
  · -- stack and finished disjoint
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨t, ht, rfl, hb⟩ := (hnews q).mp hq
      rcases Finset.mem_union.mp hqf with h | h
      · -- an old finished segment equal to a large class: ranges overlap
        have hL' : Lv (p :: rest) fin (scls e t) := Or.inr h
        have hrd := hI.rdisj _ p hL' hLp (hclsp t ht).1
        obtain ⟨a, b, c⟩ := hS.scls_in ht
        unfold len at hb hbig
        simp only [scls] at hrd hb
        rcases hrd with h | h | h | h <;> omega
      · have := (Finset.mem_filter.mp h).2.2; omega
    · rcases Finset.mem_union.mp hqf with h | h
      · exact hI.sf q (List.mem_cons_of_mem _ hq) h
      · obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp h
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hq1
        have hL' : Lv (p :: rest) fin (scls e t) := Or.inl (List.mem_cons_of_mem _ hq)
        have hrd := hI.rdisj _ p hL' hLp (hclsp t (Finset.mem_range.mp ht)).1
        obtain ⟨a, b, c⟩ := hS.scls_in (Finset.mem_range.mp ht)
        have := hq2.1
        unfold len at this hbig
        simp only [scls] at hrd this
        rcases hrd with h | h | h | h <;> omega
  · -- range disjointness
    rcases hlive q hq with ⟨h1, h2⟩ | ⟨t, ht, rfl, _⟩ <;>
      rcases hlive q' hq' with ⟨h1', h2'⟩ | ⟨t', ht', rfl, _⟩
    · exact hI.rdisj q q' h1 h1' hne
    · have := hrd_cls_old t' ht' q h1 h2
      unfold RDisj at this ⊢; omega
    · exact hrd_cls_old t ht q' h1' h2'
    · have htt : t ≠ t' := fun h => hne (by rw [h])
      simp only [RDisj, scls]
      rcases Nat.lt_or_gt_of_ne htt with h | h
      · left; exact hS.e_mono (show t + 1 ≤ t' by omega) (by omega)
      · right; left; exact hS.e_mono (show t' + 1 ≤ t by omega) (by omega)
  · -- item disjointness
    rcases hlive q hq with ⟨h1, h2⟩ | ⟨t, ht, rfl, _⟩ <;>
      rcases hlive q' hq' with ⟨h1', h2'⟩ | ⟨t', ht', rfl, _⟩
    · rw [hold q h1 h2, hold q' h1' h2']; exact hI.disj q q' h1 h1' hne
    · rw [hold q h1 h2, Finset.disjoint_left]
      intro v hv hv'
      exact Finset.disjoint_left.mp (hI.disj q p h1 hLp h2) hv (hnew_items t' ht' v hv').1
    · rw [hold q' h1' h2', Finset.disjoint_left]
      intro v hv hv'
      exact Finset.disjoint_left.mp (hI.disj q' p h1' hLp h2') hv' (hnew_items t ht v hv).1
    · exact hS.scls_disj ht ht' (fun h => hne (by rw [h]))
  · -- large on the stack
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨t, ht, rfl, hb⟩ := (hnews q).mp hq; exact hb
    · exact hI.big q (List.mem_cons_of_mem _ hq)
  · -- small finished
    rcases Finset.mem_union.mp hq with h | h
    · exact hI.small q h
    · exact (Finset.mem_filter.mp h).2.2
  · -- cover
    rw [Finset.mem_union, not_or] at h2
    obtain ⟨q, hq, hvq⟩ := hI.cover v hv h1 h2.1
    by_cases hqp : q = p
    · subst hqp
      obtain ⟨t, ht, hvt⟩ := hS.parts v hvq h2.2
      have hpos : 0 < len (scls e t) := by
        obtain ⟨i, a, b, _⟩ := mem_items.mp hvt
        unfold len scls; simp only at a b; omega
      exact ⟨scls e t, hcls_live t ht hpos, hvt⟩
    · exact ⟨q, hold_live q hq hqp, by rw [hold q hq hqp]; exact hvq⟩
  · -- off
    rcases hlive q hq with ⟨h1, h2⟩ | ⟨t, ht, rfl, _⟩
    · rw [hold q h1 h2] at hv
      obtain ⟨a, b⟩ := hI.off q h1 v hv
      refine ⟨?_, b⟩
      rw [Finset.mem_union, not_or]
      refine ⟨a, fun hs => ?_⟩
      exact Finset.disjoint_left.mp (hI.disj q p h1 hLp h2) hv (hS.sub hs)
    · obtain ⟨a, b⟩ := hnew_items t ht v hv
      obtain ⟨c, d⟩ := hoffp v a
      exact ⟨by rw [Finset.mem_union, not_or]; exact ⟨c, b⟩, d⟩
  · -- slabs
    rcases hlive q hq with ⟨h1, h2⟩ | ⟨t, ht, rfl, _⟩
    · rw [hold q h1 h2] at hv hw; exact hI.inslab q h1 v hv w hw
    · exact hI.inslab p hLp v (hnew_items t ht v hv).1 w (hnew_items t ht w hw).1
  · -- edges
    rw [Finset.mem_union, not_or] at b d
    obtain ⟨q, hq, hxq, hyq⟩ := hI.edge x y hxy a b.1 c d.1
    by_cases hqp : q = p
    · subst hqp
      obtain ⟨t, ht, hxt⟩ := hS.parts x hxq b.2
      obtain ⟨t', ht', hyt⟩ := hS.parts y hyq d.2
      have := hS.noedge x y hxy t t' ht ht' hxt hyt
      subst this
      have hpos : 0 < len (scls e t) := by
        obtain ⟨i, a, b, _⟩ := mem_items.mp hxt
        unfold len scls; simp only at a b; omega
      exact ⟨scls e t, hcls_live t ht hpos, hxt, hyt⟩
    · exact ⟨q, hold_live q hq hqp, by rw [hold q hq hqp]; exact hxq,
        by rw [hold q hq hqp]; exact hyq⟩
  · -- `D ∪ sep` stays off `H`
    rw [Finset.disjoint_union_left]
    exact ⟨hI.hD, Finset.disjoint_left.mpr (fun v hv => (hsep_off v hv).2)⟩
  · -- the potential
    have hdisjDs : Disjoint D sep := Finset.disjoint_right.mpr (fun v hv => (hsep_off v hv).1)
    rw [Finset.card_union_of_disjoint hdisjDs]
    have hpot := hI.pot
    have hpr : p ∉ rest := (List.nodup_cons.mp hI.nodup).1
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using hpr)] at hpot
    rw [List.toFinset_append]
    have hdn : Disjoint news.toFinset rest.toFinset := by
      rw [Finset.disjoint_left]
      intro q h1 h2
      exact List.disjoint_of_nodup_append (List.Nodup.append hnd (List.nodup_cons.mp hI.nodup).2
        (by
          intro q hq1 hq2
          obtain ⟨t, ht, rfl, hb⟩ := (hnews q).mp hq1
          have hq2' : Lv (p :: rest) fin (scls e t) := Or.inl (List.mem_cons_of_mem _ hq2)
          have hrd := hI.rdisj _ p hq2' hLp (hclsp t ht).1
          obtain ⟨a, b, c⟩ := hS.scls_in ht
          unfold len at hb hbig
          simp only [scls] at hrd hb
          rcases hrd with h | h | h | h <;> omega)) (List.mem_toFinset.mp h1)
          (List.mem_toFinset.mp h2)
    rw [Finset.sum_union hdn]
    -- the new terms
    have hsub : news.toFinset ⊆ (Finset.range 3).image (scls e) := by
      intro q hq
      obtain ⟨t, ht, rfl, _⟩ := (hnews q).mp (List.mem_toFinset.mp hq)
      exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, rfl⟩
    have hnewsum : ∑ q ∈ news.toFinset, 3 * k * (2 * len q - s) ≤
        ∑ t ∈ Finset.range 3, 3 * k * (2 * len (scls e t) - s) :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))
        (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _))
    -- the recursion bound
    have hsizes : ∑ t ∈ Finset.range 3, len (scls e t) ≤ len p := by
      have hcard : ∀ t, t < 3 → (items act' (scls e t)).card = len (scls e t) :=
        fun t ht => items_card (hS.scls_inj ht)
      rw [← Finset.sum_congr rfl (fun t ht => hcard t (Finset.mem_range.mp ht)),
        ← Finset.card_biUnion (fun t ht t' ht' htt' => hS.scls_disj (Finset.mem_range.mp ht)
          (Finset.mem_range.mp ht') htt')]
      rw [← items_card (hI.inj p hLp)]
      refine Finset.card_le_card (fun v hv => ?_)
      obtain ⟨t, ht, hvt⟩ := Finset.mem_biUnion.mp hv
      exact (hnew_items t (Finset.mem_range.mp ht) v hvt).1
    have hb := Chazelle.Separator.sum_split_bound (Finset.range 3) (fun t => len (scls e t))
      (len p) s hsizes (fun t ht => hS.half t (Finset.mem_range.mp ht)) hbig
    have hb3 : 3 * k * (s + ∑ t ∈ Finset.range 3, (2 * len (scls e t) - s)) ≤
        3 * k * (2 * len p - s) := Nat.mul_le_mul_left _ hb
    rw [Nat.mul_add, Finset.mul_sum] at hb3
    have hsc : s * sep.card ≤ s * (3 * k) := Nat.mul_le_mul_left _ hS.card
    have : s * (3 * k) = 3 * k * s := by ring
    rw [Nat.mul_add]
    omega
  · -- the split counter
    have hpot := hI.pot2
    have hpr : p ∉ rest := (List.nodup_cons.mp hI.nodup).1
    rw [List.toFinset_cons, Finset.sum_insert (by simpa using hpr)] at hpot
    rw [List.toFinset_append]
    have hdn : Disjoint news.toFinset rest.toFinset := by
      rw [Finset.disjoint_left]
      intro q h1 h2
      obtain ⟨t, ht, rfl, hb⟩ := (hnews q).mp (List.mem_toFinset.mp h1)
      have hq2' : Lv (p :: rest) fin (scls e t) :=
        Or.inl (List.mem_cons_of_mem _ (List.mem_toFinset.mp h2))
      have hrd := hI.rdisj _ p hq2' hLp (hclsp t ht).1
      obtain ⟨a, b, c⟩ := hS.scls_in ht
      unfold len at hb hbig
      simp only [scls] at hrd hb
      rcases hrd with h | h | h | h <;> omega
    rw [Finset.sum_union hdn]
    have hsub : news.toFinset ⊆ (Finset.range 3).image (scls e) := by
      intro q hq
      obtain ⟨t, ht, rfl, _⟩ := (hnews q).mp (List.mem_toFinset.mp hq)
      exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, rfl⟩
    have hnewsum : ∑ q ∈ news.toFinset, (2 * len q - s) ≤
        ∑ t ∈ Finset.range 3, (2 * len (scls e t) - s) :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))
        (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _))
    have hsizes : ∑ t ∈ Finset.range 3, len (scls e t) ≤ len p := by
      have hcard : ∀ t, t < 3 → (items act' (scls e t)).card = len (scls e t) :=
        fun t ht => items_card (hS.scls_inj ht)
      rw [← Finset.sum_congr rfl (fun t ht => hcard t (Finset.mem_range.mp ht)),
        ← Finset.card_biUnion (fun t ht t' ht' htt' => hS.scls_disj (Finset.mem_range.mp ht)
          (Finset.mem_range.mp ht') htt')]
      rw [← items_card (hI.inj p hLp)]
      refine Finset.card_le_card (fun v hv => ?_)
      obtain ⟨t, ht, hvt⟩ := Finset.mem_biUnion.mp hv
      exact (hnew_items t (Finset.mem_range.mp ht) v hvt).1
    have hb := Chazelle.Separator.sum_split_bound (Finset.range 3) (fun t => len (scls e t))
      (len p) s hsizes (fun t ht => hS.half t (Finset.mem_range.mp ht)) hbig
    rw [Nat.add_mul, one_mul]
    omega

/-- **The size potential of a split**: `Σ_{classes} |C| · size |C| + |P| ≤ |P| · size |P|`
when the classes have at most half of `|P|` items each and at most `|P|` in total. -/
theorem split_size_pot (m : ℕ → ℕ) (M : ℕ) (hsum : ∑ t ∈ Finset.range 3, m t ≤ M)
    (hhalf : ∀ t, t < 3 → 2 * m t ≤ M) :
    ∑ t ∈ Finset.range 3, m t * Nat.size (m t) + M ≤ M * Nat.size M := by
  have hsz : ∀ t, t < 3 → m t * Nat.size (m t) + m t ≤ m t * Nat.size M := by
    intro t ht
    rcases Nat.eq_zero_or_pos (m t) with h0 | hpos
    · rw [h0]; simp
    · have h2 : Nat.size (2 * m t) ≤ Nat.size M := Nat.size_le_size (hhalf t ht)
      have h3 : Nat.size (2 * m t) = Nat.size (m t) + 1 := by
        rw [show 2 * m t = m t <<< 1 by rw [Nat.shiftLeft_eq_mul_pow]; ring]
        exact Nat.size_shiftLeft (by omega) 1
      calc m t * Nat.size (m t) + m t = m t * (Nat.size (m t) + 1) := by ring
        _ ≤ m t * Nat.size M := Nat.mul_le_mul_left _ (by omega)
  have h1 : ∑ t ∈ Finset.range 3, (m t * Nat.size (m t) + m t) ≤
      ∑ t ∈ Finset.range 3, m t * Nat.size M :=
    Finset.sum_le_sum (fun t ht => hsz t (Finset.mem_range.mp ht))
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h1
  have h2 : (∑ t ∈ Finset.range 3, m t) * Nat.size M ≤ M * Nat.size M :=
    Nat.mul_le_mul_right _ hsum
  -- `M ≤ |P| size |P| - Σ |C| size |C|` needs `M ≤ (M - Σ) size M + Σ`: fine when `size M ≥ 1`
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have : ∀ t ∈ Finset.range 3, m t = 0 := fun t ht => by
      have := hhalf t (Finset.mem_range.mp ht); omega
    rw [Finset.sum_congr rfl (fun t ht => by rw [this t ht])]
    simp
  · have hs1 : 1 ≤ Nat.size M := Nat.size_pos.mpr hM
    have h3 : (M - ∑ t ∈ Finset.range 3, m t) ≤ (M - ∑ t ∈ Finset.range 3, m t) * Nat.size M :=
      Nat.le_mul_of_pos_right _ hs1
    have h4 : (M - ∑ t ∈ Finset.range 3, m t) * Nat.size M + (∑ t ∈ Finset.range 3, m t) *
        Nat.size M = M * Nat.size M := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hsum]
    omega

end stack

end

end Chazelle.Core.Cluster
