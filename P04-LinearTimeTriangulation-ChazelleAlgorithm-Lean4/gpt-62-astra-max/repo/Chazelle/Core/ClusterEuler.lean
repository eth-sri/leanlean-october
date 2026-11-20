module

public import Chazelle.Core.ClusterMap

/-!
# WP-I, part 8: preorder intervals of a tree in breadth-first order

A rooted tree on the nodes `[0, n)` given as a breadth-first search leaves it (`BTree`): the
queue `q` (a bijection of `[0, n)`, the root `q 0` first) and the parent `par h` of every other
node, which comes earlier in the queue.

* `BTree.Anc g h`: `g` is on the path from `h` to the root; `sub g` (the descendants),
  `sub_eq` (`sub g = {g} ⊔ ⋃ sub c` over the children), hence `card_sub` (the size recursion).
* **Sizes** (`SizeInv`): processing the queue backwards and adding the size of every node to its
  parent computes `|sub g|`.
* **Preorder** (`PreInv`): processing the queue forwards, every node takes the next free slot of
  its parent and advances it by its size.  At the end (`PreInv.final`) the preorder `pre` is
  injective and the descendants of `g` are exactly the nodes whose preorder lies in
  `[pre g, pre g + |sub g|)` (`PreInv.anc_iff`).
-/

namespace Chazelle.Core.Cluster

@[expose] public section

/-- A tree in breadth-first order on the nodes `[0, n)`. -/
structure BTree where
  /-- number of nodes -/
  n : ℕ
  /-- the queue -/
  q : ℕ → ℕ
  /-- the parent of a non-root node -/
  par : ℕ → ℕ

namespace BTree

variable (R : BTree)

/-- Well-formedness: the queue is a bijection of `[0, n)` and parents come earlier. -/
structure OK : Prop where
  n_pos : 0 < R.n
  q_lt : ∀ i, i < R.n → R.q i < R.n
  q_inj : ∀ i, i < R.n → ∀ j, j < R.n → R.q i = R.q j → i = j
  par_lt : ∀ i, 0 < i → i < R.n → ∃ j, j < i ∧ R.q j = R.par (R.q i)

/-- The root. -/
def root : ℕ := R.q 0

/-- The parent, the root being its own parent. -/
def up (h : ℕ) : ℕ := if h = R.root then h else R.par h

/-- `g` is an ancestor of `h` (reflexive). -/
def Anc (g h : ℕ) : Prop := ∃ m : ℕ, R.up^[m] h = g

/-- The descendants of `g`. -/
noncomputable def sub (g : ℕ) : Finset ℕ :=
  haveI := Classical.decPred (fun h => R.Anc g h)
  (Finset.range R.n).filter (fun h => R.Anc g h)

/-- The children of `g`. -/
noncomputable def ch (g : ℕ) : Finset ℕ :=
  (Finset.range R.n).filter (fun h => h ≠ R.root ∧ R.par h = g)

variable {R}

theorem OK.surj (hR : R.OK) {h : ℕ} (hh : h < R.n) : ∃ i, i < R.n ∧ R.q i = h := by
  classical
  have hsub : (Finset.range R.n).image R.q ⊆ Finset.range R.n := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hR.q_lt i (Finset.mem_range.mp hi))
  have hcard : ((Finset.range R.n).image R.q).card = R.n := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact hR.q_inj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
  have : h ∈ (Finset.range R.n).image R.q := by rw [heq]; exact Finset.mem_range.mpr hh
  obtain ⟨i, hi, hqi⟩ := Finset.mem_image.mp this
  exact ⟨i, Finset.mem_range.mp hi, hqi⟩

open Classical in
/-- The position of a node in the queue. -/
noncomputable def pos (h : ℕ) : ℕ := if hh : ∃ i, i < R.n ∧ R.q i = h then Nat.find hh else 0

theorem OK.pos_spec (hR : R.OK) {h : ℕ} (hh : h < R.n) : R.pos h < R.n ∧ R.q (R.pos h) = h := by
  classical
  have hex := hR.surj hh
  unfold pos
  rw [dite_eq_left hex]
  exact Nat.find_spec hex

theorem OK.pos_q (hR : R.OK) {i : ℕ} (hi : i < R.n) : R.pos (R.q i) = i := by
  have := hR.pos_spec (hR.q_lt i hi)
  exact hR.q_inj _ this.1 i hi this.2

theorem OK.root_lt (hR : R.OK) : R.root < R.n := hR.q_lt 0 hR.n_pos

theorem OK.pos_root (hR : R.OK) : R.pos R.root = 0 := hR.pos_q hR.n_pos

/-- The parent of a non-root node is a node earlier in the queue. -/
theorem OK.par_spec (hR : R.OK) {h : ℕ} (hh : h < R.n) (hr : h ≠ R.root) :
    R.par h < R.n ∧ R.pos (R.par h) < R.pos h := by
  obtain ⟨hp, hq⟩ := hR.pos_spec hh
  have h0 : 0 < R.pos h := by
    rcases Nat.eq_zero_or_pos (R.pos h) with h0 | h0
    · exact absurd (by rw [← hq, h0]; rfl) hr
    · exact h0
  obtain ⟨j, hj, hqj⟩ := hR.par_lt (R.pos h) h0 hp
  rw [hq] at hqj
  rw [← hqj, hR.pos_q (by omega)]
  exact ⟨hR.q_lt j (by omega), hj⟩

theorem OK.up_lt (hR : R.OK) {h : ℕ} (hh : h < R.n) : R.up h < R.n := by
  unfold up
  split_ifs with hr
  · exact hh
  · exact (hR.par_spec hh hr).1

theorem OK.iterate_up_lt (hR : R.OK) (m : ℕ) {h : ℕ} (hh : h < R.n) : R.up^[m] h < R.n := by
  induction m generalizing h with
  | zero => exact hh
  | succ m ih => rw [Function.iterate_succ_apply]; exact ih (hR.up_lt hh)

/-- Ancestors come no later in the queue. -/
theorem OK.pos_le_of_anc (hR : R.OK) {g h : ℕ} (hh : h < R.n) (hgh : R.Anc g h) :
    R.pos g ≤ R.pos h := by
  obtain ⟨m, rfl⟩ := hgh
  induction m generalizing h with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    refine (ih (hR.up_lt hh)).trans ?_
    unfold up
    split_ifs with hr
    · exact le_rfl
    · exact (hR.par_spec hh hr).2.le

theorem anc_refl (g : ℕ) : R.Anc g g := ⟨0, rfl⟩

theorem anc_up (h : ℕ) : R.Anc (R.up h) h := ⟨1, rfl⟩

theorem Anc.trans {a b c : ℕ} (h1 : R.Anc a b) (h2 : R.Anc b c) : R.Anc a c := by
  obtain ⟨m1, rfl⟩ := h1
  obtain ⟨m2, rfl⟩ := h2
  exact ⟨m1 + m2, by rw [Function.iterate_add_apply]⟩

/-- Anti-symmetry of ancestry. -/
theorem OK.anc_antisymm (hR : R.OK) {g h : ℕ} (hh : h < R.n) (hg : g < R.n) (h1 : R.Anc g h)
    (h2 : R.Anc h g) : g = h := by
  have := hR.pos_le_of_anc hh h1
  have := hR.pos_le_of_anc hg h2
  have e1 := (hR.pos_spec hg).2
  have e2 := (hR.pos_spec hh).2
  rw [← e1, ← e2, show R.pos g = R.pos h by omega]

/-- The root is an ancestor of every node. -/
theorem OK.anc_root (hR : R.OK) {h : ℕ} (hh : h < R.n) : R.Anc R.root h := by
  induction hp : R.pos h using Nat.strong_induction_on generalizing h with
  | _ p ih =>
    by_cases hr : h = R.root
    · rw [hr]; exact anc_refl _
    · obtain ⟨hpn, hpp⟩ := hR.par_spec hh hr
      have := ih (R.pos (R.par h)) (by omega) hpn rfl
      refine this.trans ?_
      have : R.up h = R.par h := by simp [up, hr]
      rw [← this]; exact anc_up h

/-- Stepping up from a proper descendant. -/
theorem anc_iff_up {g h : ℕ} (hgh : g ≠ h) : R.Anc g h ↔ R.Anc g (R.up h) := by
  constructor
  · rintro ⟨m, hm⟩
    rcases m with _ | m
    · exact absurd hm.symm hgh
    · exact ⟨m, by rw [Function.iterate_succ_apply] at hm; exact hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨m + 1, by rw [Function.iterate_succ_apply]; exact hm⟩

/-- **The descendants of `g`**: `g` and the descendants of its children, disjointly. -/
theorem OK.sub_eq (hR : R.OK) {g : ℕ} (hg : g < R.n) :
    R.sub g = insert g ((R.ch g).biUnion R.sub) := by
  classical
  ext h
  simp only [sub, ch, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hh, hgh⟩
    by_cases heq : h = g
    · exact Or.inl heq
    · right
      -- the child of `g` on the path from `h`
      obtain ⟨m, hm⟩ := hgh
      have key : ∀ m h, h < R.n → R.up^[m] h = g → h ≠ g →
          ∃ c, (c < R.n ∧ c ≠ R.root ∧ R.par c = g) ∧ h < R.n ∧ R.Anc c h := by
        intro m
        induction m with
        | zero => intro h _ hm hne; exact absurd hm hne
        | succ m ih =>
          intro h hh hm hne
          rw [Function.iterate_succ_apply] at hm
          have hr : h ≠ R.root := by
            intro hr
            have : R.up^[m] (R.up h) = R.up h := by
              rw [show R.up h = h by simp [up, hr]]
              exact Function.iterate_fixed (by simp [up, hr]) m
            rw [this, show R.up h = h by simp [up, hr]] at hm
            exact hne hm
          have hup : R.up h = R.par h := by simp [up, hr]
          by_cases hpg : R.par h = g
          · exact ⟨h, ⟨hh, hr, hpg⟩, hh, anc_refl h⟩
          · obtain ⟨c, hc, -, hch⟩ := ih (R.up h) (hR.up_lt hh) hm (by rw [hup]; exact hpg)
            exact ⟨c, hc, hh, hch.trans (anc_up h)⟩
      exact key m h hh hm heq
  · rintro (rfl | ⟨c, ⟨hc, hcr, hpc⟩, hh, hch⟩)
    · exact ⟨hg, anc_refl h⟩
    · refine ⟨hh, Anc.trans ?_ hch⟩
      have : R.up c = g := by simp [up, hcr, hpc]
      rw [← this]; exact anc_up c

/-- Descendants of distinct children are disjoint. -/
theorem OK.sub_disjoint (hR : R.OK) {g c c' : ℕ} (hc : c ∈ R.ch g) (hc' : c' ∈ R.ch g)
    (hne : c ≠ c') : Disjoint (R.sub c) (R.sub c') := by
  classical
  rw [Finset.disjoint_left]
  intro h h1 h2
  simp only [sub, ch, Finset.mem_filter, Finset.mem_range] at h1 h2 hc hc'
  -- both `c` and `c'` are ancestors of `h`, so one is an ancestor of the other
  have key : ∀ m m' h, R.up^[m] h = c → R.up^[m'] h = c' → R.Anc c c' ∨ R.Anc c' c := by
    intro m m' h hm hm'
    rcases le_total m m' with hle | hle
    · right; refine ⟨m' - m, ?_⟩
      rw [← hm', ← hm, ← Function.iterate_add_apply]; congr 1; omega
    · left; refine ⟨m - m', ?_⟩
      rw [← hm', ← hm, ← Function.iterate_add_apply]; congr 1; omega
  obtain ⟨m, hm⟩ := h1.2
  obtain ⟨m', hm'⟩ := h2.2
  -- a child of `g` that is an ancestor of another child of `g` is that child
  have hup : ∀ x, x < R.n → x ≠ R.root → R.par x = g → R.up x = g := fun x _ hxr hpx => by
    simp [up, hxr, hpx]
  have hchild : ∀ x y, x < R.n → y < R.n → x ≠ R.root → y ≠ R.root → R.par x = g →
      R.par y = g → R.Anc x y → x = y := by
    intro x y hx hy hxr hyr hpx hpy hxy
    by_contra hxy'
    have h1 := (anc_iff_up hxy').mp hxy
    rw [hup y hy hyr hpy] at h1
    have h2 : R.Anc g x := by rw [← hup x hx hxr hpx]; exact anc_up x
    have hgn : g < R.n := by rw [← hpx]; exact (hR.par_spec hx hxr).1
    have hxg : x = g := hR.anc_antisymm hgn hx h1 h2
    have hl := hR.par_spec hx hxr
    rw [hpx, ← hxg] at hl
    omega
  rcases key m m' h hm hm' with h3 | h3
  · exact hne (hchild c c' hc.1 hc'.1 hc.2.1 hc'.2.1 hc.2.2 hc'.2.2 h3)
  · exact hne (hchild c' c hc'.1 hc.1 hc'.2.1 hc.2.1 hc'.2.2 hc.2.2 h3).symm

/-- A child comes after its parent in the queue. -/
theorem OK.pos_ch (hR : R.OK) {g c : ℕ} (hc : c ∈ R.ch g) : R.pos g < R.pos c := by
  simp only [ch, Finset.mem_filter, Finset.mem_range] at hc
  have := hR.par_spec hc.1 hc.2.1
  rw [hc.2.2] at this
  exact this.2

/-- A node is not a descendant of its own children. -/
theorem OK.notMem_sub_ch (hR : R.OK) {g c : ℕ} (hc : c ∈ R.ch g) : g ∉ R.sub c := by
  intro hg
  simp only [sub, Finset.mem_filter, Finset.mem_range] at hg
  have := hR.pos_le_of_anc hg.1 hg.2
  have := hR.pos_ch hc
  omega

/-- **The size recursion**: `|sub g| = 1 + Σ_{c child of g} |sub c|`. -/
theorem OK.card_sub (hR : R.OK) {g : ℕ} (hg : g < R.n) :
    (R.sub g).card = 1 + ∑ c ∈ R.ch g, (R.sub c).card := by
  classical
  rw [hR.sub_eq hg, Finset.card_insert_of_notMem, Finset.card_biUnion]
  · omega
  · intro c hc c' hc' hne
    exact hR.sub_disjoint hc hc' hne
  · simp only [Finset.mem_biUnion, not_exists, not_and]
    intro c hc
    exact hR.notMem_sub_ch hc

/-- The root's subtree is everything. -/
theorem OK.card_sub_root (hR : R.OK) : (R.sub R.root).card = R.n := by
  classical
  have : R.sub R.root = Finset.range R.n := by
    ext h
    simp only [sub, Finset.mem_filter, Finset.mem_range, and_iff_left_iff_imp]
    exact fun hh => hR.anc_root hh
  rw [this, Finset.card_range]

/-! ## Sizes -/

/-- **The invariant of the size loop** (queue entries from `i` on processed): the size array holds
`1 + Σ |sub c|` over the processed children. -/
def SizeInv (sz : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ g, g < R.n → sz g = 1 + ∑ c ∈ (R.ch g).filter (fun c => i ≤ R.pos c), (R.sub c).card

/-- The start: all sizes `1`. -/
theorem SizeInv.init {sz : ℕ → ℕ} (h : ∀ g, g < R.n → sz g = 1) (hR : R.OK) :
    R.SizeInv sz R.n := by
  intro g hg
  have hempty : (R.ch g).filter (fun c => R.n ≤ R.pos c) = ∅ := by
    refine Finset.filter_false_of_mem (fun c hc => ?_)
    simp only [ch, Finset.mem_filter, Finset.mem_range] at hc
    have := (hR.pos_spec hc.1).1
    omega
  rw [h g hg, hempty, Finset.sum_empty]; rfl

/-- At an entry, the size array holds the true size. -/
theorem SizeInv.eq_card (hR : R.OK) {sz : ℕ → ℕ} {i : ℕ} (hS : R.SizeInv sz (i + 1))
    (hi : i < R.n) : sz (R.q i) = (R.sub (R.q i)).card := by
  rw [hS _ (hR.q_lt i hi), hR.card_sub (hR.q_lt i hi)]
  congr 1
  refine Finset.sum_congr (Finset.filter_true_of_mem (fun c hc => ?_)) (fun _ _ => rfl)
  have := hR.pos_ch hc
  rw [hR.pos_q hi] at this
  omega

/-- **One step of the size loop**: at the entry `i ≥ 1`, add its size to its parent. -/
theorem SizeInv.step (hR : R.OK) {sz : ℕ → ℕ} {i : ℕ} (hS : R.SizeInv sz (i + 1))
    (hi0 : 0 < i) (hi : i < R.n) :
    R.SizeInv (Function.update sz (R.par (R.q i)) (sz (R.par (R.q i)) + sz (R.q i))) i := by
  classical
  have hq := hR.q_lt i hi
  have hr : R.q i ≠ R.root := by
    intro h; have := hR.q_inj i hi 0 hR.n_pos h; omega
  have hpos : R.pos (R.q i) = i := hR.pos_q hi
  intro g hg
  have hch : ∀ c, c ∈ (R.ch g).filter (fun c => i ≤ R.pos c) ↔
      c ∈ (R.ch g).filter (fun c => i + 1 ≤ R.pos c) ∨ (c = R.q i ∧ R.par (R.q i) = g) := by
    intro c
    simp only [Finset.mem_filter, ch, Finset.mem_range]
    constructor
    · rintro ⟨⟨hc, hcr, hpc⟩, hic⟩
      by_cases hci : R.pos c = i
      · right
        have := (hR.pos_spec hc).2
        rw [hci] at this
        exact ⟨this.symm, by rw [this]; exact hpc⟩
      · exact Or.inl ⟨⟨hc, hcr, hpc⟩, by omega⟩
    · rintro (⟨⟨hc, hcr, hpc⟩, hic⟩ | ⟨rfl, hpg⟩)
      · exact ⟨⟨hc, hcr, hpc⟩, by omega⟩
      · exact ⟨⟨hq, hr, hpg⟩, by omega⟩
  by_cases hpg : R.par (R.q i) = g
  · subst hpg
    rw [Function.update_self, hS _ hg, hS.eq_card hR hi]
    have hset : (R.ch (R.par (R.q i))).filter (fun c => i ≤ R.pos c) =
        insert (R.q i) ((R.ch (R.par (R.q i))).filter (fun c => i + 1 ≤ R.pos c)) := by
      ext c; rw [hch c, Finset.mem_insert]; tauto
    rw [hset, Finset.sum_insert]
    · ring
    · simp only [Finset.mem_filter]; omega
  · rw [Function.update_of_ne (Ne.symm hpg), hS _ hg]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext c
    rw [hch c]
    constructor
    · intro h
      exact Or.inl h
    · intro h
      rcases h with h | h
      · exact h
      · exact absurd h.2 hpg

/-- At the end of the size loop, the sizes are the true sizes. -/
theorem SizeInv.final (hR : R.OK) {sz : ℕ → ℕ} (hS : R.SizeInv sz 1) {g : ℕ} (hg : g < R.n) :
    sz g = (R.sub g).card := by
  rw [hS g hg, hR.card_sub hg]
  congr 1
  refine Finset.sum_congr (Finset.filter_true_of_mem (fun c hc => ?_)) (fun _ _ => rfl)
  have := hR.pos_ch hc
  omega

theorem mem_ch {g x : ℕ} : x ∈ R.ch g ↔ x < R.n ∧ x ≠ R.root ∧ R.par x = g := by
  simp [ch]

/-- A subtree has at most `n` nodes. -/
theorem card_sub_le (g : ℕ) : (R.sub g).card ≤ R.n := by
  classical
  unfold sub
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])

/-- During the size loop, sizes are at most the true sizes. -/
theorem SizeInv.le (hR : R.OK) {sz : ℕ → ℕ} {i : ℕ} (hS : R.SizeInv sz i) {g : ℕ}
    (hg : g < R.n) : sz g ≤ (R.sub g).card := by
  rw [hS g hg, hR.card_sub hg]
  have := Finset.sum_le_sum_of_subset (f := fun c => (R.sub c).card)
    (Finset.filter_subset (fun c => i ≤ R.pos c) (R.ch g))
  omega

/-! ## Preorder -/

/-- **The invariant of the preorder loop** (queue entries before `i` processed): the next free
slot of a processed node follows its processed children; a processed non-root node has its
interval `[pre c, pre c + |sub c|)` inside the used part of its parent's; processed siblings have
disjoint intervals. -/
structure PreInv (pre slot : ℕ → ℕ) (i : ℕ) : Prop where
  i_pos : 0 < i
  i_le : i ≤ R.n
  root : pre R.root = 0
  slotEq : ∀ j, j < i → slot (R.q j) =
    pre (R.q j) + 1 + ∑ c ∈ (R.ch (R.q j)).filter (fun c => R.pos c < i), (R.sub c).card
  nest : ∀ j, 0 < j → j < i →
    pre (R.par (R.q j)) + 1 ≤ pre (R.q j) ∧
      pre (R.q j) + (R.sub (R.q j)).card ≤ slot (R.par (R.q j))
  disj : ∀ j j', 0 < j → j < i → 0 < j' → j' < i → j ≠ j' → R.par (R.q j) = R.par (R.q j') →
    pre (R.q j) + (R.sub (R.q j)).card ≤ pre (R.q j') ∨
      pre (R.q j') + (R.sub (R.q j')).card ≤ pre (R.q j)
  bound : ∀ j, j < i → pre (R.q j) + (R.sub (R.q j)).card ≤ R.n

/-- The start: the root takes preorder `0` and next slot `1`. -/
theorem PreInv.init (hR : R.OK) {pre slot : ℕ → ℕ} (hp : pre R.root = 0) (hs : slot R.root = 1) :
    R.PreInv pre slot 1 := by
  classical
  refine ⟨by omega, hR.n_pos, hp, fun j hj => ?_, fun j hj0 hj => by omega,
    fun j j' hj0 hj _ _ _ _ => by omega, fun j hj => ?_⟩
  swap
  · have hj0 : j = 0 := by omega
    subst hj0
    show pre R.root + (R.sub R.root).card ≤ R.n
    rw [hp, hR.card_sub_root]; omega
  have hj0 : j = 0 := by omega
  subst hj0
  have hempty : (R.ch (R.q 0)).filter (fun c => R.pos c < 1) = ∅ := by
    refine Finset.filter_false_of_mem (fun c hc => ?_)
    have := hR.pos_ch hc
    rw [hR.pos_q hR.n_pos] at this
    omega
  rw [hempty, Finset.sum_empty]
  show slot R.root = pre R.root + 1 + 0
  rw [hp, hs]

/-- **One step of the preorder loop**: the entry `i ≥ 1` takes the next free slot of its parent,
which advances by its size; its own next free slot follows it. -/
theorem PreInv.step (hR : R.OK) {pre slot : ℕ → ℕ} {i : ℕ} (hP : R.PreInv pre slot i)
    (hi : i < R.n) :
    R.PreInv (Function.update pre (R.q i) (slot (R.par (R.q i))))
      (Function.update (Function.update slot (R.par (R.q i))
        (slot (R.par (R.q i)) + (R.sub (R.q i)).card)) (R.q i) (slot (R.par (R.q i)) + 1))
      (i + 1) := by
  classical
  set c := R.q i with hc_def
  set p := R.par c with hp_def
  have hcn : c < R.n := hR.q_lt i hi
  have hcr : c ≠ R.root := by
    intro h; have := hR.q_inj i hi 0 hR.n_pos h; have := hP.i_pos; omega
  have hposc : R.pos c = i := hR.pos_q hi
  obtain ⟨hpn, hpp⟩ := hR.par_spec hcn hcr
  rw [hposc, ← hp_def] at hpp
  rw [← hp_def] at hpn
  have hpq : R.q (R.pos p) = p := (hR.pos_spec hpn).2
  have hpc : p ≠ c := fun h => by rw [h] at hpp; omega
  -- facts about processed entries
  have hne : ∀ j, j < i → R.q j ≠ c := by
    intro j hj h; have := hR.q_inj j (by omega) i hi h; omega
  have pre_old : ∀ j, j < i → Function.update pre c (slot p) (R.q j) = pre (R.q j) :=
    fun j hj => Function.update_of_ne (hne j hj) _ _
  have hchild_pos : ∀ x, x ∈ R.ch c → i < R.pos x := by
    intro x hx; have := hR.pos_ch hx; omega
  -- the slot of the parent covers the processed children
  have hslot_p := hP.slotEq (R.pos p) hpp
  rw [hpq] at hslot_p
  refine ⟨by omega, by omega, ?_, fun j hj => ?_, fun j hj0 hj => ?_,
    fun j j' hj0 hj hj0' hj' hjj' hpar => ?_, fun j hj => ?_⟩
  rotate_right
  · -- the bound
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hji
    · rw [pre_old j hj]; exact hP.bound j hj
    · rw [hji, Function.update_self]
      have hb := hP.bound (R.pos p) hpp
      rw [hpq] at hb
      have hcp : c ∈ R.ch p := mem_ch.mpr ⟨hcn, hcr, rfl⟩
      have hsub : insert c ((R.ch p).filter (fun x => R.pos x < i)) ⊆ R.ch p := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hcp
        · exact (Finset.mem_filter.mp hx).1
      have hsum := Finset.sum_le_sum_of_subset (f := fun x => (R.sub x).card) hsub
      rw [Finset.sum_insert (fun h => by
        rw [Finset.mem_filter, hposc] at h; exact lt_irrefl _ h.2)] at hsum
      have hcs := hR.card_sub hpn
      show slot p + (R.sub c).card ≤ R.n
      omega
  · rw [Function.update_of_ne (fun h => hcr h.symm)]; exact hP.root
  · -- slots
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hji
    · have hqc := hne j hj
      rw [pre_old j hj, Function.update_of_ne hqc]
      by_cases hjp : R.q j = p
      · have hset : (R.ch (R.q j)).filter (fun x => R.pos x < i + 1) =
            insert c ((R.ch (R.q j)).filter (fun x => R.pos x < i)) := by
          ext x
          rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter, mem_ch]
          constructor
          · rintro ⟨⟨hx, hxr, hxp⟩, hxi⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hxi with hxi | hxi
            · exact Or.inr ⟨⟨hx, hxr, hxp⟩, hxi⟩
            · left
              have := (hR.pos_spec hx).2
              rw [hxi] at this; exact this.symm
          · rintro (rfl | ⟨hx, hxi⟩)
            · exact ⟨⟨hcn, hcr, by rw [hjp]⟩, by omega⟩
            · exact ⟨hx, by omega⟩
        rw [hset, hjp, Function.update_self, Finset.sum_insert (fun h => by
          rw [Finset.mem_filter, hposc] at h; exact lt_irrefl _ h.2), hslot_p]
        ring
      · have hset : (R.ch (R.q j)).filter (fun x => R.pos x < i + 1) =
            (R.ch (R.q j)).filter (fun x => R.pos x < i) := by
          ext x
          rw [Finset.mem_filter, Finset.mem_filter]
          constructor
          · rintro ⟨hx, hxi⟩
            refine ⟨hx, ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hxi with hxi | hxi
            · exact hxi
            · exfalso
              obtain ⟨hxn, -, hxp⟩ := mem_ch.mp hx
              have := (hR.pos_spec hxn).2
              rw [hxi] at this
              exact hjp (by rw [← hxp, ← this])
          · rintro ⟨hx, hxi⟩; exact ⟨hx, by omega⟩
        rw [hset, Function.update_of_ne hjp]
        exact hP.slotEq j hj
    · -- the new entry
      rw [hji, Function.update_self, Function.update_self]
      have hempty : (R.ch c).filter (fun x => R.pos x < i + 1) = ∅ :=
        Finset.filter_false_of_mem (fun x hx => by have := hchild_pos x hx; omega)
      rw [hempty, Finset.sum_empty]; rfl
  · -- nesting
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hji
    · obtain ⟨n1, n2⟩ := hP.nest j hj0 hj
      have hqp : R.par (R.q j) ≠ c := by
        intro h
        have := (hR.par_spec (hR.q_lt j (by omega)) (fun h' => by
          have := hR.q_inj j (by omega) 0 hR.n_pos h'; omega)).2
        rw [h, hposc, hR.pos_q (by omega)] at this
        omega
      rw [pre_old j hj, Function.update_of_ne hqp]
      refine ⟨n1, ?_⟩
      rw [Function.update_of_ne hqp]
      by_cases hjp : R.par (R.q j) = p
      · rw [hjp, Function.update_self]; rw [hjp] at n2; omega
      · rw [Function.update_of_ne hjp]; exact n2
    · rw [hji, Function.update_self, Function.update_of_ne hpc, Function.update_of_ne hpc,
        Function.update_self]
      constructor
      · rw [hslot_p]; omega
      · exact le_refl _
  · -- disjointness
    have hcase : ∀ j j', 0 < j → j < i → j' = i → R.par (R.q j) = R.par (R.q j') →
        Function.update pre c (slot p) (R.q j) + (R.sub (R.q j)).card ≤
          Function.update pre c (slot p) (R.q j') := by
      intro j j' hj0 hj hj' hpar
      subst hj'
      rw [pre_old j hj, Function.update_self]
      have := (hP.nest j hj0 hj).2
      rw [hpar] at this
      exact this
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hji <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | hji'
    · rw [pre_old j hj, pre_old j' hj']
      exact hP.disj j j' hj0 hj hj0' hj' hjj' hpar
    · exact Or.inl (hcase j j' hj0 hj hji' hpar)
    · exact Or.inr (hcase j' j hj0' hj' hji hpar.symm)
    · exact absurd (hji.trans hji'.symm) hjj'

section final

variable {pre slot : ℕ → ℕ}

theorem one_le_card_sub {g : ℕ} (hg : g < R.n) : 1 ≤ (R.sub g).card := by
  classical
  refine Finset.card_pos.mpr ⟨g, ?_⟩
  simp only [sub, Finset.mem_filter, Finset.mem_range]
  exact ⟨hg, anc_refl g⟩

/-- At the end, every next free slot is at the end of the interval. -/
theorem PreInv.slot_final (hR : R.OK) (hP : R.PreInv pre slot R.n) {g : ℕ} (hg : g < R.n) :
    slot g = pre g + (R.sub g).card := by
  obtain ⟨hpn, hpq⟩ := hR.pos_spec hg
  have := hP.slotEq (R.pos g) hpn
  rw [hpq] at this
  rw [this, hR.card_sub hg]
  have : (R.ch g).filter (fun c => R.pos c < R.n) = R.ch g :=
    Finset.filter_true_of_mem (fun c hc => (hR.pos_spec (mem_ch.mp hc).1).1)
  rw [this]; ring

/-- At the end, the interval of a non-root node is inside its parent's, after the parent. -/
theorem PreInv.nest_final (hR : R.OK) (hP : R.PreInv pre slot R.n) {c : ℕ} (hc : c < R.n)
    (hcr : c ≠ R.root) :
    pre (R.par c) + 1 ≤ pre c ∧ pre c + (R.sub c).card ≤ pre (R.par c) + (R.sub (R.par c)).card := by
  obtain ⟨hpn, hpq⟩ := hR.pos_spec hc
  have h0 : 0 < R.pos c := by
    rcases Nat.eq_zero_or_pos (R.pos c) with h | h
    · exact absurd (by rw [← hpq, h]; rfl) hcr
    · exact h
  have := hP.nest (R.pos c) h0 hpn
  rw [hpq, hP.slot_final hR (hR.par_spec hc hcr).1] at this
  exact this

/-- Ancestors have enclosing intervals. -/
theorem PreInv.anc_le (hR : R.OK) (hP : R.PreInv pre slot R.n) {g h : ℕ} (hh : h < R.n)
    (hgh : R.Anc g h) :
    pre g ≤ pre h ∧ pre h + (R.sub h).card ≤ pre g + (R.sub g).card := by
  obtain ⟨m, rfl⟩ := hgh
  induction m generalizing h with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨i1, i2⟩ := ih (hR.up_lt hh)
    by_cases hr : h = R.root
    · rw [show R.up h = h by simp [up, hr]] at i1 i2 ⊢
      exact ⟨i1, i2⟩
    · have hup : R.up h = R.par h := by simp [up, hr]
      rw [hup] at i1 i2 ⊢
      obtain ⟨n1, n2⟩ := hP.nest_final hR hh hr
      exact ⟨by omega, by omega⟩

/-- A proper ancestor comes strictly earlier in preorder. -/
theorem PreInv.anc_lt (hR : R.OK) (hP : R.PreInv pre slot R.n) {g h : ℕ} (hh : h < R.n)
    (hgh : R.Anc g h) (hne : g ≠ h) : pre g < pre h := by
  have hgn : g < R.n := by obtain ⟨m, rfl⟩ := hgh; exact hR.iterate_up_lt m hh
  have hr : h ≠ R.root := by
    intro hr
    exact hne (hR.anc_antisymm hh hgn hgh (hr ▸ hR.anc_root hgn))
  have h1 := (anc_iff_up hne).mp hgh
  rw [show R.up h = R.par h by simp [up, hr]] at h1
  have := (hP.anc_le hR (hR.par_spec hh hr).1 h1).1
  have := (hP.nest_final hR hh hr).1
  omega

/-- The child of `p` on the path to a proper descendant `g`. -/
theorem OK.exists_ch_anc (hR : R.OK) {p g : ℕ} (hg : g < R.n) (hpg : R.Anc p g) (hne : p ≠ g) :
    ∃ c, c ∈ R.ch p ∧ R.Anc c g := by
  classical
  have hpn : p < R.n := by obtain ⟨m, rfl⟩ := hpg; exact hR.iterate_up_lt m hg
  have hmem : g ∈ R.sub p := by
    simp only [sub, Finset.mem_filter, Finset.mem_range]; exact ⟨hg, hpg⟩
  rw [hR.sub_eq hpn, Finset.mem_insert, Finset.mem_biUnion] at hmem
  rcases hmem with h | ⟨c, hc, hgc⟩
  · exact absurd h.symm hne
  · simp only [sub, Finset.mem_filter, Finset.mem_range] at hgc
    exact ⟨c, hc, hgc.2⟩

/-- The key step of the disjointness of unrelated nodes (the later one's parent). -/
theorem PreInv.disj_step (hR : R.OK) (hP : R.PreInv pre slot R.n) {g h : ℕ} (hg : g < R.n)
    (hh : h < R.n) (hgh : ¬ R.Anc g h) (hhg : ¬ R.Anc h g) (hpos : R.pos g < R.pos h)
    (ih : ∀ g' h', g' < R.n → h' < R.n → R.pos g' + R.pos h' < R.pos g + R.pos h →
      ¬ R.Anc g' h' → ¬ R.Anc h' g' →
        pre g' + (R.sub g').card ≤ pre h' ∨ pre h' + (R.sub h').card ≤ pre g') :
    pre g + (R.sub g).card ≤ pre h ∨ pre h + (R.sub h).card ≤ pre g := by
  have hr : h ≠ R.root := fun hr => hhg (hr ▸ hR.anc_root hg)
  obtain ⟨hpn, hpp⟩ := hR.par_spec hh hr
  have hup : R.up h = R.par h := by simp [up, hr]
  have hph : R.Anc (R.par h) h := hup ▸ anc_up h
  obtain ⟨nh1, nh2⟩ := hP.nest_final hR hh hr
  have hσh := one_le_card_sub (R := R) hh
  have hσg := one_le_card_sub (R := R) hg
  by_cases hgp : R.Anc g (R.par h)
  · exact absurd (hgp.trans hph) hgh
  by_cases hpg : R.Anc (R.par h) g
  · have hpne : R.par h ≠ g := fun h' => hgp (h' ▸ anc_refl _)
    obtain ⟨c, hc, hcg⟩ := hR.exists_ch_anc hg hpg hpne
    obtain ⟨hcn, hcr, hcp⟩ := mem_ch.mp hc
    have hch : c ≠ h := fun h' => hhg (h' ▸ hcg)
    -- `c` and `h` are distinct children of `p`
    obtain ⟨pcn, pcq⟩ := hR.pos_spec hcn
    obtain ⟨phn, phq⟩ := hR.pos_spec hh
    have hc0 : 0 < R.pos c := by
      rcases Nat.eq_zero_or_pos (R.pos c) with h0 | h0
      · exact absurd (by rw [← pcq, h0]; rfl) hcr
      · exact h0
    have hh0 : 0 < R.pos h := by omega
    have hd := hP.disj (R.pos c) (R.pos h) hc0 pcn hh0 phn
      (fun e => hch (by rw [← pcq, ← phq, e])) (by rw [pcq, phq, hcp])
    rw [pcq, phq] at hd
    obtain ⟨a1, a2⟩ := hP.anc_le hR hg hcg
    omega
  · have := ih g (R.par h) hg hpn (by omega) hgp hpg
    omega

/-- **Unrelated nodes have disjoint intervals.** -/
theorem PreInv.disj_unrel (hR : R.OK) (hP : R.PreInv pre slot R.n) :
    ∀ g h, g < R.n → h < R.n → ¬ R.Anc g h → ¬ R.Anc h g →
      pre g + (R.sub g).card ≤ pre h ∨ pre h + (R.sub h).card ≤ pre g := by
  intro g h
  induction hs : R.pos g + R.pos h using Nat.strong_induction_on generalizing g h with
  | _ s ih =>
    intro hg hh hgh hhg
    have ih' : ∀ g' h', g' < R.n → h' < R.n → R.pos g' + R.pos h' < R.pos g + R.pos h →
        ¬ R.Anc g' h' → ¬ R.Anc h' g' →
          pre g' + (R.sub g').card ≤ pre h' ∨ pre h' + (R.sub h').card ≤ pre g' :=
      fun g' h' a b c => ih _ (by omega) g' h' rfl a b
    have hgne : g ≠ h := fun e => hgh (e ▸ anc_refl g)
    have hposne : R.pos g ≠ R.pos h := by
      intro e
      exact hgne (by rw [← (hR.pos_spec hg).2, ← (hR.pos_spec hh).2, e])
    rcases Nat.lt_or_gt_of_ne hposne with hlt | hlt
    · exact hP.disj_step hR hg hh hgh hhg hlt ih'
    · have := hP.disj_step hR hh hg hhg hgh hlt (fun g' h' a b c d e => ih' g' h' a b
        (by omega) d e)
      omega

/-- **Preorder intervals**: at the end, `h` is a descendant of `g` iff `pre h` lies in
`[pre g, pre g + |sub g|)`; preorders are below `n`. -/
theorem PreInv.anc_iff (hR : R.OK) (hP : R.PreInv pre slot R.n) {g h : ℕ} (hg : g < R.n)
    (hh : h < R.n) : R.Anc g h ↔ pre g ≤ pre h ∧ pre h < pre g + (R.sub g).card := by
  have hσh := one_le_card_sub (R := R) hh
  constructor
  · intro hgh
    have := hP.anc_le hR hh hgh
    omega
  · rintro ⟨h1, h2⟩
    by_contra hgh
    by_cases hhg : R.Anc h g
    · have hne : h ≠ g := fun e => hgh (by rw [e]; exact anc_refl g)
      have := hP.anc_lt hR hg hhg hne
      omega
    · have := hP.disj_unrel hR g h hg hh hgh hhg
      omega

/-- Preorders are below `n`. -/
theorem PreInv.pre_lt (hR : R.OK) (hP : R.PreInv pre slot R.n) {h : ℕ} (hh : h < R.n) :
    pre h < R.n := by
  have := (hP.anc_iff hR hR.root_lt hh).mp (hR.anc_root hh)
  rw [hP.root, hR.card_sub_root] at this
  omega

end final

end BTree

end

end Chazelle.Core.Cluster
