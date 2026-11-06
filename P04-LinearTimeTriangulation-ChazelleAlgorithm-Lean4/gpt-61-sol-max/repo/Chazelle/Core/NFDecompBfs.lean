module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.NFDecompFinal2
public import Chazelle.Core.NFDecompTree

/-!
# Tree decomposition (WP-C), part 10: the breadth-first search

The search from region `0` over the record tree (chord `i` joins `up i` and `dn i`; `lst r` is
the exit-chord list of region `r`), as functions mirroring the RAM loops: `bstep` scans one chord
of the current region, `bouter` dequeues one region and scans its list.  `BInv` is the loop
invariant; when the queue is empty (`head = tail`) the search establishes `Rooted` together with
the child endpoint of every chord (`chOf`) and the side bit (`isdn`) (`bfs_rooted`).
-/

namespace Chazelle.Core.Dec

@[expose] public section

open Relation Finset


/-- The state of the search. -/
structure BS where
  /-- Visited regions (`1`). -/
  vis : ℕ → ℕ
  /-- The queue (the search order). -/
  ord : ℕ → ℕ
  /-- Parent regions. -/
  prg : ℕ → ℕ
  /-- Parent chords. -/
  pch : ℕ → ℕ
  /-- `1` iff the region is the `dn` endpoint of its parent chord. -/
  isdn : ℕ → ℕ
  /-- The child endpoint of each chord. -/
  chOf : ℕ → ℕ
  /-- The tail of the queue. -/
  tl : ℕ

section
variable (up dn : ℕ → ℕ)
include up dn
/-- Scan chord `i` from region `r`: discover its other endpoint if it is new. -/
def bstep (r : ℕ) (st : BS) (i : ℕ) : BS :=
  if st.vis (if up i = r then dn i else up i) = 1 then st
  else
    { vis := Function.update st.vis (if up i = r then dn i else up i) 1
      ord := Function.update st.ord st.tl (if up i = r then dn i else up i)
      prg := Function.update st.prg (if up i = r then dn i else up i) r
      pch := Function.update st.pch (if up i = r then dn i else up i) i
      isdn := Function.update st.isdn (if up i = r then dn i else up i) (if up i = r then 1 else 0)
      chOf := Function.update st.chOf i (if up i = r then dn i else up i)
      tl := st.tl + 1 }

/-- Dequeue the region at the head `q` and scan its exit chords. -/
def bouter (lst : ℕ → List ℕ) (st : BS) (q : ℕ) : BS :=
  (lst (st.ord q)).foldl (bstep up dn (st.ord q)) st


end

/-- The facts on a discovered (non-root) region. -/
def Disc (K : ℕ) (up dn : ℕ → ℕ) (st : BS) (q : ℕ) : Prop :=
  st.ord q ≠ 0 ∧ st.pch (st.ord q) < K ∧ (∃ q', q' < q ∧ st.prg (st.ord q) = st.ord q') ∧
    ((up (st.pch (st.ord q)) = st.prg (st.ord q) ∧ dn (st.pch (st.ord q)) = st.ord q) ∨
      (up (st.pch (st.ord q)) = st.ord q ∧ dn (st.pch (st.ord q)) = st.prg (st.ord q))) ∧
    (st.isdn (st.ord q) = 1 ↔ dn (st.pch (st.ord q)) = st.ord q) ∧
    st.chOf (st.pch (st.ord q)) = st.ord q

/-- **The search invariant** with head `h`; `done` lists the chords already scanned from the
region at the head. -/
structure BInv (R K : ℕ) (up dn : ℕ → ℕ) (lst : ℕ → List ℕ) (h : ℕ) (done : List ℕ) (st : BS) :
    Prop where
  tl_pos : 1 ≤ st.tl
  tl_le : st.tl ≤ R
  h_lt : h < st.tl ∨ (h = st.tl ∧ done = [])
  ord_lt : ∀ q, q < st.tl → st.ord q < R ∧ st.vis (st.ord q) = 1
  ord_inj : ∀ q q', q < st.tl → q' < st.tl → st.ord q = st.ord q' → q = q'
  vis_ord : ∀ r, r < R → st.vis r = 1 → ∃ q, q < st.tl ∧ st.ord q = r
  root : st.ord 0 = 0
  disc : ∀ q, 0 < q → q < st.tl → Disc K up dn st q
  closed : ∀ q, q < h → ∀ i ∈ lst (st.ord q), st.vis (up i) = 1 ∧ st.vis (dn i) = 1
  closed_cur : ∀ i ∈ done, st.vis (up i) = 1 ∧ st.vis (dn i) = 1

section bfs

variable {R K : ℕ} {up dn : ℕ → ℕ} {lst : ℕ → List ℕ}
variable (hends : ∀ i, i < K → up i < R ∧ dn i < R ∧ up i ≠ dn i)
variable (hlists : ∀ r, r < R → ∀ i, i ∈ lst r ↔ i < K ∧ (up i = r ∨ dn i = r))
include hends hlists

/-- The invariant at the start, for any state with only the root visited and queued. -/
theorem binv_start (hR : 1 ≤ R) {st : BS} (hv : ∀ r, r < R → st.vis r = if r = 0 then 1 else 0)
    (ho : st.ord 0 = 0) (ht : st.tl = 1) : BInv R K up dn lst 0 [] st where
  tl_pos := by omega
  tl_le := by omega
  h_lt := Or.inl (by omega)
  ord_lt q hq := by
    ram_grind
  ord_inj q q' hq hq' _ := by omega
  vis_ord r hr hvr := by
    ram_grind
  root := ho
  disc q hq hq' := by omega
  closed q hq := absurd hq (Nat.not_lt_zero _)
  closed_cur i hi := by simp at hi

/-- One scan step preserves the invariant (the scanned chord is added to `done`). -/
theorem bstep_inv {h : ℕ} {done : List ℕ} {st : BS} (hI : BInv R K up dn lst h done st)
    (hh : h < st.tl) {i : ℕ} (hi : i ∈ lst (st.ord h)) :
    BInv R K up dn lst h (i :: done) (bstep up dn (st.ord h) st i) := by
  obtain ⟨hrR, hrv⟩ := hI.ord_lt h hh
  set r := st.ord h with hrdef
  obtain ⟨hiK, hir⟩ := (hlists r hrR i).1 hi
  obtain ⟨hu, hd, hne⟩ := hends i hiK
  set s := (if up i = r then dn i else up i) with hsdef
  have hsR : s < R := by grind
  -- the two endpoints are `r` and `s`
  have hpair : (up i = r ∧ dn i = s) ∨ (up i = s ∧ dn i = r) := by
    grind
  unfold bstep
  rw [← hsdef]
  by_cases hvs : st.vis s = 1
  · rw [ite_eq_left hvs]
    refine { hI with h_lt := Or.inl hh, closed_cur := ?_ }
    intro i' hi'
    rcases List.mem_cons.1 hi' with rfl | hi'
    · grind
    · ram_grind
  · rw [ite_eq_right hvs]
    -- `s` is new
    have hsnew : ∀ q, q < st.tl → st.ord q ≠ s := fun q hq e => hvs (e ▸ (hI.ord_lt q hq).2)
    have hsr : s ≠ r := fun e => hvs (e ▸ hrv)
    have hs0 : s ≠ 0 := fun e => hsnew 0 hI.tl_pos (hI.root.trans e.symm)
    have htlR : st.tl < R := by
      -- the queue holds `tl` distinct regions other than `s`
      have himg : ((range st.tl).image st.ord) ⊆ (range R).erase s := by
        intro w hw
        rw [Finset.mem_image] at hw
        obtain ⟨q, hq, rfl⟩ := hw
        rw [Finset.mem_range] at hq
        exact Finset.mem_erase.2 ⟨hsnew q hq, Finset.mem_range.2 (hI.ord_lt q hq).1⟩
      have hc := Finset.card_le_card himg
      rw [Finset.card_image_of_injOn (fun a ha b hb e => hI.ord_inj a b
        (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) e), Finset.card_range,
        Finset.card_erase_of_mem (Finset.mem_range.2 hsR), Finset.card_range] at hc
      
      omega
    -- the chord `i` is no parent chord yet
    have hinew : ∀ q, 0 < q → q < st.tl → st.pch (st.ord q) ≠ i := by
      intro q hq0 hq e
      obtain ⟨-, -, ⟨q', hq', hpq⟩, hends', -, -⟩ := hI.disc q hq0 hq
      grind
    have hord_old : ∀ q, q < st.tl → Function.update st.ord st.tl s q = st.ord q :=
      fun q hq => Function.update_of_ne (by omega) _ _
    constructor
    · grind
    · grind
    · grind
    · intro q hq
      dsimp only at hq ⊢
      by_cases hqt : q = st.tl
      · grind
      · have hq' : q < st.tl := by omega
        rw [hord_old q hq']
        ram_grind
    · intro q q' hq hq' e
      dsimp only at hq hq' e
      by_cases h1 : q = st.tl <;> by_cases h2 : q' = st.tl
      · omega
      · rw [h1, Function.update_self, hord_old q' (by omega)] at e
        exact absurd e.symm (hsnew q' (by omega))
      · rw [h2, Function.update_self, hord_old q (by omega)] at e
        exact absurd e (hsnew q (by omega))
      · rw [hord_old q (by omega), hord_old q' (by omega)] at e
        exact hI.ord_inj q q' (by omega) (by omega) e
    · intro v hv hvv
      dsimp only at hvv ⊢
      by_cases hvs' : v = s
      · exact ⟨st.tl, by omega, by grind⟩
      · rw [Function.update_of_ne hvs'] at hvv
        obtain ⟨q, hq, e⟩ := hI.vis_ord v hv hvv
        grind
    · dsimp only
      rw [hord_old 0 hI.tl_pos]; exact hI.root
    · intro q hq0 hq
      dsimp only at hq
      by_cases hqt : q = st.tl
      · subst hqt
        unfold Disc
        dsimp only
        simp only [Function.update_self]
        grind
      · have hq' : q < st.tl := by omega
        obtain ⟨d1, d2, ⟨q', hq'', d3⟩, d4, d5, d6⟩ := hI.disc q hq0 hq'
        have hne' := hsnew q hq'
        unfold Disc
        dsimp only
        rw [hord_old q hq', Function.update_of_ne hne', Function.update_of_ne hne',
          Function.update_of_ne hne', Function.update_of_ne (hinew q hq0 hq')]
        grind
    · intro q hq i' hi'
      dsimp only at hi' ⊢
      rw [hord_old q (by omega)] at hi'
      obtain ⟨c1, c2⟩ := hI.closed q hq i' hi'
      grind
    · intro i' hi'
      dsimp only
      have hvis : ∀ v, st.vis v = 1 → Function.update st.vis s 1 v = 1 := by
        grind
      rcases List.mem_cons.1 hi' with rfl | hi'
      · grind
      · obtain ⟨c1, c2⟩ := hI.closed_cur i' hi'
        grind

/-- A scan never changes the queue up to the old tail, nor the tail downwards. -/
theorem bstep_mono (r : ℕ) (st : BS) (i : ℕ) :
    st.tl ≤ (bstep up dn r st i).tl ∧
      ∀ q, q < st.tl → (bstep up dn r st i).ord q = st.ord q := by
  unfold bstep
  by_cases hv : st.vis (if up i = r then dn i else up i) = 1
  · ram_all
  · ram_simp

theorem fold_mono (r : ℕ) (l : List ℕ) (st : BS) :
    st.tl ≤ (l.foldl (bstep up dn r) st).tl ∧
      ∀ q, q < st.tl → (l.foldl (bstep up dn r) st).ord q = st.ord q := by
  induction l generalizing st with
  | nil => ram_all
  | cons i l ih =>
    rw [List.foldl_cons]
    obtain ⟨a1, a2⟩ := bstep_mono hends hlists r st i
    grind

section
variable {h : ℕ} {st : BS}
/-- Scanning a prefix of the list of the head region. -/
theorem fold_inv (hh : h < st.tl) :
    ∀ (l done : List ℕ), (∀ i ∈ l, i ∈ lst (st.ord h)) → BInv R K up dn lst h done st →
      BInv R K up dn lst h (l.reverse ++ done) (l.foldl (bstep up dn (st.ord h)) st) := by
  intro l
  induction l generalizing st with
  | nil => ram_all
  | cons i l ih =>
    intro done hl hI
    rw [List.foldl_cons]
    have h1 := bstep_inv hends hlists hI hh (hl i (List.mem_cons_self))
    obtain ⟨m1, m2⟩ := bstep_mono hends hlists (st.ord h) st i
    have hord : (bstep up dn (st.ord h) st i).ord h = st.ord h := m2 h hh
    have := ih (st := bstep up dn (st.ord h) st i) (by omega) (i :: done)
      (fun j hj => by grind) h1
    grind

/-- **Dequeuing one region** preserves the invariant (with the next head). -/
theorem bouter_inv (hI : BInv R K up dn lst h [] st) (hh : h < st.tl) :
    BInv R K up dn lst (h + 1) [] (bouter up dn lst st h) := by
  have hI' := fold_inv hends hlists hh (lst (st.ord h)) [] (fun _ hi => hi) hI
  rw [List.append_nil] at hI'
  obtain ⟨m1, m2⟩ := fold_mono hends hlists (st.ord h) (lst (st.ord h)) st
  unfold bouter
  set st' := (lst (st.ord h)).foldl (bstep up dn (st.ord h)) st with hst'
  have hord : st'.ord h = st.ord h := m2 h hh
  refine { hI' with h_lt := ?_, closed := ?_, closed_cur := fun i hi => by simp at hi }
  · grind
  · intro q hq i hi
    by_cases e : q = h
    · ram_grind
    · exact hI'.closed q (by omega) i hi


end

variable (hcount : R = K + 1)
variable (hconn : ∀ r, r < R → ReflTransGen (fun a b => ∃ i, i < K ∧
    (up i = a ∧ dn i = b ∨ up i = b ∧ dn i = a)) 0 r)
include hcount hconn

section
variable {st : BS} (hI : BInv R K up dn lst st.tl [] st)
include hI
/-- **The end of the search**: with the queue exhausted, every region is queued. -/
theorem bfs_all : st.tl = R := by
  -- every region is visited
  have hvis : ∀ r, r < R → st.vis r = 1 := by
    intro r hr
    have := hconn r hr
    induction this with
    | refl => have := hI.ord_lt 0 hI.tl_pos; rw [hI.root] at this; exact this.2
    | tail hab hbc ih =>
      rename_i b c
      obtain ⟨i, hi, hh⟩ := hbc
      obtain ⟨hu, hd, -⟩ := hends i hi
      have hb : b < R := by omega
      obtain ⟨q, hq, hqb⟩ := hI.vis_ord b hb (ih hb)
      have hmem : i ∈ lst (st.ord q) := by
        grind
      obtain ⟨c1, c2⟩ := hI.closed q hq i hmem
      grind
  -- so the queue holds all regions
  have himg : range R ⊆ (range st.tl).image st.ord := by
    intro r hr
    rw [Finset.mem_range] at hr
    obtain ⟨q, hq, e⟩ := hI.vis_ord r hr (hvis r hr)
    grind
  have hc := Finset.card_le_card himg
  rw [Finset.card_range, Finset.card_image_of_injOn (fun a ha b hb e => hI.ord_inj a b
    (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) e), Finset.card_range] at hc
  have := hI.tl_le
  omega

/-- With the queue exhausted, every region is in the queue. -/
theorem bfs_cover :
    ∀ r, r < R → ∃ q, q < st.tl ∧ st.ord q = r := by
  have hvis : ∀ r, r < R → st.vis r = 1 := by
    intro r hr
    have := hconn r hr
    induction this with
    | refl => have := hI.ord_lt 0 hI.tl_pos; rw [hI.root] at this; exact this.2
    | tail hab hbc ih =>
      rename_i b c
      obtain ⟨i, hi, hh⟩ := hbc
      obtain ⟨hu, hd, -⟩ := hends i hi
      have hb : b < R := by omega
      obtain ⟨q, hq, hqb⟩ := hI.vis_ord b hb (ih hb)
      have hmem : i ∈ lst (st.ord q) := by
        grind
      obtain ⟨c1, c2⟩ := hI.closed q hq i hmem
      grind
  ram_grind


end

open Classical in
/-- The position of a region in the search order. -/
noncomputable def bpos (st : BS) (r : ℕ) : ℕ :=
  if h : ∃ q, q < st.tl ∧ st.ord q = r then Nat.find h else 0

/-- **The search establishes the rooted tree**, the child endpoints and the side bits. -/
theorem bfs_rooted {st : BS} (hI : BInv R K up dn lst st.tl [] st) :
    Rooted R K up dn st.ord (bpos st) st.prg st.pch ∧
      (∀ e, e < K → st.chOf e < R ∧ st.chOf e ≠ 0 ∧ st.pch (st.chOf e) = e) ∧
      (∀ s, s < R → s ≠ 0 → (st.isdn s = 1 ↔ dn (st.pch s) = s)) := by
  classical
  have htl := bfs_all hends hlists hcount hconn hI
  have hcov := bfs_cover hends hlists hcount hconn hI
  -- positions
  have hposs : ∀ r, r < R → bpos st r < st.tl ∧ st.ord (bpos st r) = r := by
    grind [bpos]
  have hpos_ord : ∀ q, q < R → bpos st (st.ord q) = q := by
    intro q hq
    have h1 := hposs (st.ord q) (hI.ord_lt q (by omega)).1
    exact hI.ord_inj _ _ h1.1 (by omega) h1.2
  -- a non-root region and its discovery facts
  have hdisc : ∀ s, s < R → s ≠ 0 → Disc K up dn st (bpos st s) := by
    intro s hs hs0
    obtain ⟨p1, p2⟩ := hposs s hs
    have hp0 : 0 < bpos st s := by
      rcases Nat.eq_zero_or_pos (bpos st s) with e | e
      · rw [e, hI.root] at p2; omega
      · exact e
    exact hI.disc _ hp0 p1
  have hprg : ∀ s, s < R → s ≠ 0 → st.prg s < R ∧ bpos st (st.prg s) < bpos st s := by
    intro s hs hs0
    obtain ⟨-, -, ⟨q', hq', hpq⟩, -, -, -⟩ := hdisc s hs hs0
    rw [(hposs s hs).2] at hpq
    have hq'R : q' < R := by grind
    refine ⟨by rw [hpq]; exact (hI.ord_lt q' (by omega)).1, ?_⟩
    grind
  have hdisc' : ∀ s, s < R → s ≠ 0 → st.pch s < K ∧
      ((up (st.pch s) = st.prg s ∧ dn (st.pch s) = s) ∨ (up (st.pch s) = s ∧ dn (st.pch s) = st.prg s)) ∧
      (st.isdn s = 1 ↔ dn (st.pch s) = s) ∧ st.chOf (st.pch s) = s := by
    intro s hs hs0
    obtain ⟨-, d2, -, d4, d5, d6⟩ := hdisc s hs hs0
    rw [(hposs s hs).2] at d2 d4 d5 d6
    ram_simp
  -- parent chords are injective
  
  -- so they are onto the chords
  have hsurj : ∀ i, i < K → ∃ s, s < R ∧ s ≠ 0 ∧ st.pch s = i := by
    have himg : ((range R).erase 0).image st.pch = range K := by
      apply Finset.eq_of_subset_of_card_le
      · intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨s, hs, rfl⟩ := hi
        grind
      · rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_range.2 (by omega)),
          Finset.card_range, Finset.card_range]
        · omega
        · intro a ha b hb e
          simp only [Finset.coe_erase, Finset.coe_range, Set.mem_sdiff, Set.mem_Iio,
            Set.mem_singleton_iff] at ha hb
          grind
    intro i hi
    have : i ∈ ((range R).erase 0).image st.pch := by grind
    rw [Finset.mem_image] at this
    obtain ⟨s, hs, e⟩ := this
    rw [Finset.mem_erase, Finset.mem_range] at hs
    grind
  refine ⟨⟨hcount, fun q hq => (hI.ord_lt q (by omega)).1, fun r hr => by
      grind, fun r hr => (hposs r hr).2, hpos_ord, hI.root,
      fun s hs h0 => (hprg s hs h0).1, fun s hs h0 => (hprg s hs h0).2,
      fun s hs h0 => (hdisc' s hs h0).1, fun s hs h0 => (hdisc' s hs h0).2.1, hsurj,
      fun i hi => ⟨(hends i hi).1, (hends i hi).2.1⟩⟩, ?_, fun s hs h0 => (hdisc' s hs h0).2.2.1⟩
  intro e he
  obtain ⟨s, hs, h0, rfl⟩ := hsurj e he
  grind

end bfs

end

end Chazelle.Core.Dec
