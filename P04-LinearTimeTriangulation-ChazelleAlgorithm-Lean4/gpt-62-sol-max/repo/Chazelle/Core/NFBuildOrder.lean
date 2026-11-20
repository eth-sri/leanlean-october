module

public import Chazelle.Core.FactsTie
public import Chazelle.Core.NFBuildSort
public import Chazelle.Core.SpecKernels

/-!
# WP-C (BuildNF): the attachment events of a chord list

For a chord list `L` (the input of `BuildNFSpec`, triples `(h, lp, rp)`), chord `i` has two
attachment events: `(i, key lpos, key rpos)` and `(i, key rpos, key lpos)` (`events`).

## Results

* `parenthesis_of_sorted`: **every** ordering of the events of a valid chord list
  (`ChordTriplesOK`) that is sorted by `BuildSort.EvLe` (key, then the tie rule) has a parenthesis
  chord word (`BuildStack.NoCross`, `BuildStack.Twice`), so the stack pass of `NFBuildStack`
  computes the nesting (for every good model; the geometric input is `WalkAx.no_cross`).
* `tie_rule_down`, `tie_rule_up`: at a tie (two chords attached at one position), the tie rule of
  `EvLe` is the direction rule: at a walk vertex whose leaving edge goes down, the event of the
  west chord (the one whose right endpoint is the vertex: its `rpos` event) has the larger cyclic
  distance to its other end, so it comes first; at a vertex whose leaving edge goes up, the east
  chord's (`lpos`) event comes first.  One height comparison of the leaving edge decides the tie.
-/

namespace Chazelle.Core

namespace BuildOrder

@[expose] public section

open Set List
open Chazelle.Chain (SideAttach sideInArc sidePt sideKey_inj)
open BuildSort (Ev EvLe cycDist)

/-- The chord of index `i` of a triple list. -/
noncomputable def chordSet (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) :
    Set Point :=
  (recOf (L.getD i (0, 0, 0))).toSet M Q

/-- The two attachment events of chord `i`. -/
noncomputable def evPair (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : List Ev :=
  [(i, M.key Q (recOf (L.getD i (0, 0, 0))).lpos, M.key Q (recOf (L.getD i (0, 0, 0))).rpos),
   (i, M.key Q (recOf (L.getD i (0, 0, 0))).rpos, M.key Q (recOf (L.getD i (0, 0, 0))).lpos)]

/-- **The attachment events of a chord list.** -/
noncomputable def events (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) : List Ev :=
  (List.range L.length).flatMap (evPair M Q L)

theorem events_map_fst (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) :
    (events M Q L).map Prod.fst = (List.range L.length).flatMap (fun i => [i, i]) := by
  unfold events evPair
  rw [List.map_flatMap]
  rfl

theorem count_doubles (n i : ℕ) :
    ((List.range n).flatMap (fun j => [j, j])).count i = if i < n then 2 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.count_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_cons,
      List.count_nil, beq_iff_eq]
    by_cases h : i = n
    · subst h; simp
    · have h' := Ne.symm h
      simp only [h', ite_false, add_zero]
      by_cases h2 : i < n
      · ram_simp [ite_eq_left h2, ite_eq_left]
      ram_simp [ite_eq_right h2, ite_eq_right]

theorem count_events (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) {i : ℕ}
    (hi : i < L.length) : ((events M Q L).map Prod.fst).count i = 2 := by
  rw [events_map_fst, count_doubles, ite_eq_left hi]

theorem mem_events {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {e : Ev} :
    e ∈ events M Q L ↔ ∃ i < L.length, e ∈ evPair M Q L i := by
  unfold events
  simp [List.mem_flatMap]

/-- A triple of the list, by index. -/
theorem getD_mem {L : List (ℕ × ℕ × ℕ)} {i : ℕ} (hi : i < L.length) : L.getD i (0, 0, 0) ∈ L := by
  simp_all

/-- Distinct indices of a valid chord list give distinct chords. -/
theorem chordSet_inj {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} (hL : ChordTriplesOK M Q L)
    {i j : ℕ} (hi : i < L.length) (hj : j < L.length) (h : chordSet M Q L i = chordSet M Q L j) :
    i = j := by
  have hnd := hL.2.1
  have hi' := hi
  rw [← List.length_map] at hi'
  have hj' := hj
  rw [← List.length_map] at hj'
  refine (hnd.getElem_inj_iff (hi := hi') (hj := hj')).1 ?_
  rw [List.getElem_map, List.getElem_map]
  unfold chordSet at h
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at h

/-- The chords of a valid chord list are in its family. -/
theorem chordSet_mem {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {i : ℕ}
    (hi : i < L.length) :
    chordSet M Q L i ∈ {c | ∃ x ∈ L, c = (recOf x).toSet M Q} :=
  ⟨_, getD_mem hi, rfl⟩

/-- **The attachment data of an event**: its chord is attached at the positions of its two keys,
at distinct points. -/
theorem event_data {M : Model} (hM : WalkAx M) {Q : Polygon} {L : List (ℕ × ℕ × ℕ)}
    (hL : ChordTriplesOK M Q L) {e : Ev} (he : e ∈ events M Q L) :
    ∃ i < L.length, e.1 = i ∧ ∃ (pa pb : ℕ) (ta tb : ℝ),
      SideAttach M.W (chordSet M Q L i) pa ta ∧ SideAttach M.W (chordSet M Q L i) pb tb ∧
      sidePt M.W pa ta ≠ sidePt M.W pb tb ∧ e.2.1 = pa + ta ∧ e.2.2 = pb + tb := by
  obtain ⟨i, hi, he⟩ := mem_events.1 he
  set r := recOf (L.getD i (0, 0, 0)) with hr
  have hatt : r.Attached M Q := hL.2.2.1 _ (getD_mem hi)
  have hadm : r.toSet M Q ∈ M.Adm := hL.1.2.1 (chordSet_mem hi)
  have hlt := hM.endpoints_lt hadm hatt
  have hne : sidePt M.W r.lp (M.param Q r.lpos) ≠ sidePt M.W r.rp (M.param Q r.rpos) := by
    intro h
    have : M.pos Q r.lpos = M.pos Q r.rpos := h
    rw [this] at hlt
    exact lt_irrefl _ hlt
  unfold evPair at he
  rw [← hr] at he
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨i, hi, rfl, r.lp, r.rp, _, _, hatt.1, hatt.2, hne, rfl, rfl⟩
  · rw [List.mem_singleton] at he
    subst he
    exact ⟨i, hi, rfl, r.rp, r.lp, _, _, hatt.2, hatt.1, Ne.symm hne, rfl, rfl⟩

/-- The key of an attached chord lies in the walk's key interval. -/
theorem attachKey_bounds {M : Model} {p : ℕ} {t : ℝ} {c : Set Point}
    (h : SideAttach M.W c p t) : 0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < M.W.n := by
  have : (p : ℝ) + 1 ≤ M.W.n := by exact_mod_cast h.1
  exact ⟨by have := h.2.1; positivity, by linarith [h.2.2.1]⟩

/-- **The sorted attachment events of a valid chord list form a parenthesis word**, for every
ordering sorted by `EvLe` (so for the output of the RAM sort with the corresponding
comparator). -/
theorem parenthesis_of_sorted {M : Model} (hM : WalkAx M) {Q : Polygon}
    {L : List (ℕ × ℕ × ℕ)} (hL : ChordTriplesOK M Q L) {S : List Ev}
    (hperm : S.Perm (events M Q L)) (hsorted : S.Pairwise (EvLe M.W.n)) :
    BuildStack.NoCross (S.map Prod.fst) ∧ BuildStack.Twice (S.map Prod.fst) := by
  have hmem : ∀ e, e ∈ S ↔ e ∈ events M Q L := fun e => hperm.mem_iff
  have hfin := hL.1.1
  have hAdm := hL.1.2.1
  refine BuildSort.noCross_of_sorted (n := (M.W.n : ℝ)) ?_ ?_ ?_ ?_ ?_ hsorted
  · intro e he
    obtain ⟨i, hi, -, pa, pb, ta, tb, hA, hB, hAB, h1, h2⟩ := event_data hM hL ((hmem e).1 he)
    rw [h1, h2]
    exact ⟨(attachKey_bounds hA).1, (attachKey_bounds hA).2, (attachKey_bounds hB).1, (attachKey_bounds hB).2,
      WalkAx.key_ne_of_pt_ne hA hB hAB⟩
  · intro e he
    rw [hmem] at he ⊢
    obtain ⟨i, hi, he⟩ := mem_events.1 he
    refine mem_events.2 ⟨i, hi, ?_⟩
    unfold evPair at he ⊢
    rcases List.mem_cons.1 he with rfl | he
    · simp
    · rw [List.mem_singleton] at he; subst he; simp
  · intro e he
    obtain ⟨i, hi, hei, -⟩ := event_data hM hL ((hmem e).1 he)
    rw [(hperm.map Prod.fst).count_eq, hei]
    exact count_events M Q L hi
  · intro e he f hf hef
    obtain ⟨i, hi, hei, pa, pb, ta, tb, hA, hB, hAB, h1, h2⟩ := event_data hM hL ((hmem e).1 he)
    obtain ⟨j, hj, hfj, pc, pd, tc, td, hC, hD, -, h3, h4⟩ := event_data hM hL ((hmem f).1 hf)
    rw [h1, h2, h3, h4]
    have hne := fun h =>
      hef (by rw [hei, hfj]; exact chordSet_inj hL hi hj h)
    exact hM.no_cross hAdm hfin (chordSet_mem hi) (chordSet_mem hj) hne hA hB hAB hC hD
  · intro e he f hf hef
    obtain ⟨i, hi, hei, pa, pb, ta, tb, hA, hB, hAB, h1, h2⟩ := event_data hM hL ((hmem e).1 he)
    obtain ⟨j, hj, hfj, pc, pd, tc, td, hC, hD, hCD, h3, h4⟩ := event_data hM hL ((hmem f).1 hf)
    have k1 : (pa : ℝ) + ta = pc + tc := by rw [← h1, ← h3, hef]
    have k2 : (pb : ℝ) + tb = pd + td := by rw [← h2, ← h4, hef]
    obtain ⟨rfl, rfl⟩ := sideKey_inj hA.2.1 hA.2.2.1 hC.2.1 hC.2.2.1 k1
    obtain ⟨rfl, rfl⟩ := sideKey_inj hB.2.1 hB.2.2.1 hD.2.1 hD.2.2.1 k2
    have e1 := (hM.attach_seg (hAdm (chordSet_mem hi)) hA hB hAB).1
    have e2 := (hM.attach_seg (hAdm (chordSet_mem hj)) hC hD hCD).1
    rw [hei, hfj]
    exact chordSet_inj hL hi hj (e1.trans e2.symm)

/-! ## The tie rule is the direction rule -/

/-- Convert a tie's cyclic betweenness to an order on the two distances. -/
private theorem tie_distance {M : Model} {x y : Set Point} {p q r : ℕ} {u v : ℝ}
    (hx : SideAttach M.W x p 0) (hy : SideAttach M.W y p 0)
    (hq : SideAttach M.W x q u) (hr : SideAttach M.W y r v)
    (hnq : sidePt M.W q u ≠ sidePt M.W p 0) (hnr : sidePt M.W r v ≠ sidePt M.W p 0)
    (h : sideInArc p ((r : ℝ) + v) ((q : ℝ) + u)) :
    cycDist M.W.n p (q + u) < cycDist M.W.n p (r + v) := by
  refine (BuildSort.sideInArc_iff_cycDist (by simpa using attachKey_bounds hx)
    (attachKey_bounds hq) (attachKey_bounds hr) ?_ ?_).1 h
  · simpa using WalkAx.key_ne_of_pt_ne hx hq hnq.symm
  · simpa using WalkAx.key_ne_of_pt_ne hy hr hnr.symm

section

variable {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm)
    (hfin : F.Finite) {ce cw : Set Point} (hce : ce ∈ F) (hcw : cw ∈ F) {p : ℕ} {t : ℝ}
    (hAe : SideAttach M.W ce p t) (hAw : SideAttach M.W cw p t)
    (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1)
include hM hF hfin hce hcw hAe hAw hE hW

/-- **Tie at a vertex whose leaving edge goes down**: the east chord's other end is cyclically
closer to the vertex key than the west chord's, so under `EvLe` the west chord's event (the
larger cyclic distance) comes first. -/
theorem tie_rule_down
    (hdown : (M.wb p).2 < (M.wa p).2) {pe pw : ℕ} {te tw : ℝ}
    (hBe : SideAttach M.W ce pe te) (hBe' : sidePt M.W pe te ≠ sidePt M.W p t)
    (hBw : SideAttach M.W cw pw tw) (hBw' : sidePt M.W pw tw ≠ sidePt M.W p t) :
    t = 0 ∧ cycDist M.W.n p (pe + te) < cycDist M.W.n p (pw + tw) := by
  obtain ⟨rfl, U, V, R, -, -, -, -, -, -, -, -, -, hord⟩ :=
    hM.tie_down hF hfin hce hcw hAe hAw hE hW hdown
  have h := hord pe pw te tw (by exact hBe) (by simpa [Chazelle.Chain.sidePt_zero] using hBe')
    hBw (by simpa [Chazelle.Chain.sidePt_zero] using hBw')
  exact ⟨rfl, tie_distance hAe hAw hBe hBw hBe' hBw' h⟩

/-- **Tie at a vertex whose leaving edge goes up**: the west chord's other end is cyclically
closer, so under `EvLe` the east chord's event comes first. -/
theorem tie_rule_up
    (hup : (M.wa p).2 < (M.wb p).2) {pe pw : ℕ} {te tw : ℝ}
    (hBe : SideAttach M.W ce pe te) (hBe' : sidePt M.W pe te ≠ sidePt M.W p t)
    (hBw : SideAttach M.W cw pw tw) (hBw' : sidePt M.W pw tw ≠ sidePt M.W p t) :
    t = 0 ∧ cycDist M.W.n p (pw + tw) < cycDist M.W.n p (pe + te) := by
  obtain ⟨rfl, U, V, R, -, -, -, -, -, -, -, -, -, hord⟩ :=
    hM.tie_up hF hfin hce hcw hAe hAw hE hW hup
  have h := hord pe pw te tw (by exact hBe) (by simpa [Chazelle.Chain.sidePt_zero] using hBe')
    hBw (by simpa [Chazelle.Chain.sidePt_zero] using hBw')
  exact ⟨rfl, tie_distance hAw hAe hBw hBe hBw' hBe' h⟩

end

end

end BuildOrder

end Chazelle.Core
