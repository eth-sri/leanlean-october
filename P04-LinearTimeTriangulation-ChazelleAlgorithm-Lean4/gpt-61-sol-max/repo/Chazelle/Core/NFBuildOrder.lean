module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.FactsTie
public import Chazelle.Core.NFBuildSort
public import Chazelle.Core.SpecKernels

/-!
# WP-C (BuildNF): the attachment events of a chord list

For a chord list `L` (the input of `BuildNFSpec`, triples `(h, lp, rp)`), chord `i` has two
attachment events: `(i, key lpos, key rpos)` and `(i, key rpos, key lpos)` (`events`).

## Results

* `endpoints`: the two attachments of an admissible, attached record are at distinct points, the
  left endpoint (lower `x`) at `lpos` and the right one at `rpos`.
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

section
variable (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ))
include M Q L
/-- The chord of index `i` of a triple list. -/
noncomputable def chordSet (i : ℕ) :
    Set Point :=
  (recOf (L.getD i (0, 0, 0))).toSet M Q

/-- The two attachment events of chord `i`. -/
noncomputable def evPair (i : ℕ) : List Ev :=
  [(i, M.key Q (recOf (L.getD i (0, 0, 0))).lpos, M.key Q (recOf (L.getD i (0, 0, 0))).rpos),
   (i, M.key Q (recOf (L.getD i (0, 0, 0))).rpos, M.key Q (recOf (L.getD i (0, 0, 0))).lpos)]

/-- **The attachment events of a chord list.** -/
noncomputable def events : List Ev :=
  (List.range L.length).flatMap (evPair M Q L)

theorem events_map_fst :
    (events M Q L).map Prod.fst = (List.range L.length).flatMap (fun i => [i, i]) := by
  unfold events evPair
  grind [List.map_flatMap]


end

theorem count_doubles (n i : ℕ) :
    ((List.range n).flatMap (fun j => [j, j])).count i = if i < n then 2 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.count_append, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_cons,
      List.count_nil, beq_iff_eq]
    grind

theorem count_events (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) {i : ℕ}
    (hi : i < L.length) : ((events M Q L).map Prod.fst).count i = 2 := by
  grind [events_map_fst, count_doubles]

theorem mem_events {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {e : Ev} :
    e ∈ events M Q L ↔ ∃ i < L.length, e ∈ evPair M Q L i := by
  unfold events
  simp_all

/-- **The two attachments of a record** of an admissible attached chord are at distinct points:
the left endpoint at `lpos`, the right one at `rpos`. -/
theorem endpoints {M : Model} (hM : WalkAx M) {Q : Polygon} {r : CRec}
    (hadm : r.toSet M Q ∈ M.Adm) (hr : r.Attached M Q) :
    (M.pos Q r.lpos).1 < (M.pos Q r.rpos).1 := by
  obtain ⟨hA, hB⟩ := hr
  have h1 := hA.2.2.2.1
  obtain ⟨a, b, hab, hcab, hy, -⟩ := hM.ends _ hadm
  have hpA : sidePt M.W r.lp (M.param Q r.lpos) = M.pos Q r.lpos := rfl
  rw [hpA] at h1
  obtain ⟨-, h1a, h1b⟩ := h1
  by_contra hle
  push Not at hle
  have hsub : ∀ z ∈ r.toSet M Q, z.1 = (M.pos Q r.lpos).1 := by
    rintro z ⟨-, hz1, hz2⟩
    linarith
  have ha : a ∈ r.toSet M Q := by rw [hcab]; exact Geometry.left_mem_segment _ _
  have hb : b ∈ r.toSet M Q := by rw [hcab]; exact Geometry.right_mem_segment _ _
  grind

/-- A triple of the list, by index. -/
theorem getD_mem {L : List (ℕ × ℕ × ℕ)} {i : ℕ} (hi : i < L.length) : L.getD i (0, 0, 0) ∈ L := by
  simp_all

section
variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)}
/-- Distinct indices of a valid chord list give distinct chords. -/
theorem chordSet_inj (hL : ChordTriplesOK M Q L)
    {i j : ℕ} (hi : i < L.length) (hj : j < L.length) (h : chordSet M Q L i = chordSet M Q L j) :
    i = j := by
  have hnd := hL.2.1
  have hi' : i < (L.map fun x => (recOf x).toSet M Q).length := by simp_all
  have hj' : j < (L.map fun x => (recOf x).toSet M Q).length := by simp_all
  refine (hnd.getElem_inj_iff (hi := hi') (hj := hj')).1 ?_
  simp_all [List.getElem_map, chordSet, List.getD_eq_getElem?_getD, Option.getD_some] 

/-- The chords of a valid chord list are in its family. -/
theorem chordSet_mem {i : ℕ}
    (hi : i < L.length) :
    chordSet M Q L i ∈ {c | ∃ x ∈ L, c = (recOf x).toSet M Q} :=
  ⟨_, getD_mem hi, rfl⟩


end

section
variable {M : Model} (hM : WalkAx M) {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} (hL : ChordTriplesOK M Q L)
include hM hL
/-- **The attachment data of an event**: its chord is attached at the positions of its two keys,
at distinct points. -/
theorem event_data {e : Ev} (he : e ∈ events M Q L) :
    ∃ i < L.length, e.1 = i ∧ ∃ (pa pb : ℕ) (ta tb : ℝ),
      SideAttach M.W (chordSet M Q L i) pa ta ∧ SideAttach M.W (chordSet M Q L i) pb tb ∧
      sidePt M.W pa ta ≠ sidePt M.W pb tb ∧ e.2.1 = pa + ta ∧ e.2.2 = pb + tb := by
  obtain ⟨i, hi, he⟩ := mem_events.1 he
  set r := recOf (L.getD i (0, 0, 0)) with hr
  have hatt : r.Attached M Q := hL.2.2.1 _ (getD_mem hi)
  have hadm : r.toSet M Q ∈ M.Adm := hL.1.2.1 (chordSet_mem hi)
  have hlt := endpoints hM hadm hatt
  have hne : sidePt M.W r.lp (M.param Q r.lpos) ≠ sidePt M.W r.rp (M.param Q r.rpos) := by
    intro h
    have : M.pos Q r.lpos = M.pos Q r.rpos := h
    simp_all
  unfold evPair at he
  rw [← hr] at he
  rcases List.mem_cons.1 he with rfl | he
  · exact ⟨i, hi, rfl, r.lp, r.rp, _, _, hatt.1, hatt.2, hne, rfl, rfl⟩
  · rw [List.mem_singleton] at he
    subst he
    exact ⟨i, hi, rfl, r.rp, r.lp, _, _, hatt.2, hatt.1, Ne.symm hne, rfl, rfl⟩

/-- **The sorted attachment events of a valid chord list form a parenthesis word**, for every
ordering sorted by `EvLe` (so for the output of the RAM sort with the corresponding
comparator). -/
theorem parenthesis_of_sorted {S : List Ev}
    (hperm : S.Perm (events M Q L)) (hsorted : S.Pairwise (EvLe M.W.n)) :
    BuildStack.NoCross (S.map Prod.fst) ∧ BuildStack.Twice (S.map Prod.fst) := by
  have hmem : ∀ e, e ∈ S ↔ e ∈ events M Q L := fun e => hperm.mem_iff
  have hfin := hL.1.1
  have hAdm := hL.1.2.1
  have keyb : ∀ {pa : ℕ} {ta : ℝ} {c : Set Point}, SideAttach M.W c pa ta →
      0 ≤ (pa : ℝ) + ta ∧ (pa : ℝ) + ta < M.W.n := by
    intro pa ta c h
    have : (pa : ℝ) + 1 ≤ M.W.n := by exact_mod_cast h.1
    exact ⟨by have := h.2.1; positivity, by linarith [h.2.2.1]⟩
  refine BuildSort.noCross_of_sorted (n := (M.W.n : ℝ)) ?_ ?_ ?_ ?_ ?_ hsorted
  · intro e he
    obtain ⟨i, hi, -, pa, pb, ta, tb, hA, hB, hAB, h1, h2⟩ := event_data hM hL ((hmem e).1 he)
    rw [h1, h2]
    exact ⟨(keyb hA).1, (keyb hA).2, (keyb hB).1, (keyb hB).2,
      WalkAx.key_ne_of_pt_ne hA hB hAB⟩
  · intro e he
    rw [hmem] at he ⊢
    obtain ⟨i, hi, he⟩ := mem_events.1 he
    refine mem_events.2 ⟨i, hi, ?_⟩
    grind [evPair, List.mem_singleton]
  · intro e he
    obtain ⟨i, hi, hei, -⟩ := event_data hM hL ((hmem e).1 he)
    rw [(hperm.map Prod.fst).count_eq, hei]
    exact count_events M Q L hi
  · intro e he f hf hef
    obtain ⟨i, hi, hei, pa, pb, ta, tb, hA, hB, hAB, h1, h2⟩ := event_data hM hL ((hmem e).1 he)
    obtain ⟨j, hj, hfj, pc, pd, tc, td, hC, hD, -, h3, h4⟩ := event_data hM hL ((hmem f).1 hf)
    rw [h1, h2, h3, h4]
    have hne : chordSet M Q L i ≠ chordSet M Q L j := fun h =>
      hef (by rw [hei, hfj]; exact chordSet_inj hL hi hj h)
    exact hM.no_cross hAdm hfin (chordSet_mem hi) (chordSet_mem hj) hne hA hB hAB hC hD
  · intro e he f hf hef
    obtain ⟨i, hi, hei, pa, pb, ta, tb, hA, hB, hAB, h1, h2⟩ := event_data hM hL ((hmem e).1 he)
    obtain ⟨j, hj, hfj, pc, pd, tc, td, hC, hD, hCD, h3, h4⟩ := event_data hM hL ((hmem f).1 hf)
    have k1 : (pa : ℝ) + ta = pc + tc := by grind
    have k2 : (pb : ℝ) + tb = pd + td := by grind
    obtain ⟨rfl, rfl⟩ := sideKey_inj hA.2.1 hA.2.2.1 hC.2.1 hC.2.2.1 k1
    obtain ⟨rfl, rfl⟩ := sideKey_inj hB.2.1 hB.2.2.1 hD.2.1 hD.2.2.1 k2
    have e1 := (hM.attach_seg (hAdm (chordSet_mem hi)) hA hB hAB).1
    have e2 := (hM.attach_seg (hAdm (chordSet_mem hj)) hC hD hCD).1
    rw [hei, hfj]
    exact chordSet_inj hL hi hj (e1.trans e2.symm)

/-! ## The tie rule is the direction rule -/


end

section
variable {M : Model} (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite) {ce cw : Set Point} (hce : ce ∈ F) (hcw : cw ∈ F) {p : ℕ} {t : ℝ} (hAe : SideAttach M.W ce p t) (hAw : SideAttach M.W cw p t) (hE : ∀ z ∈ ce, (sidePt M.W p t).1 ≤ z.1) (hW : ∀ z ∈ cw, z.1 ≤ (sidePt M.W p t).1)
include hM F hF hfin hce hcw hAe hAw hE hW
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
  have hv0 : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero M.W p
  rw [hv0] at hBe' hBw'
  have hin := hord pe pw te tw hBe hBe' hBw hBw'
  have keyb : ∀ {pa : ℕ} {ta : ℝ} {c : Set Point}, SideAttach M.W c pa ta →
      0 ≤ (pa : ℝ) + ta ∧ (pa : ℝ) + ta < M.W.n := by
    intro pa ta c h
    have : (pa : ℝ) + 1 ≤ M.W.n := by exact_mod_cast h.1
    exact ⟨by have := h.2.1; positivity, by linarith [h.2.2.1]⟩
  have hk := keyb hAe
  rw [add_zero] at hk
  refine ⟨rfl, (BuildSort.sideInArc_iff_cycDist hk (keyb hBe) (keyb hBw) ?_ ?_).1 hin⟩
  · have := WalkAx.key_ne_of_pt_ne hAe hBe (by grind)
    grind
  · have := WalkAx.key_ne_of_pt_ne hAw hBw (by grind)
    grind

/-- **Tie at a vertex whose leaving edge goes up**: the west chord's other end is cyclically
closer, so under `EvLe` the east chord's event comes first. -/
theorem tie_rule_up
    (hup : (M.wa p).2 < (M.wb p).2) {pe pw : ℕ} {te tw : ℝ}
    (hBe : SideAttach M.W ce pe te) (hBe' : sidePt M.W pe te ≠ sidePt M.W p t)
    (hBw : SideAttach M.W cw pw tw) (hBw' : sidePt M.W pw tw ≠ sidePt M.W p t) :
    t = 0 ∧ cycDist M.W.n p (pw + tw) < cycDist M.W.n p (pe + te) := by
  obtain ⟨rfl, U, V, R, -, -, -, -, -, -, -, -, -, hord⟩ :=
    hM.tie_up hF hfin hce hcw hAe hAw hE hW hup
  have hv0 : sidePt M.W p 0 = M.W.vtx p := Chazelle.Chain.sidePt_zero M.W p
  rw [hv0] at hBe' hBw'
  have hin := hord pe pw te tw hBe hBe' hBw hBw'
  have keyb : ∀ {pa : ℕ} {ta : ℝ} {c : Set Point}, SideAttach M.W c pa ta →
      0 ≤ (pa : ℝ) + ta ∧ (pa : ℝ) + ta < M.W.n := by
    intro pa ta c h
    have : (pa : ℝ) + 1 ≤ M.W.n := by exact_mod_cast h.1
    exact ⟨by have := h.2.1; positivity, by linarith [h.2.2.1]⟩
  have hk := keyb hAe
  rw [add_zero] at hk
  refine ⟨rfl, (BuildSort.sideInArc_iff_cycDist hk (keyb hBw) (keyb hBe) ?_ ?_).1 hin⟩
  · have := WalkAx.key_ne_of_pt_ne hAw hBw (by grind)
    grind
  · have := WalkAx.key_ne_of_pt_ne hAe hBe (by grind)
    grind


end

end

end BuildOrder

end Chazelle.Core
