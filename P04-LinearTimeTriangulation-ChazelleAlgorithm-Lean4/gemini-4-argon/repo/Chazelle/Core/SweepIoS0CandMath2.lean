module

public import Chazelle.Core.SweepIoS0CandMath

/-!
# The sweep RAM (WP-D), answers: stop and table candidates of a side-0 query (mathematics, 2)

* `cut_key`: an attachment of a chord of `F₂⁺` on the `C₁` part is a key of the event log
  (`LogOK`: no cut strictly between two keys or after the last one);
* `stopRecs_unique`, `logRecs_unique`: the record lists in memory are determined by the memory;
* `stop_cand`, `tab_cand`: the stop records and the regular table entries give candidate
  origins (`CandAt`) at their positions, attached at cuts;
* `valid_iff`: the regular origins (on `C₂`, neither the shared vertex nor the top) by their
  normalised walk positions.
-/

namespace Chazelle.Core

namespace SweepIo

namespace S0C

open Set
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt SideAttach)
open Chazelle.Merge (FreeAt)
open Sweep WalkEmbed

@[expose] public section

/-! ## Cuts are log keys -/

theorem gW_lt (J : Merge.Junction) : (gW J : ℝ) < (chainModel J.whole).W.n := by
  rw [cm_n]
  have := tpos_lt J.whole J.m₁
  unfold gW
  exact_mod_cast (by omega : 6 + tpos J.whole J.m₁ < 2 * J.whole.m + 7)

/-- **An attachment of a chord of `F₂⁺` on the `C₁` part is a key of the event log.** -/
theorem cut_key (J : Merge.Junction) {S₂ : Set (Set Point)} {es : List (ℕ × ℝ × Set (Set Point))}
    (hL : LogOK J S₂ es) {e : Set Point} (he : e ∈ F₂plus J S₂) {p : ℕ} {t : ℝ}
    (hA : SideAttach (chainModel J.whole).W e p t) (hst : (Lst J : ℝ) ≤ oW J (p + t)) :
    ∃ i, i < es.length ∧ (es.getD i (0, 0, ∅)).1 = p ∧ (es.getD i (0, 0, ∅)).2.1 = t := by
  obtain ⟨hne, hmem, hhead, hsort, hgap, hlast, -⟩ := hL
  set n := (chainModel J.whole).W.n
  set x : ℝ := p + t
  have hpn := hA.1
  have ht0 := hA.2.1
  have ht1 := hA.2.2.1
  have hx0 : 0 ≤ x := by positivity
  have hxn : x < n := by
    have : (p : ℝ) + 1 ≤ n := by exact_mod_cast hpn
    linarith
  have hcut : (chainModel J.whole).IsCut (F₂plus J S₂) x := ⟨e, he, p, t, hA, rfl⟩
  have hlen : 0 < es.length := List.length_pos_iff.2 hne
  -- keys of the log
  let K : ℕ → ℝ := fun i => (es.getD i (0, 0, ∅)).1 + (es.getD i (0, 0, ∅)).2.1
  have hget : ∀ i (hi : i < es.length), es.getD i (0, 0, ∅) = es[i] := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]
  have hmemi : ∀ i, i < es.length → es.getD i (0, 0, ∅) ∈ es := fun i hi => by
    rw [hget i hi]; exact List.getElem_mem _
  have hK0 : oW J (K 0) ≤ oW J x := by
    have h := hhead (es.getD 0 (0, 0, ∅)) (by
      rw [hget 0 hlen, List.head?_eq_getElem?, List.getElem?_eq_getElem hlen]; rfl)
    show oW J (K 0) ≤ _
    rwa [show K 0 = _ from rfl, h]
  -- the last key not after `x`
  set i := Nat.findGreatest (fun i => oW J (K i) ≤ oW J x) (es.length - 1) with hi
  have hiP : oW J (K i) ≤ oW J x := Nat.findGreatest_spec (P := fun i => oW J (K i) ≤ oW J x)
    (Nat.zero_le _) hK0
  have hil : i < es.length := by
    have : i ≤ es.length - 1 := Nat.findGreatest_le _
    omega
  have hKi := hmem _ (hmemi i hil)
  have hKi0 : 0 ≤ K i := by have := hKi.2.1; have : (0 : ℝ) ≤ (es.getD i (0, 0, ∅)).1 := by positivity
                            simp only [K]; linarith
  have hKin : K i < n := by
    have h1 := hKi.1; have h2 := hKi.2.2.1
    have : ((es.getD i (0, 0, ∅)).1 : ℝ) + 1 ≤ n := by exact_mod_cast h1
    simp only [K]; linarith
  have hgW0 : (0 : ℝ) ≤ gW J := by positivity
  have heq : oW J (K i) = oW J x := by
    rcases hiP.lt_or_eq with hlt | h
    · exfalso
      by_cases hnext : i + 1 < es.length
      · have hnot : ¬ oW J (K (i + 1)) ≤ oW J x :=
          Nat.findGreatest_is_greatest (P := fun i => oW J (K i) ≤ oW J x)
            (n := es.length - 1) (k := i + 1) (by omega) (by omega)
        exact hgap i hnext x hcut hx0 hxn ⟨hlt, not_le.1 hnot⟩
      · have hlast' : es.getLast? = some (es.getD i (0, 0, ∅)) := by
          rw [List.getLast?_eq_getElem?, hget i hil, show es.length - 1 = i by omega, List.getElem?_eq_getElem hil]
        have := hlast _ (by rw [hlast']; rfl) x hcut hx0 hxn
        exact this ⟨hlt, off_lt hxn hgW0⟩
    · exact h
  have hkx : K i = x := off_inj hgW0 (gW_lt J) hKi0 hKin hx0 hxn heq
  obtain ⟨h1, h2⟩ := key_split hKi.2.1 hKi.2.2.1 ht0 ht1 hkx
  exact ⟨i, hil, h1, h2⟩

/-! ## Records in memory -/

theorem stopRecs_unique {m : ℕ → ℕ} {A : ℕ} {rs rs' : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (h : StopRecsAt m A rs) (h' : StopRecsAt m A rs') (hl : rs.length = rs'.length) : rs = rs' := by
  apply List.ext_getElem hl
  intro i hi hi'
  obtain ⟨a1, a2, a3, a4, a5⟩ := h i hi
  obtain ⟨b1, b2, b3, b4, b5⟩ := h' i hi'
  rw [List.getD_eq_getElem _ _ hi] at a1 a2 a3 a4 a5
  rw [List.getD_eq_getElem _ _ hi'] at b1 b2 b3 b4 b5
  ext <;> simp only [← a1, ← a2, ← a3, ← a4, ← a5, b1, b2, b3, b4, b5]

/-- The key of a log record in the event log. -/
theorem logOf_getD (J : Merge.Junction) (Q : Polygon) (N : NF)
    {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)} {i : ℕ} (hi : i < ls.length) :
    ((logOf J Q N ls).getD i (0, 0, ∅)).1 = (ls.getD i (0, 0, 0, 0, 0, 0, 0)).1 ∧
      ((logOf J Q N ls).getD i (0, 0, ∅)).2.1 = (chainModel J.whole).param Q
        ⟨(ls.getD i (0, 0, 0, 0, 0, 0, 0)).1, (ls.getD i (0, 0, 0, 0, 0, 0, 0)).2.1⟩ := by
  unfold logOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem _ _ hi]
  simp

/-! ## The candidates of the stops and the table -/

/-- **A stop record gives a candidate origin** at its position, attached at a log key. -/
theorem stop_cand (J : Merge.Junction) {Q : Polygon} {N : NF}
    (hN : IsNF (chainModel J.right) Q N) {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hS : StopsOK J (N.F (chainModel J.right) Q) (stopsOf J Q N rs))
    {r : ℕ × ℕ × ℕ × ℕ × ℕ} (hr : r ∈ rs) (hkind : r.2.2.1 ≤ 2)
    (hk : r.2.2.1 = 1 → r.2.2.2.1 < N.nChords) :
    CandAt J (stopOrig J Q N r.2.2.1 r.2.2.2.1 r.2.2.2.2) (dirOf r.2.2.2.2)
        (sidePt (chainModel J.whole).W r.1 ((chainModel J.whole).param Q ⟨r.1, r.2.1⟩)) ∧
      stopSet J Q N r.2.2.1 r.2.2.2.1 r.2.2.2.2 ∈ F₂plus J (N.F (chainModel J.right) Q) ∧
      SideAttach (chainModel J.whole).W (stopSet J Q N r.2.2.1 r.2.2.2.1 r.2.2.2.2) r.1
        ((chainModel J.whole).param Q ⟨r.1, r.2.1⟩) ∧
      (Lst J : ℝ) ≤ oW J (r.1 + (chainModel J.whole).param Q ⟨r.1, r.2.1⟩) := by
  have hs : (r.1, (chainModel J.whole).param Q ⟨r.1, r.2.1⟩,
      stopSet J Q N r.2.2.1 r.2.2.2.1 r.2.2.2.2) ∈ stopsOf J Q N rs := by
    unfold stopsOf; exact List.mem_map.2 ⟨r, hr, rfl⟩
  obtain ⟨hF, -, hA, hL⟩ := hS.1 _ hs
  obtain ⟨n1, n2⟩ := stopOrig_not_dom J hN (b := r.2.2.2.2) hkind hk
  refine ⟨⟨n2, n1, ?_⟩, hF, hA, hL⟩
  rw [← stopSet_eq]; exact hA.2.2.2.1

/-- **A regular table entry gives a candidate origin** at its position, attached at a log key. -/
theorem tab_cand (J : Merge.Junction) {Q : Polygon} {N : NF} {T : ℕ → Option (ℕ × ℝ)}
    (hT : TabOK J Q N T) {j : ℕ} (hj : j < 2 * N.nChords) (hon : endOrigin J Q N j ∈ J.right.set)
    (hsh : endOrigin J Q N j ≠ J.shared) (htop : endOrigin J Q N j ≠ J.right.top) {p : ℕ}
    {t : ℝ} (hTj : T j = some (p, t)) :
    CandAt J (endOrigin J Q N j) (endDir j) (sidePt (chainModel J.whole).W p t) ∧
      Merge.shoot J.whole (endOrigin J Q N j) (endDir j) ∈ F₂plus J (N.F (chainModel J.right) Q) ∧
      SideAttach (chainModel J.whole).W (Merge.shoot J.whole (endOrigin J Q N j) (endDir j)) p t ∧
      (Lst J : ℝ) ≤ oW J (p + t) := by
  obtain ⟨hfree, hm⟩ := hT j hj hon hsh htop
  rw [hTj] at hm
  obtain ⟨hA, hpt, hL⟩ := hm
  obtain ⟨n1, n2⟩ := right_not_dom J hon
  refine ⟨⟨n2, n1, ?_⟩, ?_, hA, hL⟩
  · rw [hpt]
    exact ⟨1, zero_le_one, le_rfl, by ext <;> simp⟩
  · left
    have hk : j / 2 < N.nChords := by omega
    have hc := chord_mem_F (M := chainModel J.right) (Q := Q) hk
    unfold endOrigin endDir at hfree ⊢
    by_cases h : j % 2 = 0
    · simp only [h, ite_true] at hfree ⊢
      left; left
      exact ⟨_, Or.inr hc, hfree, rfl⟩
    · simp only [h, ite_false] at hfree ⊢
      left; right
      exact ⟨_, Or.inr hc, hfree, rfl⟩

/-! ## Regular origins by their positions -/

/-- **The regular origins**: on `C₂`, neither the shared vertex nor the top, by a normalised walk
position of the model of `C₂`. -/
theorem valid_iff (J : Merge.Junction) (hP : J.right.P.Simple) (Q : Polygon) {x : WPos}
    (hx : x.edge < (chainModel J.right).W.n) (h0 : 0 ≤ (chainModel J.right).param Q x)
    (h1 : (chainModel J.right).param Q x < 1)
    (hnorm : x.hgt = 0 ↔ (chainModel J.right).param Q x = 0) :
    ((chainModel J.right).pos Q x ∈ J.right.set ∧ (chainModel J.right).pos Q x ≠ J.shared ∧
        (chainModel J.right).pos Q x ≠ J.right.top) ↔
      (6 ≤ x.edge ∧ x.edge ≤ 2 * J.right.m + 5 ∧
        (x.hgt ≠ 0 ∨ (x.edge ≠ 6 ∧ x.edge ≠ 6 + tpos J.right 0 ∧
          x.edge ≠ 6 + midT J.right))) := by
  have hmem := pos_mem_set_iff J.right hP (Q := Q) hx h0 h1 hnorm
  have hsh := atEnd_iff J.right hP (k := 0) (Or.inl rfl) Q hx h0 h1
  have htop := atTop_iff J.right hP Q hx h0 h1
  rw [Merge.Junction.right_vertex_zero] at hsh
  rw [hmem]
  constructor
  · rintro ⟨hm, hs, ht⟩
    rcases hm with ⟨h6, h5⟩ | ⟨he, hh⟩
    · refine ⟨h6, h5, ?_⟩
      by_cases hh : x.hgt = 0
      · right
        have hp0 := hnorm.1 hh
        refine ⟨fun h => ht (htop.2 ⟨hp0, Or.inl h⟩), fun h => hs (hsh.2 ⟨hp0, Or.inl h⟩),
          fun h => ht (htop.2 ⟨hp0, Or.inr (Or.inr h)⟩)⟩
      · left; exact hh
    · exact absurd (htop.2 ⟨hnorm.1 hh, Or.inr (Or.inl he)⟩) ht
  · rintro ⟨h6, h5, hc⟩
    refine ⟨Or.inl ⟨h6, h5⟩, fun h => ?_, fun h => ?_⟩
    · obtain ⟨hp0, he⟩ := hsh.1 h
      rcases hc with hc | ⟨-, hc, -⟩
      · exact hc (hnorm.2 hp0)
      · rcases he with he | ⟨he, -⟩
        · exact hc he
        · omega
    · obtain ⟨hp0, he⟩ := htop.1 h
      rcases hc with hc | ⟨hc1, -, hc3⟩
      · exact hc (hnorm.2 hp0)
      · rcases he with he | he | he
        · exact hc1 he
        · omega
        · exact hc3 he

end

end S0C

end SweepIo

end Chazelle.Core
