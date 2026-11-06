module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseMathOrd
public import Chazelle.Core.DownPhaseDrvSplice
public import Chazelle.Core.NFBuildValid

/-!
# Down phase, math (H-R1): the region records of `buildNF` and the host keys

For `N = buildNF I Q L E` (interior model `I` of `Q`, valid sorted input) and a region
correspondence `reg` of `N` (`Restore.NFRegs`):

* the arcs of region `r` (`(N.region r).arcs`) are arcs of `reg r`, listed in increasing order of
  their start keys, and every arc of `reg r` is listed (`regArcs_isArc`, `regArcs_sorted`,
  `regArcs_complete`);
* the ends of the arcs are chord positions `lpos`/`rpos` of chord records (`arc_pos`);
* a chord position is an attachment of its chord, at the height of its height vertex
  (`chordPos_attach`); two chord positions with the same key are equal (`chordPos_eq`,
  distinct heights); `DrvR.atVtx` tests whether a chord position is at a walk vertex
  (`atVtx_iff`).
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
open BuildNF (buildNF wposOf gapStarts)

variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- A **chord position** of `N`: an end (`lpos` or `rpos`) of one of its chord records. -/
def ChordPos (N : NF) (x : WPos) : Prop :=
  ∃ i, i < N.nChords ∧ (x = (N.chord i).lpos ∨ x = (N.chord i).rpos)

/-! ## Chord positions -/

section

variable {M : Model} {N : NF}

/-- **A chord position is an attachment of its chord**, at the height of its height vertex. -/
theorem chordPos_attach (hN : IsNF M Q N) {i : ℕ} (hi : i < N.nChords) {x : WPos}
    (hx : x = (N.chord i).lpos ∨ x = (N.chord i).rpos) :
    (N.chord i).toSet M Q ∈ N.F M Q ∧
      SideAttach M.W ((N.chord i).toSet M Q) x.edge (M.param Q x) ∧
      M.key Q x = x.edge + M.param Q x ∧ x.hgt = (N.chord i).h + 1 ∧ (N.chord i).h < Q.n ∧
      (sidePt M.W x.edge (M.param Q x)).2 = (Q.vtx (N.chord i).h).2 := by
  obtain ⟨-, -, hatt, reg, -, -, -, -, -, hh, -⟩ := hN
  have hmem : (N.chord i).toSet M Q ∈ N.F M Q := ⟨N.chord i, by
    unfold NF.chord; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi, rfl⟩
  have hA : SideAttach M.W ((N.chord i).toSet M Q) x.edge (M.param Q x) := by
    rcases hx with rfl | rfl
    · exact (hatt i hi).1
    · exact (hatt i hi).2
  refine ⟨hmem, hA, rfl, by rcases hx with rfl | rfl <;> rfl, hh i hi, ?_⟩
  have := hA.2.2.2.1
  exact this.1

end

/-! ## The region records of `buildNF` -/

theorem isNF_build (hQ : Q.Simple) (hL : ChordTriplesOK (interiorModel Q) Q L)
    (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (BuildNF.codeLe (interiorModel Q) Q L)) :
    IsNF (interiorModel Q) Q (buildNF (interiorModel Q) Q L E) :=
  (BuildNF.isNF_goodModel (Or.inr ⟨Q, hQ, rfl⟩) hL hperm hsort).1

theorem nChords_build (hQ : Q.Simple) (hL : ChordTriplesOK (interiorModel Q) Q L)
    (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (BuildNF.codeLe (interiorModel Q) Q L)) :
    (buildNF (interiorModel Q) Q L E).nChords = L.length := by
  have := (BuildNF.isNF_goodModel (Or.inr ⟨Q, hQ, rfl⟩) hL hperm hsort).2.1
  have h := congrArg List.length this
  simpa [NF.nChords] using h

/-- The arcs of region `r` of `buildNF` in record order. -/
theorem region_arcs_build {r : ℕ} (_hK : 0 < L.length) (hr : r < L.length + 1) :
    ((buildNF (interiorModel Q) Q L E).region r).arcs =
      BuildNF.regArcs (interiorModel Q) Q L E r := by
  unfold NF.region buildNF
  simp only
  Ξ List.getD_eq_getElem _ _ (by simpa using hr)
  simp

/-- **The arcs of a region are listed in increasing record order.** -/
theorem region_arcs_sorted {r : ℕ} (hK : 0 < L.length) (hr : r < L.length + 1) :
    ((buildNF (interiorModel Q) Q L E).region r).arcs.Pairwise (· < ·) := by
  Ξ region_arcs_build hK hr
  exact (List.pairwise_lt_range).filter _

/-- **The ends of an arc record are chord positions.** -/
theorem arc_pos (hQ : Q.Simple) (hL : ChordTriplesOK (interiorModel Q) Q L)
    (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (BuildNF.codeLe (interiorModel Q) Q L)) (hK : 0 < L.length) {j : ℕ}
    (hj : j < (buildNF (interiorModel Q) Q L E).arcs.length) :
    ChordPos (buildNF (interiorModel Q) Q L E) ((buildNF (interiorModel Q) Q L E).arc j).s ∧
      ChordPos (buildNF (interiorModel Q) Q L E) ((buildNF (interiorModel Q) Q L E).arc j).e := by
  set N := buildNF (interiorModel Q) Q L E
  have hnc : N.nChords = L.length := nChords_build hQ hL hperm hsort
  have hlen : N.arcs.length = (gapStarts (interiorModel Q) Q L E).length := by
    rw [DownDrv.buildNF_arcs hK, List.length_map]
  have hj' : j < (gapStarts (interiorModel Q) Q L E).length := hlen ▸ hj
  have harc := DownDrv.buildNF_arc (M := interiorModel Q) (Q := Q) (E := E) hK hj'
  have hE : E.length = 2 * L.length := by rw [hperm.length_eq, List.length_range]
  set m := (gapStarts (interiorModel Q) Q L E).getD j 0 with hm
  have hmE : m < E.length := by
    have hmem : m ∈ gapStarts (interiorModel Q) Q L E := by
      rw [hm, List.getD_eq_getElem _ _ hj']; exact List.getElem_mem hj'
    exact (BuildNF.Input.mem_gapStarts.1 hmem).1
  have hpos : ∀ u, u < E.length → ChordPos N (wposOf L (E.getD u 0)) := by
    intro u hu
    have hc : E.getD u 0 < 2 * L.length := by
      rw [List.getD_eq_getElem _ _ hu]
      exact List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hu))
    have hc' : E.getD u 0 / 2 < L.length := by omega
    refine ⟨E.getD u 0 / 2, hnc ▸ hc', ?_⟩
    have hchord : N.chord (E.getD u 0 / 2) = BuildNF.chordRec (interiorModel Q) Q L E
        (E.getD u 0 / 2) := by
      unfold NF.chord
      show ((List.range L.length).map (BuildNF.chordRec (interiorModel Q) Q L E)).getD _ _ = _
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hc'),
        List.getElem_map, List.getElem_range]
    rw [hchord]
    unfold wposOf
    split_ifs
    · left; rfl
    · right; rfl
  have he : N.arc j = _ := harc
  constructor
  · rw [show (N.arc j).s = wposOf L (E.getD m 0) by rw [he]]
    exact hpos m hmE
  · rw [show (N.arc j).e = wposOf L (E.getD ((m + 1) % E.length) 0) by rw [he]]
    exact hpos _ (Nat.mod_lt _ (by omega))

end

end DownMath

end Chazelle.Core
