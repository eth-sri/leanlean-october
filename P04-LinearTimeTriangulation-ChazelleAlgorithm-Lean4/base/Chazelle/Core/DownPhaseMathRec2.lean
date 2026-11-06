module

public import Chazelle.Core.DownPhaseMathRec

/-!
# Down phase, math (H-R1): region records of `buildNF`, continued

* `regArcs_facts`: the arcs of region `r` are arcs of `reg r`, sorted by start key, complete;
* `chordPos_eq`: chord positions with equal keys are equal (distinct heights);
* `chordPos_ne`: the two ends of a chord record have distinct keys;
* `atVtx_iff`: `DrvR.atVtx` tests that a chord position is at a walk vertex;
* `partner_spec`: `DrvR.partner` returns the other end of an exit chord record of `r`.
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)
open DownHost
open BuildNF (buildNF)
open DrvR (ivB qE atVtx partner)

variable {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-! ## Chord positions -/

section

variable {M : Model} {N : NF}

/-- **Chord positions with the same key are equal** (distinct heights). -/
theorem chordPos_eq (hN : IsNF M Q N) (hdh : DistinctHeights Q) {x x' : WPos}
    (hx : ChordPos N x) (hx' : ChordPos N x') (hk : M.key Q x = M.key Q x') : x = x' := by
  obtain ⟨i, hi, hxi⟩ := hx
  obtain ⟨i', hi', hxi'⟩ := hx'
  obtain ⟨-, hA, ek, eh, hh, hy⟩ := chordPos_attach hN hi hxi
  obtain ⟨-, hA', ek', eh', hh', hy'⟩ := chordPos_attach hN hi' hxi'
  rw [ek, ek'] at hk
  obtain ⟨he, hp⟩ := key_inj hA.2.1 hA.2.2.1 hA'.2.1 hA'.2.2.1 hk
  have hyy : (Q.vtx (N.chord i).h).2 = (Q.vtx (N.chord i').h).2 := by
    rw [← hy, ← hy', he, hp]
  have hhh : (N.chord i).h = (N.chord i').h := by
    by_contra hne; exact hdh _ _ hh hh' hne hyy
  cases x; cases x'
  simp only at he eh eh'
  rw [he, eh, eh', hhh]

/-- **The two ends of a chord record have distinct keys.** -/
theorem chordPos_ne (hN : IsNF M Q N) (hM : WalkAx M) {i : ℕ} (hi : i < N.nChords) :
    M.key Q (N.chord i).lpos ≠ M.key Q (N.chord i).rpos := by
  intro hk
  obtain ⟨hmem, hA, ek, -, -, -⟩ := chordPos_attach hN hi (Or.inl rfl)
  obtain ⟨-, hA', ek', -, -, -⟩ := chordPos_attach hN hi (Or.inr rfl)
  rw [ek, ek'] at hk
  obtain ⟨he, hp⟩ := key_inj hA.2.1 hA.2.2.1 hA'.2.1 hA'.2.2.1 hk
  have hP : M.pos Q (N.chord i).lpos = M.pos Q (N.chord i).rpos := by
    unfold Model.pos; rw [he, hp]
  have hF := hN.1.2.1 hmem
  obtain ⟨a, b, hab, hcab, -⟩ := hM.ends _ hF
  have ha : a ∈ (N.chord i).toSet M Q := by rw [hcab]; exact Geometry.left_mem_segment _ _
  have hb : b ∈ (N.chord i).toSet M Q := by rw [hcab]; exact Geometry.right_mem_segment _ _
  unfold CRec.toSet at ha hb
  rw [hP] at ha hb
  apply hab
  obtain ⟨ha2, ha1, ha1'⟩ := ha
  obtain ⟨hb2, hb1, hb1'⟩ := hb
  exact Prod.ext (by linarith) (ha2.trans hb2.symm)

end

/-- **`DrvR.atVtx` tests that a chord position is at a walk vertex** (distinct heights). -/
theorem atVtx_iff {N : NF} (hN : IsNF (interiorModel Q) Q N) (hdh : DistinctHeights Q)
    {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) {x : WPos} (hx : ChordPos N x) :
    atVtx li Q.n x = true ↔
      (interiorModel Q).key Q x = ⌊(interiorModel Q).key Q x⌋₊ := by
  obtain ⟨i, hi, hxi⟩ := hx
  obtain ⟨-, hA, ek, eh, hh, hy⟩ := chordPos_attach hN hi hxi
  have hp : x.edge < Q.n := walk_n Q ▸ hA.1
  have hW : (interiorModel Q).W = interiorWalk Q := rfl
  rw [ek, floor_add hA.2.1 hA.2.2.1]
  unfold atVtx
  rw [decide_eq_true_iff, eh, Nat.add_sub_cancel]
  constructor
  · intro h
    have hpar : (interiorModel Q).param Q x = 0 := by
      have e : (interiorModel Q).param Q x =
          if ((interiorModel Q).wa x.edge).2 = ((interiorModel Q).wb x.edge).2 then 0
          else ((Q.vtx (N.chord i).h).2 - ((interiorModel Q).wa x.edge).2) /
            (((interiorModel Q).wb x.edge).2 - ((interiorModel Q).wa x.edge).2) := by
        unfold Model.param; rw [eh]
      rw [e]
      split_ifs
      · rfl
      · rw [h]; unfold Model.wa; rw [hW, walk_vtx hli hp, sub_self, zero_div]
    rw [hpar, add_zero]
  · intro h
    have hp0 : (interiorModel Q).param Q x = 0 := by linarith
    rw [hp0, Chazelle.Chain.sidePt_zero, hW, walk_vtx hli hp] at hy
    by_contra hne
    exact hdh _ _ hh (ivB_lt li hp) hne hy.symm

/-- **`DrvR.partner` returns the other end of an exit chord record** attached at `x`. -/
theorem partner_spec {N : NF} {r : ℕ} {x : WPos}
    (hxc : ∃ i ∈ (N.region r).chords, x = (N.chord i).lpos ∨ x = (N.chord i).rpos) :
    ∃ i ∈ (N.region r).chords,
      (x = (N.chord i).lpos ∧ partner N r x = (N.chord i).rpos) ∨
        (x = (N.chord i).rpos ∧ partner N r x = (N.chord i).lpos) := by
  obtain ⟨i, hi, hx⟩ := hxc
  set p : ℕ → Bool := fun i => decide ((N.chord i).lpos = x ∨ (N.chord i).rpos = x) with hp
  have hsome : ((N.region r).chords.find? p).isSome := by
    rw [List.find?_isSome]
    refine ⟨i, hi, ?_⟩
    simp only [hp, decide_eq_true_eq]
    rcases hx with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  obtain ⟨i₀, h₀⟩ := Option.isSome_iff_exists.1 hsome
  have hpi := List.find?_some h₀
  have hmi := List.mem_of_find?_eq_some h₀
  simp only [hp, decide_eq_true_eq] at hpi
  refine ⟨i₀, hmi, ?_⟩
  unfold partner
  rw [show (N.region r).chords.find? (fun i => decide ((N.chord i).lpos = x ∨ (N.chord i).rpos = x))
    = some i₀ from h₀]
  simp only
  by_cases hl : (N.chord i₀).lpos = x
  · left; rw [ite_eq_left hl]; exact ⟨hl.symm, rfl⟩
  · right; rw [ite_eq_right hl]; exact ⟨(hpi.resolve_left hl).symm, rfl⟩

/-! ## The arcs of a region record -/

/-- **The arcs of region `r` of `buildNF`**: arcs of `reg r`, sorted by start key, complete. -/
theorem regArcs_facts (hQ : Q.Simple) (hL : ChordTriplesOK (interiorModel Q) Q L)
    (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (BuildNF.codeLe (interiorModel Q) Q L)) (hK : 0 < L.length)
    {reg : ℕ → Set Point}
    (hregs : Restore.NFRegs (interiorModel Q) Q (buildNF (interiorModel Q) Q L E) reg) {r : ℕ}
    (hr : r < (buildNF (interiorModel Q) Q L E).nRegions) :
    let N := buildNF (interiorModel Q) Q L E
    let as := (N.region r).arcs
    (∀ t, t < as.length → as.getD t 0 < N.arcs.length ∧
      (interiorModel Q).IsArc (N.F (interiorModel Q) Q) (reg r)
        ((interiorModel Q).key Q (N.arc (as.getD t 0)).s)
        ((interiorModel Q).key Q (N.arc (as.getD t 0)).e)) ∧
    (∀ t t', t < t' → t' < as.length →
      (interiorModel Q).key Q (N.arc (as.getD t 0)).s <
        (interiorModel Q).key Q (N.arc (as.getD t' 0)).s) ∧
    (∀ a b, (interiorModel Q).IsArc (N.F (interiorModel Q) Q) (reg r) a b →
      ∃ t, t < as.length ∧ (interiorModel Q).key Q (N.arc (as.getD t 0)).s = a ∧
        (interiorModel Q).key Q (N.arc (as.getD t 0)).e = b) := by
  intro N as
  obtain ⟨-, -, ⟨hA1, hA2, hA3, hA4⟩, -⟩ := hregs
  have hN := isNF_build (E := E) hQ hL hperm hsort
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, hseq⟩, -, -⟩ := hN
  have hnr : r < L.length + 1 := by
    have : (buildNF (interiorModel Q) Q L E).nRegions = L.length + 1 := by
      simp [NF.nRegions, buildNF]
    omega
  have hsorted : as.Pairwise (· < ·) := region_arcs_sorted hK hnr
  have hget : ∀ t (ht : t < as.length), as.getD t 0 = as[t]'ht := fun t ht =>
    List.getD_eq_getElem _ _ ht
  have hmem : ∀ t, t < as.length → as.getD t 0 < N.arcs.length ∧
      (N.arc (as.getD t 0)).reg = r := by
    intro t ht
    rw [hget t ht]
    exact (hA4 r hr _).1 (List.getElem_mem ht)
  refine ⟨fun t ht => ?_, fun t t' htt ht' => ?_, fun a b hab => ?_⟩
  · obtain ⟨hj, hreg⟩ := hmem t ht
    have := (hA1 _ hj).2
    rw [hreg] at this
    exact ⟨hj, this⟩
  · obtain ⟨hj, hreg⟩ := hmem t (by omega)
    obtain ⟨hj', hreg'⟩ := hmem t' ht'
    have hlt : as.getD t 0 < as.getD t' 0 := by
      rw [hget t (by omega), hget t' ht']
      exact List.pairwise_iff_getElem.1 hsorted t t' (by omega) ht' htt
    have hle : (interiorModel Q).key Q (N.arc (as.getD t 0)).s ≤
        (interiorModel Q).key Q (N.arc (as.getD t' 0)).s := by
      have := List.pairwise_iff_getElem.1 hseq (as.getD t 0) (as.getD t' 0)
        (by rw [DownDrv.buildNF_seq, List.length_range]; exact lt_trans hlt hj')
        (by rw [DownDrv.buildNF_seq, List.length_range]; exact hj') hlt
      simpa [DownDrv.buildNF_seq] using this
    refine lt_of_le_of_ne hle fun he => ?_
    have := hA2 _ _ hj hj' (hreg.trans hreg'.symm) he
    omega
  · obtain ⟨j, hj, hreg, hs, he⟩ := hA3 r hr a b hab
    have hjm : j ∈ as := (hA4 r hr j).2 ⟨hj, hreg⟩
    obtain ⟨t, ht, htj⟩ := List.getElem_of_mem hjm
    exact ⟨t, ht, by rw [hget t ht, htj, hs], by rw [hget t ht, htj, he]⟩

end

end DownMath

end Chazelle.Core
