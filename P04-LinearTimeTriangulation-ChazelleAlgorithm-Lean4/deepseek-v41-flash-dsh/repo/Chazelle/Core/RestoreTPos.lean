module

public import Chazelle.Golf

public import Chazelle.Core.RestoreTKey
public import Chazelle.Core.RestoreCompleteInt

/-!
# WP-E, the candidate test on the RAM, part 5: the positions the test compares

The test compares keys of positions at heights of chords (the ends of exit chords, the ends of
the arcs of a region of a nonempty family, the candidate and its arrival position).  Such points
are strictly inside the height band of the box (`chord_height_lt`), so the positions are valid
inputs of `offCmp` (`PosOK`).

* `posOK_of_attach`: a position at which an admissible chord is attached.
* `chord_posOK`: the ends of the chord records of a normal form.
* `arc_posOK`: the ends of the arc records of a nonempty family.
* `endpoints_lt`: the left end of an attached record is left of its right end.
* `exit_block`: an attached record whose left (right) end is the candidate vertex contains ray
  points near it in direction `1` (`-1`): the completeness half of the exit scan.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideKey_inj)
open Chazelle.Visibility (rayPt)
open Sweep

/-- The points of an admissible chord of a chain model are strictly inside the height band of
the box. -/
theorem chord_height_lt {C : Chain} (hP : C.P.Simple) {c : Set Point}
    (hc : c ∈ (chainModel C).Adm) {z : Point} (hz : z ∈ c) : |z.2| < C.radius := by
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  obtain ⟨y, a, b, hH, rfl⟩ := adm_hchord hGM hc
  have hy := hz.1
  have hm : (((a + b) / 2, y) : Point) ∈ (chainModel C).D :=
    hH.open_mem _ (by linarith [hH.lt]) (by linarith [hH.lt])
  have := (C.dom_subset_box hm).2
  rw [hy]; exact this

/-- **A position at which an admissible chord is attached** is a valid input of `offCmp`. -/
theorem posOK_of_attach {C : Chain} (hP : C.P.Simple) {Q : Polygon} {n : ℕ} {x : WPos}
    {c : Set Point} (hc : c ∈ (chainModel C).Adm)
    (hA : SideAttach (chainModel C).W c x.edge ((chainModel C).param Q x)) (hh : x.hgt ≤ n) :
    PosOK C Q n x :=
  posOK_of hA.1 ⟨hA.2.1, hA.2.2.1, hh⟩ (chord_height_lt hP hc hA.2.2.2.1)

variable {C : Chain} {P : Polygon} {N : NF}

theorem chord_mem_list {i : ℕ} (hi : i < N.nChords) : N.chord i ∈ N.chords := by
  unfold NF.chord
  Ξ List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some
  exact List.getElem_mem hi

/-- **The ends of the chord records** are valid inputs of `offCmp`. -/
theorem chord_posOK (hP : C.P.Simple) (hNF : IsNF (chainModel C) (Qof P) N) {i : ℕ}
    (hi : i < N.nChords) :
    PosOK C (Qof P) P.n (N.chord i).lpos ∧ PosOK C (Qof P) P.n (N.chord i).rpos := by
  obtain ⟨hFam, -, hat, reg, -, -, -, -, -, hh, -⟩ := hNF
  have hQ : (Qof P).n = P.n := shear_n _ _
  have hadm : (N.chord i).toSet (chainModel C) (Qof P) ∈ (chainModel C).Adm :=
    hFam.2.1 ⟨_, chord_mem_list hi, rfl⟩
  have hhn : (N.chord i).h + 1 ≤ P.n := by have := hh i hi; omega
  exact ⟨posOK_of_attach hP hadm (hat i hi).1 hhn, posOK_of_attach hP hadm (hat i hi).2 hhn⟩

/-- **The ends of the arc records** of a nonempty family are valid inputs of `offCmp`. -/
theorem arc_posOK (hP : C.P.Simple) (hNF : IsNF (chainModel C) (Qof P) N)
    (hne : (N.F (chainModel C) (Qof P)).Nonempty) {j : ℕ} (hj : j < N.arcs.length) :
    PosOK C (Qof P) P.n (N.arc j).s ∧ PosOK C (Qof P) P.n (N.arc j).e := by
  obtain ⟨hFam, -, -, reg, -, -, harcs, -, -, -, hpp⟩ := hNF
  have hQ : (Qof P).n = P.n := shear_n _ _
  obtain ⟨hs, he⟩ := hpp j hj
  have harc := (harcs.1 j hj).2
  obtain ⟨hcs, hce, -⟩ := WalkAx.arc_cuts hne harc
  have key : ∀ x : WPos, ProperPos (chainModel C) (Qof P) (Qof P).n x →
      (chainModel C).IsCut (N.F (chainModel C) (Qof P)) ((chainModel C).key (Qof P) x) →
      PosOK C (Qof P) P.n x := by
    intro x hx hcut
    obtain ⟨c, hc, p, t, hA, hk⟩ := hcut
    obtain ⟨hpp, htt⟩ := sideKey_inj hx.1 hx.2.1 hA.2.1 hA.2.2.1 hk
    rw [← hpp, ← htt] at hA
    exact posOK_of_attach hP (hFam.2.1 hc) hA (by rw [← hQ]; exact hx.2.2)
  exact ⟨key _ hs hcs, key _ he hce⟩

/-- **The left end of an attached admissible record is left of its right end.** -/
theorem endpoints_lt {M : Model} (hM : WalkAx M) {Q : Polygon} {r : CRec}
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
  exact hab (Geometry.point_ext ((hsub a ha).trans (hsub b hb).symm) hy)

/-- **The exit scan is complete**: an attached admissible record whose left end is the walk vertex
`(p, 0)` contains ray points arbitrarily close to the vertex in direction `1`; one whose right end
is the vertex, in direction `-1`. -/
theorem exit_block {M : Model} (hM : WalkAx M) {Q : Polygon} {cr : CRec}
    (hadm : cr.toSet M Q ∈ M.Adm) (hat : cr.Attached M Q) {p : ℕ} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1)
    (hend : (σ = 1 ∧ cr.lp = p ∧ M.param Q cr.lpos = 0) ∨
      (σ = -1 ∧ cr.rp = p ∧ M.param Q cr.rpos = 0))
    (hav : ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) σ s ∉ cr.toSet M Q) : False := by
  have hlt := endpoints_lt hM hadm hat
  have epl : sidePt M.W cr.lp (M.param Q cr.lpos) = M.pos Q cr.lpos := rfl
  have epr : sidePt M.W cr.rp (M.param Q cr.rpos) = M.pos Q cr.rpos := rfl
  rcases hend with ⟨rfl, hl, h0⟩ | ⟨rfl, hl, h0⟩
  · have hA := hat.1
    rw [hl, h0] at hA
    obtain ⟨d, -, hall, -, -⟩ := attached_opposite hM hadm hA hσ hav
    obtain ⟨s, hs0, -, hx⟩ := hall _ hat.2.2.2.2.1
    rw [epr] at hx
    have e1 : (M.pos Q cr.rpos).1 = (sidePt M.W p 0).1 - s := by
      rw [hx]; simp only [Visibility.rayPt]; ring
    have e2 : sidePt M.W p 0 = M.pos Q cr.lpos := Ρ ← epl, hl, h0
    rw [e2] at e1
    linarith
  · have hA := hat.2
    rw [hl, h0] at hA
    obtain ⟨d, -, hall, -, -⟩ := attached_opposite hM hadm hA hσ hav
    obtain ⟨s, hs0, -, hx⟩ := hall _ hat.1.2.2.2.1
    rw [epl] at hx
    have e1 : (M.pos Q cr.lpos).1 = (sidePt M.W p 0).1 + s := by
      rw [hx]; simp only [Visibility.rayPt]; ring
    have e2 : sidePt M.W p 0 = M.pos Q cr.rpos := Ρ ← epr, hl, h0
    rw [e2] at e1
    linarith

end

end Restore

end Chazelle.Core
