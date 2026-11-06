module

public import Chazelle.Core.RestoreTestOK
public import Chazelle.Core.RestoreMath
public import Chazelle.Core.RestoreTHoleMath
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.MiscTactics

/-!
# WP-E, Lemma 3.2 part 14: the good candidate of the search

The search of Lemma 3.2 looks for a walk vertex `X` and a direction `σ` whose ray starts into the
left sector at `X` and whose chord up to the first exit splits the region well (`GoodCand`).
`exists_good`: under the hypotheses of `FindOK`'s completeness (`FullDegLe D`, more than `D`
exit chords), such a candidate exists: Lemma 3.3 (`exists_step`) gives a chord of the full map
splitting the region well, and a full chord is the ray segment from a walk vertex.

* `full_ray`: a full chord is the chord of the ray from a walk vertex, and every proper position
  of that vertex is a vertex position.
* `good_of_full`: the good candidate of a full chord splitting a region well.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sidePt SideAttach sideLeft)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open SweepPrim (candIdx)

variable {M : Model}

/-- **A good candidate** of the search for the region `R` of `S`: a walk vertex `X` and a
direction `σ` into its left sector whose ray first leaves the domain at `T`, with an admissible
chord splitting `R` well. -/
def GoodCand (M : Model) (Q : Polygon) (S : Set (Set Point)) (R : Set Point) (X : WPos)
    (σ T : ℝ) : Prop :=
  X.hgt = 0 ∧ X.edge < M.W.n ∧ (σ = 1 ∨ σ = -1) ∧ 0 < T ∧
    sideLeft M.W X.edge 0 (rayPt (M.pos Q X) σ 1) ∧
    (∀ t, 0 < t → t < T → rayPt (M.pos Q X) σ t ∈ M.D) ∧ rayPt (M.pos Q X) σ T ∉ M.D ∧
    chordOf (M.pos Q X) σ T ∈ M.Adm ∧ SplitsWell M S R (chordOf (M.pos Q X) σ T)

theorem iv_iv {Q : Polygon} {i : ℕ} (hi : i < Q.n) : IOrc.iv Q (IOrc.iv Q i) = i := by
  unfold IOrc.iv; splao

/-- **A full chord is the chord of the ray from a walk vertex** `p`; every proper position of
the vertex is a vertex position. -/
theorem full_ray (hGM : GoodModel M) {e : Set Point} (he : e ∈ M.Full) :
    ∃ p, p < M.W.n ∧ ∃ σ T : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < T ∧
      (∀ t, 0 < t → t < T → rayPt (M.W.vtx p) σ t ∈ M.D) ∧ rayPt (M.W.vtx p) σ T ∉ M.D ∧
      e = chordOf (M.W.vtx p) σ T ∧
      (∀ p' t', p' < M.W.n → 0 ≤ t' → t' < 1 → sidePt M.W p' t' = M.W.vtx p → t' = 0) ∧
      ∀ C : Chain, M = chainModel C → 6 ≤ p ∧ p ≤ 2 * C.m + 6 := by
  rcases hGM with ⟨C, hP, rfl⟩ | ⟨Q, hQ, rfl⟩
  · obtain ⟨k, σ, hk, hσ, hfree, rfl⟩ := he
    have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
    have cv := (SweepPrim.cand_vertex C C.sideBeta hk).1
    have hv : (chainModel C).W.vtx (candIdx C.m (C.sideS C.sideBeta) k + 6) = C.vertex k := by
      show (C.sideWalk C.sideBeta).vtx _ = _
      rw [C.sideWalk_vtx_tour _ cv.1, Chain.sideTour, cv.2]
    refine ⟨candIdx C.m (C.sideS C.sideBeta) k + 6, by rwo [hn], σ, C.chordParam k σ, hσ,
      C.chordParam_pos hk hσ hfree, fun t h0 h1 => ?_, ?_, ?_, fun p' t' hp' h0 h1 hpt => ?_,
      fun C' hC' => ?_⟩
    · rw [hv]; exact C.openChordSet_subset_dom hk hσ hfree ⟨t, ⟨h0, h1⟩, rfl⟩
    · rw [hv]; exact C.chordEnd_not_mem_dom hk hσ hfree
    · rw [hv, C.chordSet_eq_hseg, chordOf, Chain.chordEnd, rayPt_fst]
    · rw [hv] at hpt
      exact (chain_vertex_positions hP hk hp' h0 h1 hpt).1
    · have e1 : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
      have e2 : (chainModel C').W.n = 2 * C'.m + 7 := C'.sideWalk_n _
      rw [hC'] at e1
      have := cv.1
      omega
  · obtain ⟨i, σ, hi, hσ, hdir, rfl⟩ := he
    have hn : (interiorModel Q).W.n = Q.n := IOrc.mi_n
    have hp : IOrc.iv Q i < Q.n := IOrc.iv_lt hi
    have hv : (interiorModel Q).W.vtx (IOrc.iv Q i) = Q.vtx i := by
      show (interiorWalk Q).vtx _ = _
      rw [IOrc.iw_vtx hp, iv_iv hi]
    refine ⟨IOrc.iv Q i, by rwx [hn], σ, Visibility.chordParam Q i σ, hσ,
      Visibility.chordParam_pos hQ hi hdir, fun t h0 h1 => ?_, ?_, ?_,
      fun p' t' hp' h0 h1 hpt => ?_, fun C hC => ?_⟩
    · rw [hv]; exact Visibility.openChordSet_subset_interior hQ hi hdir ⟨t, ⟨h0, h1⟩, rfl⟩
    · rw [hv]
      exact fun h => h.2 (Visibility.chordEnd_mem_boundary hQ hi hdir)
    · rw [hv, Visibility.chordSet_eq_hseg, chordOf, Visibility.chordEnd, rayPt_fst]
    · have hWs : (interiorModel Q).W.Simple := (FactsInterior.interiorWalk_spec hQ).1
      have := FactsInterior.pos_unique hWs hp' (by rwx [hn]) h0 h1 le_rfl zero_lt_one
        (hpt.trans (Chazelle.Chain.sidePt_zero _ _).symm)
      exact this.2
    · have := congrArg (fun M : Model => M.counted 0) hC
      simp [interiorModel, chainModel] at this

/-- **The good candidate of a full chord**, with its attachments and its vertex. -/
theorem good_of_full' (hGM : GoodModel M) {Q : Polygon} {S : Set (Set Point)} {R : Set Point}
    {e : Set Point} (he : e ∈ M.Full) (hsw : SplitsWell M S R e) :
    ∃ X σ T, GoodCand M Q S R X σ T ∧ SideAttach M.W (chordOf (M.pos Q X) σ T) X.edge 0 ∧
      (∃ po tq, SideAttach M.W (chordOf (M.pos Q X) σ T) po tq ∧
        sidePt M.W X.edge 0 ≠ sidePt M.W po tq) ∧
      ∃ p, (∀ C : Chain, M = chainModel C → 6 ≤ p ∧ p ≤ 2 * C.m + 6) ∧ M.pos Q X = M.W.vtx p := by
  have hM := walkAx_of_goodModel hGM
  obtain ⟨p, hp, σ, T, hσ, hT, hdom, hout, rfl, hvtx, hrange⟩ := full_ray hGM he
  set v := M.W.vtx p with hvdef
  have hadm  := full_subset_adm hGM he
  obtain ⟨a, b, hab, hseg', hy, -, ⟨⟨pa, ta, hA, hpa⟩, -⟩, ⟨⟨pb, tb, hB, hpb⟩, -⟩⟩ := hM.ends _ hadm
  -- the vertex is an end of the segment
  have hw1 : (rayPt v σ T).1 ≠ v.1 := by
    rw [rayPt_fst]; rcases hσ with rfl | rfl <;> intro h <;> linarith
  have hvab : v = a ∨ v = b := by
    have e1 : chordOf v σ T = hseg a.2 (min a.1 b.1) (max a.1 b.1) := by
      rw [hseg', Visibility.segment_horizontal_eq_hseg hy]
    unfold chordOf at e1
    obtain ⟨ey, emin, emax⟩ := Merge.hseg_inj min_le_max e1
    rw [← rayPt_fst] at emin emax
    have hb2 : b.2 = v.2 := by rw [← hy, ← ey]
    rcases le_total v.1 (rayPt v σ T).1 with h | h
    · rw [min_eq_left h] at emin
      rcases le_total a.1 b.1 with h' | h'
      · rw [min_eq_left h'] at emin; exact Or.inl (Prod.ext emin ey)
      · rw [min_eq_right h'] at emin; exact Or.inr (Prod.ext emin hb2.symm)
    · rw [max_eq_left h] at emax
      rcases le_total a.1 b.1 with h' | h'
      · rw [max_eq_right h'] at emax; exact Or.inr (Prod.ext emax hb2.symm)
      · rw [max_eq_left h'] at emax; exact Or.inl (Prod.ext emax ey)
  -- the attachment at the vertex
  obtain ⟨pv, tv, hAv, hpv, po, tq, hAo, hpo⟩ : ∃ pv tv, SideAttach M.W (chordOf v σ T) pv tv ∧
      sidePt M.W pv tv = v ∧ ∃ po tq, SideAttach M.W (chordOf v σ T) po tq ∧
        sidePt M.W po tq ≠ v := by
    rcases hvab with h | h
    · exact ⟨pa, ta, hA, hpa.trans h.symm, pb, tb, hB, by rw [hpb, h]; exact hab.symm⟩
    · exact ⟨pb, tb, hB, hpb.trans h.symm, pa, ta, hA, by rwx [hpa, h]⟩
  have htv  := hvtx pv tv hAv.1 hAv.2.1 hAv.2.2.1 hpv
  subst htv
  have hposX : M.pos Q ⟨pv, 0⟩ = v := by
    show Geometry.lerp (M.wa pv) (M.wb pv) (M.param Q ⟨pv, 0⟩) = v
    rw [param_vtx]
    exact hpv
  refine ⟨⟨pv, 0⟩, σ, T, ⟨rfl, hAv.1, hσ, hT, ?_, by rwx [hposX],
    by rwx [hposX], by rwx [hposX], by rwx [hposX]⟩,
    by rwx [hposX], ⟨po, tq, by rwx [hposX], by rw [hpv]; exact hpo.symm⟩,
    p, hrange, hposX⟩
  -- the ray starts into the left sector
  obtain ⟨-, -, -, -, r, hr, hsec⟩ := hAv
  set s := min (r / 2) (T / 2) with hsdef
  have hs  := lt_min (half_pos hr) (half_pos hT)
  have hsr : s ≤ r / 2 := min_le_left _ _
  have hsT : s ≤ T / 2 := min_le_right _ _
  have hmem : rayPt v σ s ∈ chordOf v σ T := (mem_chordOf hσ hT.le).2 ⟨s, hs.le, by linarith, rfl⟩
  have hd : dist (rayPt v σ s) v = s := Sweep.dist_rayPt _ hσ hs.le
  have hne : rayPt v σ s ≠ sidePt M.W pv 0 := by
    rw [hpv]; intro h; rwli [h, dist_self] at hd
  have hsl := hsec _ hmem hne (by rwli [hpv, hd])
  show sideLeft M.W pv 0 (rayPt (M.pos Q ⟨pv, 0⟩) σ 1)
  rw [hposX, ← hpv] at *
  exact (Sweep.sideLeft_rayPt_iff M.W pv 0 σ one_pos hs).2 hsl

/-- **A good candidate exists**, with its attachments and its vertex. -/
theorem exists_good' (hGM : GoodModel M) {Q : Polygon} {D : ℕ} (hfull : M.FullDegLe Q D)
    {S : Set (Set Point)} (hS : M.ChordFamily Q S) {R : Set Point}
    (hR : R ∈ Chazelle.Chain.regionsIn M.D S) (hdeg : D < (Chazelle.Merge.exitsIn M.D S R).ncard) :
    ∃ X σ T, GoodCand M Q S R X σ T ∧ SideAttach M.W (chordOf (M.pos Q X) σ T) X.edge 0 ∧
      (∃ po tq, SideAttach M.W (chordOf (M.pos Q X) σ T) po tq ∧
        sidePt M.W X.edge 0 ≠ sidePt M.W po tq) ∧
      ∃ p, (∀ C : Chain, M = chainModel C → 6 ≤ p ∧ p ≤ 2 * C.m + 6) ∧ M.pos Q X = M.W.vtx p := by
  obtain ⟨e, he, hsw⟩ := exists_step hGM hfull hS hR hdeg
  exact good_of_full' hGM he hsw

/-- **The first exit of a ray is unique.** -/
theorem exit_unique {D : Set Point} {z : Point} {σ T T' : ℝ} (hT : 0 < T) (hT' : 0 < T')
    (hdom : ∀ t, 0 < t → t < T → rayPt z σ t ∈ D) (hout : rayPt z σ T ∉ D)
    (hdom' : ∀ t, 0 < t → t < T' → rayPt z σ t ∈ D) (hout' : rayPt z σ T' ∉ D) : T = T' := by
  rcases lt_trichotomy T T' with h | h | h
  · exact absurd (hdom' T hT h) hout
  · exact h
  · exact absurd (hdom T' hT' h) hout'

end

end Restore

end Chazelle.Core
