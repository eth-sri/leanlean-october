module

public import Chazelle.Core.SweepIoAns
public import Chazelle.Core.OracleCand
public import Chazelle.Core.RestoreTNear
public import Chazelle.Core.RestoreHoles
public import Chazelle.Core.ShotListTop

/-!
# The sweep (WP-D), answers: the local hit in one chain model

A query of the sweep (or a point with a position in the model of one chain) is answered in that
model by **local shooting**: the ray leaves its walk position `x` into the left sector, and its
first hit on the chain is found among

* the arcs of the regions of the three arcs at the spine positions `j - 1`, `j`, `j + 1`, where `j`
  is an answer of double identification for the key of `x` (`LocateSpec`'s postcondition), with
  holes cut around the positions of the origin (`Restore.Near`);
* the far ends of the exit chords of these regions attached at `x` along the ray (`ChordAt`).

`local_hit_mem`: the direction is free for the chain, and its exit point lies in the arcs outside
the closed holes or is the far end of such a chord (completeness).  Soundness is free: all walk
points and chord ends are off the domain.  The proof follows `leave_cases`: along a chord (its
region on some side is faced just after or before `x`, `faced_or_middle`, so the chord is an exit
chord of one of the three regions), at a non-cut key (the region of the arc around it), at a cut
walk vertex (the region faced just after or before, whose arc starts or ends at the key).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sideInArc sideCross TouchesIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open OracleQ (sj sk ek succP predP)

namespace Sweep

/-! ## Chord records -/

section Records

variable {M : Model} {Q : Polygon} {N : NF}

/-- A chord of the family of a normal form is the chord of a record. -/
theorem nf_chord_of_mem {e : Set Point} (he : e ∈ N.F M Q) :
    ∃ k, k < N.nChords ∧ (N.chord k).toSet M Q = e := by
  obtain ⟨r, hr, rfl⟩ := he
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  refine ⟨k, hk, ?_⟩
  unfold NF.chord
  rw [NFLoc.getD_of_lt _ hk]

/-- Two horizontal segments with a nondegenerate second one are equal only with equal ends. -/
theorem hseg_eq_ends {y L R y' a b : ℝ} (h : hseg y L R = hseg y' a b) (hab : a < b) :
    L = a ∧ R = b ∧ y = y' := by
  have ha : ((a, y') : Point) ∈ hseg y L R := by rw [h]; exact ⟨rfl, le_rfl, hab.le⟩
  have hb : ((b, y') : Point) ∈ hseg y L R := by rw [h]; exact ⟨rfl, hab.le, le_rfl⟩
  obtain ⟨hy, haL, haR⟩ := ha
  obtain ⟨-, hbL, hbR⟩ := hb
  simp only at hy haL haR hbL hbR
  have hL : ((L, y) : Point) ∈ hseg y' a b := by rw [← h]; exact ⟨rfl, le_rfl, by linarith⟩
  have hR : ((R, y) : Point) ∈ hseg y' a b := by rw [← h]; exact ⟨rfl, by linarith, le_rfl⟩
  obtain ⟨-, hL1, -⟩ := hL
  obtain ⟨-, -, hR2⟩ := hR
  simp only at hL1 hR2
  exact ⟨le_antisymm haL hL1, le_antisymm hR2 hbR, hy.symm⟩

/-- **The ends of an attached record** of a nondegenerate horizontal chord. -/
theorem rec_pos_ends {c : CRec} (hA : c.Attached M Q) {y a b : ℝ}
    (hc : c.toSet M Q = hseg y a b) (hab : a < b) :
    M.pos Q c.lpos = (a, y) ∧ M.pos Q c.rpos = (b, y) ∧ (Q.vtx c.h).2 = y := by
  have hl : M.pos Q c.lpos ∈ c.toSet M Q := hA.1.2.2.2.1
  have hr : M.pos Q c.rpos ∈ c.toSet M Q := hA.2.2.2.2.1
  have hset : c.toSet M Q = hseg (Q.vtx c.h).2 (M.pos Q c.lpos).1 (M.pos Q c.rpos).1 := rfl
  obtain ⟨hL, hR, hy⟩ := hseg_eq_ends (hset.symm.trans hc) hab
  have hl2 : (M.pos Q c.lpos).2 = (Q.vtx c.h).2 := by rw [hset] at hl; exact hl.1
  have hr2 : (M.pos Q c.rpos).2 = (Q.vtx c.h).2 := by rw [hset] at hr; exact hr.1
  exact ⟨Prod.ext hL (hl2.trans hy), Prod.ext hR (hr2.trans hy), hy⟩

end Records

/-! ## Regions touching a chord -/

/-- A region on a side of an attached admissible chord touches it. -/
theorem touchesIn_of_sideOf {M : Model} (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm)
    {p : ℕ} {t : ℝ} (hA : SideAttach M.W c p t) {ρ : ℝ} {U : Set Point}
    (hS : SideOf M ρ c U) : TouchesIn M.D c U := by
  obtain ⟨z, hz, hzD⟩ := exists_mem_dom hM hc hA
  refine ⟨z, ⟨hz, hzD⟩, ?_⟩
  have hev := hS z hz hzD
  have hlim : Tendsto (fun δ : ℝ => ((z.1, z.2 + ρ * δ) : Point)) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have hc0 : Continuous (fun δ : ℝ => ((z.1, z.2 + ρ * δ) : Point)) := by fun_prop
    have := hc0.tendsto 0
    simp only [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact mem_closure_of_tendsto hlim hev

/-! ## The spine around a key -/

section Spine

variable {M : Model} {Q : Polygon} {N : NF} (hN : IsNF M Q N) (hGM : GoodModel M)
  (hne : (N.F M Q).Nonempty)
include hN hGM hne

/-- The arc starting at a located cut is at spine position `j` or `j + 1`. -/
theorem spine_start {κ : ℝ} {j : ℕ} (hj : j < N.arcs.length)
    (hloc : sk M Q N j = κ ∨ ek M Q N j = κ) {p : ℕ} (hp : p < N.arcs.length)
    (hs : sk M Q N p = κ) : p = j ∨ p = succP N.arcs.length j := by
  rcases hloc with h | h
  · exact Or.inl (OracleQ.start_unique hN hGM hne hp hj (hs.trans h.symm))
  · exact Or.inr (OracleQ.end_start_adj hN hGM hne hj hp (h.trans hs.symm))

/-- The arc ending at a located cut is at spine position `j - 1` or `j`. -/
theorem spine_end {κ : ℝ} {j : ℕ} (hj : j < N.arcs.length)
    (hloc : sk M Q N j = κ ∨ ek M Q N j = κ) {p : ℕ} (hp : p < N.arcs.length)
    (he : ek M Q N p = κ) : p = predP N.arcs.length j ∨ p = j := by
  rcases hloc with h | h
  · left
    have := OracleQ.end_start_adj hN hGM hne hp hj (he.trans h.symm)
    rw [this, OracleQ.predP_succP hp]
  · exact Or.inr (OracleQ.end_unique hN hGM hne hp hj (he.trans h.symm))

end Spine

/-! ## Arcs of the regions around a key -/

section Around

variable {M : Model} {Q : Polygon} {N : NF}

/-- The region indices of the arcs at the spine positions `j - 1`, `j`, `j + 1`. -/
def nbrRegs (N : NF) (j : ℕ) : List ℕ :=
  [(N.arc (sj N (predP N.arcs.length j))).reg, (N.arc (sj N j)).reg,
    (N.arc (sj N (succP N.arcs.length j))).reg]

/-- **A region with an arc starting or ending at a located cut** is one of the three. -/
theorem region_of_arc_at (hN : IsNF M Q N) (hGM : GoodModel M) (hne : (N.F M Q).Nonempty)
    {κ : ℝ} {j : ℕ} (hj : j < N.arcs.length) (hloc : sk M Q N j = κ ∨ ek M Q N j = κ)
    {r : ℕ} (hr : r < N.nRegions) {a b : ℝ}
    (harc : M.IsArc (N.F M Q) (regOf M Q N r) a b) (hab : a = κ ∨ b = κ) : r ∈ nbrRegs N j := by
  obtain ⟨hRC, -, hArcs, -⟩ := regOf_spec hN
  obtain ⟨i, hi, hir, his, hie⟩ := hArcs.2.2.1 r hr a b harc
  obtain ⟨p, hp, hpi⟩ := NFLoc.seq_surj hN hi
  have hsj : sj N p = i := hpi
  have hA := N.arcs.length
  rcases hab with rfl | rfl
  · have hs : sk M Q N p = a := by unfold sk; rw [hsj, his]
    rcases spine_start hN hGM hne hj hloc hp hs with rfl | rfl
    · simp only [nbrRegs, List.mem_cons, List.not_mem_nil, or_false]
      right; left; rw [hsj, hir]
    · simp only [nbrRegs, List.mem_cons, List.not_mem_nil, or_false]
      right; right; rw [hsj, hir]
  · have he : ek M Q N p = b := by unfold ek; rw [hsj, hie]
    rcases spine_end hN hGM hne hj hloc hp he with rfl | rfl
    · simp only [nbrRegs, List.mem_cons, List.not_mem_nil, or_false]
      left; rw [hsj, hir]
    · simp only [nbrRegs, List.mem_cons, List.not_mem_nil, or_false]
      right; left; rw [hsj, hir]

/-- A region of the family is `regOf` of an index. -/
theorem regOf_surj (hN : IsNF M Q N) {U : Set Point} (hU : U ∈ M.regions (N.F M Q)) :
    ∃ r, r < N.nRegions ∧ regOf M Q N r = U :=
  (regOf_spec hN).1.2.2 U hU

end Around

/-! ## Facing just after and just before a cut -/

section Facing

variable {M : Model}

/-- An arc faces its region just before its end inside a walk edge. -/
theorem beforeFaces_of_arc_end' {F : Set (Set Point)} {U : Set Point} {l : ℝ} {p : ℕ}
    (hp : p < M.W.n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (harc : M.IsArc F U l (p + t))
    (hlr : l ≠ (p : ℝ) + t) : BeforeFaces M p t U := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (sideInArc_before_end hlr)
  refine ⟨δ, hδ, fun _ s hs0 hs1 hst => ?_, fun h => absurd h ht0.ne'⟩
  have := hsub ⟨hs0, hs1⟩
  refine harc.2.2.2.2.2.2 p (t - s) hp (by linarith) (by linarith) ?_
  have e : (p : ℝ) + (t - s) = (p : ℝ) + t - s := by ring
  rw [e]; exact this

/-- **The regions faced just after and just before a cut** have arcs starting and ending at the
cut. -/
theorem faced_arcs (hM : WalkAx M) {F : Set (Set Point)} (hF : F ⊆ M.Adm) (hfin : F.Finite)
    {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hp1 : t = 0 → 1 ≤ p)
    (hcut : M.IsCut F ((p : ℝ) + t)) {U : Set Point} (hU : U ∈ M.regions F) :
    (AfterFaces M p t U → ∃ r, M.IsArc F U ((p : ℝ) + t) r) ∧
      (BeforeFaces M p t U → ∃ l, M.IsArc F U l ((p : ℝ) + t)) := by
  obtain ⟨c, hc, p', t', hAc, hkey⟩ := hcut
  obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hAc.2.1 hAc.2.2.1 ht0 ht1 hkey.symm
  obtain ⟨U', V', l, r, hU', hV', -, harcU, harcV, -⟩ := hM.attach_face hF hfin hc hAc
  have hne : F.Nonempty := ⟨c, hc⟩
  refine ⟨fun hW => ⟨r, ?_⟩, fun hW => ⟨l, ?_⟩⟩
  · have hW' : AfterFaces M p' t' U' := afterFaces_of_arc harcU hp ht0
      (WalkAx.eventually_after_start (WalkAx.arc_cuts hne harcU).2.2)
    rw [after_unique ht1 hU hU' hW hW']
    exact harcU
  · have hlr := (WalkAx.arc_cuts hne harcV).2.2
    have hW' : BeforeFaces M p' t' V' := by
      rcases ht0.lt_or_eq with htp | ht00
      · exact beforeFaces_of_arc_end' hp htp ht1 harcV hlr
      · subst ht00
        exact beforeFaces_of_arc_end hp (hp1 rfl) harcV hlr
    rw [before_unique ht0 hU hV' hW hW']
    exact harcV

end Facing

/-! ## The local hit -/

section LocalHit

/-- A chord record **matches** the position `x` in the direction of code `d`: its end at `x` (the
left end for `d = 1`, the right end otherwise) has the edge and the height code of `x`. -/
def ChordAt (c : CRec) (x : WPos) (d : ℕ) : Prop :=
  (d = 1 ∧ c.lp = x.edge ∧ c.h + 1 = x.hgt) ∨ (d ≠ 1 ∧ c.rp = x.edge ∧ c.h + 1 = x.hgt)

/-- The far end of a chord record for the direction of code `d`. -/
def farPos (c : CRec) (d : ℕ) : WPos := if d = 1 then c.rpos else c.lpos

variable (C : Chain)

/-- The position `(0, 0)` of a chain model is the top of the slit, outside the box band. -/
theorem key_pos_of_band {Q : Polygon} {x : WPos}
    (hzR : |((chainModel C).pos Q x).2| < C.radius) (h0 : (chainModel C).param Q x = 0) :
    1 ≤ x.edge := by
  by_contra hc
  have hp0 : x.edge = 0 := by omega
  have e : (chainModel C).pos Q x = C.slitTop := by
    show sidePt (chainModel C).W x.edge ((chainModel C).param Q x) = C.slitTop
    rw [hp0, h0, Chazelle.Chain.sidePt_zero]; rfl
  rw [e] at hzR
  simp only [Chain.slitTop] at hzR
  rw [abs_of_pos C.radius_pos] at hzR
  exact lt_irrefl _ hzR

/-- **The local hit** (completeness).  For a walk position `x` of the chain model whose height code
names the height of its point `z`, with the ray in direction `dirOf d` in its left sector, and an
answer `j` of double identification for its key: the direction is free for the chain, and its
exit point lies on the listed arcs of the regions `nbrRegs N j` outside the closed holes (which are
near `z`), or is the far end of an exit chord of one of these regions matching `x`. -/
theorem local_hit_mem (hP : C.P.Simple) {Q : Polygon} (hD : DistinctHeights Q) {N : NF}
    (hN : IsNF (chainModel C) Q N) {x : WPos} {h : ℕ} (hxh : x.hgt = h + 1) (hhn : h < Q.n)
    (hx : x.edge < (chainModel C).W.n) (hx0 : 0 ≤ (chainModel C).param Q x)
    (hx1 : (chainModel C).param Q x < 1) (hyz : (Q.vtx h).2 = ((chainModel C).pos Q x).2)
    {d : ℕ} (hsec : sideLeft (chainModel C).W x.edge ((chainModel C).param Q x)
      (rayPt ((chainModel C).pos Q x) (dirOf d) 1))
    (hzR : |((chainModel C).pos Q x).2| < C.radius) (hzt : ((chainModel C).pos Q x).2 ≤ C.top.2)
    {j : ℕ} (hj : j < N.arcs.length)
    (hloc1 : ¬ (chainModel C).IsCut (N.F (chainModel C) Q) ((chainModel C).key Q x) →
      N.F (chainModel C) Q = ∅ ∨
        sideInArc (sk (chainModel C) Q N j) (ek (chainModel C) Q N j) ((chainModel C).key Q x))
    (hloc2 : (chainModel C).IsCut (N.F (chainModel C) Q) ((chainModel C).key Q x) →
      sk (chainModel C) Q N j = (chainModel C).key Q x ∨
        ek (chainModel C) Q N j = (chainModel C).key Q x)
    {m : ℕ → ℕ} {AB K : ℕ}
    (hlist : ∀ r ∈ nbrRegs N j, ∀ a ∈ (N.region r).arcs, ∃ i < K,
      (chainModel C).key Q (ShotList.arcAt m AB i).1 = (chainModel C).key Q (N.arc a).s ∧
      (chainModel C).key Q (ShotList.arcAt m AB i).2 = (chainModel C).key Q (N.arc a).e)
    {hs : List (WPos × WPos)} (hnear : Restore.Near (chainModel C) Q hs ((chainModel C).pos Q x)) :
    FreeAt C ((chainModel C).pos Q x) (dirOf d) ∧
      (rayPt ((chainModel C).pos Q x) (dirOf d) (C.hitParam ((chainModel C).pos Q x) (dirOf d)) ∈
          ShotList.loSet (chainModel C) Q m AB K hs ∨
        ∃ r ∈ nbrRegs N j, ∃ k ∈ (N.region r).chords, ChordAt (N.chord k) x d ∧
          (chainModel C).pos Q (farPos (N.chord k) d) =
            rayPt ((chainModel C).pos Q x) (dirOf d)
              (C.hitParam ((chainModel C).pos Q x) (dirOf d))) := by
  set M := chainModel C with hMdef
  set F := N.F M Q with hFdef
  set p := x.edge with hpdef
  set t := M.param Q x with htdef
  set z := M.pos Q x with hzdef
  set σ := dirOf d with hσdef
  have hσ : σ = 1 ∨ σ = -1 := dirOf_cases d
  have hGM : GoodModel M := Or.inl ⟨C, hP, rfl⟩
  have hM : WalkAx M := walkAx_of_goodModel hGM
  have hFam : M.ChordFamily Q F := hN.1
  have hF : F ⊆ M.Adm := hFam.2.1
  have hfin : F.Finite := hFam.1
  have hpt : sidePt M.W p t = z := rfl
  have hsec' : sideLeft M.W p t (rayPt (sidePt M.W p t) σ 1) := hsec
  have hfree : FreeAt C z σ := freeAt_of_leave C hP hσ hx hx0 hx1 hpt hsec
  obtain ⟨hT, hwD, hdom⟩ := Merge.hit_of_freeAt C hzt hσ hfree
  set T := C.hitParam z σ with hTdef
  refine ⟨hfree, ?_⟩
  have hkey : M.key Q x = (p : ℝ) + t := rfl
  have hp1 : t = 0 → 1 ≤ p := fun h0 => key_pos_of_band C hzR h0
  obtain ⟨hRC, hCS, hArcs, hRegs, -, hhlt, -⟩ := regOf_spec hN
  -- a region of `nbrRegs` containing the start of the ray gives the exit point on the arcs
  have via_region : ∀ r, r < N.nRegions → r ∈ nbrRegs N j →
      (∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt z σ s ∈ regOf M Q N r) →
      rayPt z σ T ∈ ShotList.loSet M Q m AB K hs := by
    intro r hr hrn hray
    have hU : regOf M Q N r ∈ M.regions F := hRC.1 r hr
    set L := (List.range K).map (fun i => (M.key Q (ShotList.arcAt m AB i).1,
      M.key Q (ShotList.arcAt m AB i).2)) with hLdef
    have hL : ∀ a b, M.IsArc F (regOf M Q N r) a b → (a, b) ∈ L := by
      intro a b harc
      obtain ⟨i₀, hi₀, hir, his, hie⟩ := hArcs.2.2.1 r hr a b harc
      have hmem : i₀ ∈ (N.region r).arcs := (hArcs.2.2.2 r hr i₀).2 ⟨hi₀, hir⟩
      obtain ⟨i, hi, hk1, hk2⟩ := hlist r hrn i₀ hmem
      refine List.mem_map.2 ⟨i, List.mem_range.2 hi, ?_⟩
      simp only [hk1, hk2, his, hie]
    have hFh := firstHit_arcs C hP hFam hU hzt hσ hray L hL
    have hw := hFh.2.1
    simp only [mem_iUnion] at hw
    obtain ⟨ab, hab, hwab⟩ := hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hab
    obtain ⟨p', t', hp', ht0', ht1', hk', hpt'⟩ := (ShotList.arcSet_iff M _ _ _).1 hwab
    refine ⟨p', t', hp', ht0', ht1', ⟨i, List.mem_range.1 hi, hk'⟩, fun g hg hin => ?_, hpt'⟩
    obtain ⟨p'', hp'', ⟨t₁, h₁0, h₁1, h₁⟩, t₂, h₂0, h₂1, h₂⟩ := hnear g hg p' t' hp' ht0' ht1' hin
    exact Restore.no_common_edge hM hσ hT (fun s h0 h1 => hdom s h0 h1) hp'' h₁0 h₁1 h₂0 h₂1 h₁
      (h₂.trans hpt'.symm)
  -- the region of the arc at spine `j` when the key is not a cut
  have noncut : ¬ M.IsCut F ((p : ℝ) + t) → rayPt z σ T ∈ ShotList.loSet M Q m AB K hs := by
    intro hnc
    have hjA : sj N j < N.arcs.length := NFLoc.seq_lt hN hj
    obtain ⟨hr0, harc0⟩ := hArcs.1 (sj N j) hjA
    have hin : sideInArc (sk M Q N j) (ek M Q N j) ((p : ℝ) + t) := by
      rcases hloc1 hnc with hF0 | hin
      · rcases harc0.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, ha, hb⟩
        · rw [← hFdef, hF0] at hc; exact absurd hc (Set.notMem_empty c)
        · have hk0 : (0 : ℝ) < p + t := by
            rcases hx0.lt_or_eq with ht | ht
            · have : (0 : ℝ) ≤ p := Nat.cast_nonneg p
              linarith
            · have := hp1 ht.symm
              have : (1 : ℝ) ≤ p := by exact_mod_cast this
              linarith
          show sideInArc (M.key Q (N.arc (sj N j)).s) (M.key Q (N.arc (sj N j)).e) ((p : ℝ) + t)
          rw [ha, hb]
          unfold sideInArc; rw [ite_eq_right (lt_irrefl _)]; exact Or.inl hk0
      · exact hin
    have hray := ray_mem_region_of_arc hGM hFam (hRC.1 _ hr0) hx hx0 hx1 harc0 hin hσ hsec'
    rw [hpt] at hray
    exact via_region _ hr0 (by simp [nbrRegs]) hray
  rcases leave_cases C hP hFam hσ hx hx0 hx1 hpt hsec hzR with ⟨e, he, hAe, hev⟩ | hnc |
      ⟨ht0, -, hnot, hcr⟩
  · -- along a chord of the family attached at `x`
    right
    have he' : e ∈ Merge.augChords C := hF he
    have hcut : M.IsCut F ((p : ℝ) + t) := ⟨e, he, p, t, hAe, rfl⟩
    have hne : F.Nonempty := ⟨e, he⟩
    obtain ⟨k, hk, hke⟩ := nf_chord_of_mem he
    obtain ⟨y, a, b, hH, -, hey, -, -⟩ := Merge.augChords_spec he'
    have hab := hH.lt
    have hAk := hN.2.2.1 k hk
    obtain ⟨hla, hrb, hky⟩ := rec_pos_ends hAk (hke.trans hey) hab
    have hze : z ∈ hseg y a b := by rw [← hey, ← hpt]; exact hAe.2.2.2.1
    have hzD : z ∉ C.dom := by rw [← hpt]; exact hM.trace p hx t hx0 hx1.le
    obtain ⟨hzy, hza, hzb⟩ := hze
    have hopen : ∀ u : ℝ, a < u → u < b → ((u, y) : Point) ∈ C.dom := fun u h1 h2 => hH.open_mem u h1 h2
    have hzpt : ((z.1, y) : Point) = z := Prod.ext rfl hzy.symm
    -- the side of `z` on the chord, and the first hit
    obtain ⟨hzend, hfar, hdir, hτ⟩ : (σ = 1 ∧ z.1 = a ∨ σ = -1 ∧ z.1 = b) ∧
        ((b, y) : Point) ∉ C.dom ∧ ((a, y) : Point) ∉ C.dom ∧ True := by
      refine ⟨?_, hH.right_not, hH.left_not, trivial⟩
      obtain ⟨s₁, hs₁, hs₁0⟩ := (hev.and self_mem_nhdsWithin).exists
      have hs₁0' : (0 : ℝ) < s₁ := hs₁0
      rw [hey] at hs₁
      obtain ⟨-, hs₁a, hs₁b⟩ := hs₁
      simp only [rayPt_fst] at hs₁a hs₁b
      rcases hσ with hσ1 | hσ1
      · left; refine ⟨hσ1, ?_⟩
        rw [hσ1] at hs₁b
        rcases hza.lt_or_eq with h1 | h1
        · exact absurd (by rw [← hzpt]; exact hopen _ h1 (by linarith)) hzD
        · exact h1.symm
      · right; refine ⟨hσ1, ?_⟩
        rw [hσ1] at hs₁a
        rcases hzb.lt_or_eq with h1 | h1
        · exact absurd (by rw [← hzpt]; exact hopen _ (by linarith) h1) hzD
        · exact h1
    have hd1 : σ = 1 ↔ d = 1 := by
      constructor
      · intro h1; by_contra hd; rw [hσdef] at h1; unfold dirOf at h1; rw [ite_eq_right hd] at h1; norm_num at h1
      · intro h1; rw [hσdef, h1]; rfl
    -- the genuine hit at the far end
    have hT' : T = b - a := by
      rcases hzend with ⟨hσ1, hz1⟩ | ⟨hσ1, hz1⟩
      · have hg : Genuine C z σ (b - a) := genuine_along_chord C he' (by rw [hey]; exact ⟨hzy, hza, hzb⟩)
          hzD hσ (by linarith) (by
            rw [hey]; refine ⟨by simp [rayPt, hzy], ?_, ?_⟩ <;> simp only [rayPt_fst, hσ1, hz1] <;> linarith)
          (by
            have : rayPt z σ (b - a) = ((b, y) : Point) := by
              apply point_ext <;> simp [rayPt, hσ1, hz1, hzy]
            rw [this]; exact hfar)
        exact ((genuine_iff C hzt hσ).1 hg).2
      · have hg : Genuine C z σ (b - a) := genuine_along_chord C he' (by rw [hey]; exact ⟨hzy, hza, hzb⟩)
          hzD hσ (by linarith) (by
            rw [hey]; refine ⟨by simp [rayPt, hzy], ?_, ?_⟩ <;> simp only [rayPt_fst, hσ1, hz1] <;> linarith)
          (by
            have : rayPt z σ (b - a) = ((a, y) : Point) := by
              apply point_ext <;> simp [rayPt, hσ1, hz1, hzy]
            rw [this]; exact hdir)
        exact ((genuine_iff C hzt hσ).1 hg).2
    -- the region on a faced side
    obtain ⟨ρ, U, hρ, hU, hS, hfac⟩ : ∃ ρ U, (ρ = 1 ∨ ρ = -1) ∧ U ∈ M.regions F ∧ SideOf M ρ e U ∧
        FacedSide M p t ρ σ U := by
      have hdir' : (σ = 1 ∧ ∀ z' ∈ e, (sidePt M.W p t).1 ≤ z'.1) ∨
          (σ = -1 ∧ ∀ z' ∈ e, z'.1 ≤ (sidePt M.W p t).1) := by
        rw [hpt, hey]
        rcases hzend with ⟨hσ1, hz1⟩ | ⟨hσ1, hz1⟩
        · exact Or.inl ⟨hσ1, fun z' hz' => by rw [hz1]; exact hz'.2.1⟩
        · exact Or.inr ⟨hσ1, fun z' hz' => by rw [hz1]; exact hz'.2.2⟩
      by_cases huniq : ∀ e' ∈ F, SideAttach M.W e' p t → e' = e
      · obtain ⟨U, hU, hS⟩ := side_region_exists hM hF hfin he (Or.inl rfl : (1 : ℝ) = 1 ∨ _)
        exact ⟨1, U, Or.inl rfl, hU, hS,
          (faced_or_middle hGM hFam he hAe (Or.inl rfl) hU hS hdir').1 huniq⟩
      · push Not at huniq
        obtain ⟨e', he'F, hAe', hne'⟩ := huniq
        obtain ⟨U₁, hU₁, hS₁⟩ := side_region_exists hM hF hfin he (Or.inl rfl : (1 : ℝ) = 1 ∨ _)
        obtain ⟨U₂, hU₂, hS₂⟩ := side_region_exists hM hF hfin he (Or.inr rfl : (-1 : ℝ) = 1 ∨ _)
        have f1 := (faced_or_middle hGM hFam he hAe (Or.inl rfl) hU₁ hS₁ hdir').2 e' he'F hne' hAe'
        have f2 := (faced_or_middle hGM hFam he hAe (Or.inr rfl) hU₂ hS₂ hdir').2 e' he'F hne' hAe'
        obtain ⟨-, hne2, -, h12⟩ := f1
        obtain ⟨-, -, h21, -⟩ := f2
        rcases lt_or_gt_of_ne hne2 with hlt | hlt
        · exact ⟨-1, U₂, Or.inr rfl, hU₂, hS₂, (h21 hlt).2 rfl⟩
        · exact ⟨1, U₁, Or.inl rfl, hU₁, hS₁, (h12 hlt).2 rfl⟩
    -- its arc at the key, its index, and the chord in its exit list
    obtain ⟨hfa, hfb⟩ := faced_arcs hM hF hfin hx hx0 hx1 hp1 hcut hU
    obtain ⟨rU, hrU, hrUe⟩ := regOf_surj hN hU
    have hmem : rU ∈ nbrRegs N j := by
      have hρσ : ρ * σ = -1 ∨ ρ * σ = 1 := by
        rcases hρ with rfl | rfl <;> rcases hσ with h | h <;> rw [h] <;> norm_num
      rcases hρσ with h | h
      · obtain ⟨r', harc⟩ := hfa (hfac.1 h)
        rw [← hrUe] at harc
        exact region_of_arc_at hN hGM hne hj (hloc2 hcut) hrU harc (Or.inl rfl)
      · obtain ⟨l', harc⟩ := hfb (hfac.2 h)
        rw [← hrUe] at harc
        exact region_of_arc_at hN hGM hne hj (hloc2 hcut) hrU harc (Or.inr rfl)
    have htouch : TouchesIn M.D e U := touchesIn_of_sideOf hM (hF he) hAe hS
    have hkr : k ∈ (N.region rU).chords := by
      refine ((hRegs rU hrU).1 k).2 ⟨hk, ?_⟩
      rw [hke, hrUe]; exact htouch
    -- the height index and the attachment edge
    have hkh : (N.chord k).h = h := by
      by_contra hne'
      exact hD _ _ (hhlt k hk) hhn hne' (hky.trans (hzy.symm.trans hyz.symm))
    have hAk1 := hAk.1
    rw [hke] at hAk1
    have hAk2 := hAk.2
    rw [hke] at hAk2
    refine ⟨rU, hmem, k, hkr, ?_⟩
    rcases hzend with ⟨hσ1, hz1⟩ | ⟨hσ1, hz1⟩
    · have hd : d = 1 := hd1.1 hσ1
      have hlp : (N.chord k).lp = p := (hM.attach_unique (hF he) hAk1 hAe (by
        show M.pos Q (N.chord k).lpos = sidePt M.W p t
        rw [hla, hpt]; exact Prod.ext hz1.symm hzy.symm)).1
      refine ⟨Or.inl ⟨hd, hlp, by rw [hkh, hxh]⟩, ?_⟩
      simp only [farPos, ite_eq_left hd]
      rw [hrb, hT']
      apply point_ext <;> simp [rayPt, hσ1, hz1, hzy]
    · have hd : d ≠ 1 := fun h' => by rw [hd1.2 h'] at hσ1; norm_num at hσ1
      have hrp : (N.chord k).rp = p := (hM.attach_unique (hF he) hAk2 hAe (by
        show M.pos Q (N.chord k).rpos = sidePt M.W p t
        rw [hrb, hpt]; exact Prod.ext hz1.symm hzy.symm)).1
      refine ⟨Or.inr ⟨hd, hrp, by rw [hkh, hxh]⟩, ?_⟩
      simp only [farPos, ite_eq_right hd]
      rw [hla, hT']
      apply point_ext <;> simp [rayPt, hσ1, hz1, hzy]
  · exact Or.inl (noncut hnc)
  · -- a cut walk vertex: the region faced just after or just before
    left
    by_cases hcut : M.IsCut F ((p : ℝ) + t)
    · have hcut' := hcut
      obtain ⟨c, hc, p', t', hAc, hk'⟩ := hcut'
      obtain ⟨rfl, rfl⟩ := Chazelle.Chain.sideKey_inj hAc.2.1 hAc.2.2.1 hx0 hx1 hk'.symm
      have hne : F.Nonempty := ⟨c, hc⟩
      obtain ⟨U, V, l, r, hU, hV, -, harcU, harcV, -⟩ := hM.attach_face hF hfin hc hAc
      have hp1' : 1 ≤ p := hp1 ht0
      rw [ht0] at hAc harcU harcV
      have hpt0 : sidePt M.W p 0 = z := by rw [← ht0]; exact hpt
      have hsec0 : sideLeft M.W p 0 (rayPt (sidePt M.W p 0) σ 1) := by rw [← ht0]; exact hsec'
      have hnot' : ∀ c ∈ F, SideAttach M.W c p 0 →
          ∀ᶠ s in 𝓝[>] (0 : ℝ), rayPt (sidePt M.W p 0) σ s ∉ c := by
        intro c hc hA; rw [hpt0]; exact hnot c hc hA
      have hloc := hloc2 hcut
      rw [hkey, ht0] at hloc
      rcases hcr with hcr | hcr
      · have hray := ray_mem_region_after hGM hFam hU hx harcU hc hAc hσ hsec0 hnot' hcr
        rw [hpt0] at hray
        obtain ⟨rU, hrU, rfl⟩ := regOf_surj hN hU
        exact via_region rU hrU (region_of_arc_at hN hGM hne hj hloc hrU harcU (Or.inl rfl)) hray
      · have hray := ray_mem_region_before hGM hFam hV hx hp1' harcV hc hAc hσ hsec0 hnot' hcr
        rw [hpt0] at hray
        obtain ⟨rV, hrV, rfl⟩ := regOf_surj hN hV
        exact via_region rV hrV (region_of_arc_at hN hGM hne hj hloc hrV harcV (Or.inr rfl)) hray
    · exact noncut hcut

end LocalHit

end Sweep

end

end Chazelle.Core
