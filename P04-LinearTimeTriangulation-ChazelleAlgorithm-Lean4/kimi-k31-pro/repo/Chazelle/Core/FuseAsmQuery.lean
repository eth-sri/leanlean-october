module

public import Chazelle.Core.SweepLocal
public import Chazelle.Core.GranNF
public import Chazelle.Core.SpecMerge
public import Chazelle.Core.SweepQuery
public import Chazelle.Core.SweepDetect2
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# WP-F fusion assembly, part 1: the chord-end queries

The fusion asks the sweep, for every chord record `(h, lp, rp)` of the normal form of side `i`,
the queries `(lp, h + 1, 1)` (the left end, direction `+1`) and `(rp, h + 1, 0)` (the right end,
direction `-1`).  They are valid sweep queries (`QueryOK`) and their points are the ends of the
chord (`queryOK_ends`): the record is attached (its ends are proper positions whose left sectors
the chord enters) and admissible (`augChords`: at a height `≤` the top of the chain).
-/

namespace Chazelle.Core

namespace FuseAsm

@[expose] public section

open Chazelle.Chain (SideAttach sidePt sideLeft)
open Chazelle.Visibility (rayPt hseg)
open Chazelle.Merge (lend rend lend_hseg rend_hseg hseg_inj)

/-- The point `(z.1 + σ, z.2)` is the ray point at parameter `1`. -/
theorem ray_one (z : Point) (σ : ℝ) : ((z.1 + σ, z.2) : Point) = rayPt z σ 1 := by
  simp [rayPt]

/-- **The chord-end queries.** -/
theorem queryOK_ends (J : Merge.Junction) (Q : Polygon) (i : ℕ) (r : CRec)
    (hA : r.Attached (chainModel (sideChain J i)) Q)
    (hadm : r.toSet (chainModel (sideChain J i)) Q ∈ (chainModel (sideChain J i)).Adm)
    (hh : r.h < Q.n) :
    QueryOK J Q i (r.lp, r.h + 1, 1) ∧ QueryOK J Q i (r.rp, r.h + 1, 0) ∧
      (chainModel (sideChain J i)).pos Q r.lpos = lend (r.toSet (chainModel (sideChain J i)) Q) ∧
      (chainModel (sideChain J i)).pos Q r.rpos = rend (r.toSet (chainModel (sideChain J i)) Q) := by
  set C := sideChain J i
  set M := chainModel C
  obtain ⟨y, a, b, hIH, hytop, hc⟩ := hadm
  have hab : a < b := hIH.lt
  have hdef : r.toSet M Q = hseg (Q.vtx r.h).2 (M.pos Q r.lpos).1 (M.pos Q r.rpos).1 := rfl
  obtain ⟨⟨hpl, htl0, htl1, hml, rl, hrl, hsl⟩, ⟨hpr, htr0, htr1, hmr, rr, hrr, hsr⟩⟩ := hA
  have el : M.pos Q r.lpos = sidePt M.W r.lp (M.param Q r.lpos) := rfl
  have er : M.pos Q r.rpos = sidePt M.W r.rp (M.param Q r.rpos) := rfl
  rw [← el] at hml hsl
  rw [← er] at hmr hsr
  have hml' := hml
  rw [hdef] at hml'
  obtain ⟨-, -, hlr⟩ := hml'
  obtain ⟨-, ha, hb⟩ := hseg_inj hlr (hdef.symm.trans hc)
  -- the end points
  have pl : M.pos Q r.lpos = (a, y) := by
    rw [hc] at hml
    exact Prod.ext (ha) hml.1
  have pr : M.pos Q r.rpos = (b, y) := by
    rw [hc] at hmr
    exact Prod.ext (hb) hmr.1
  have hL : lend (r.toSet M Q) = (a, y) := by rw [hc, lend_hseg hab.le]
  have hR : rend (r.toSet M Q) = (b, y) := by rw [hc, rend_hseg hab.le]
  -- the sectors
  have secL : sideLeft M.W r.lp (M.param Q r.lpos) (rayPt (M.pos Q r.lpos) 1 1) := by
    set s := min (rl / 2) ((b - a) / 2)
    have hs : 0 < s := lt_min (by linarith) (by linarith)
    have hx : rayPt (M.pos Q r.lpos) 1 s ∈ r.toSet M Q := by
      rw [hc, pl]; refine ⟨rfl, ?_, ?_⟩ <;> simp [rayPt] <;>
        (have := min_le_right (rl / 2) ((b - a) / 2); linarith)
    have hne : rayPt (M.pos Q r.lpos) 1 s ≠ M.pos Q r.lpos := by
      intro h; have := congrArg Prod.fst h; sil [rayPt] at this
    have hd : dist (rayPt (M.pos Q r.lpos) 1 s) (M.pos Q r.lpos) < rl := by
      rw [Prod.dist_eq]; simp [rayPt, abs_of_pos hs]
      have := min_le_left (rl / 2) ((b - a) / 2); constructor <;> linarith
    have h := hsl _ hx hne hd
    rw [el] at h ⊢
    exact (Sweep.sideLeft_rayPt_iff _ _ _ 1 hs one_pos).1 h
  have secR : sideLeft M.W r.rp (M.param Q r.rpos) (rayPt (M.pos Q r.rpos) (-1) 1) := by
    set s := min (rr / 2) ((b - a) / 2)
    have hs : 0 < s := lt_min (by linarith) (by linarith)
    have hx : rayPt (M.pos Q r.rpos) (-1) s ∈ r.toSet M Q := by
      rw [hc, pr]; refine ⟨rfl, ?_, ?_⟩ <;> simp [rayPt] <;>
        (have := min_le_right (rr / 2) ((b - a) / 2); linarith)
    have hne : rayPt (M.pos Q r.rpos) (-1) s ≠ M.pos Q r.rpos := by
      intro h; have := congrArg Prod.fst h; sil [rayPt] at this
    have hd : dist (rayPt (M.pos Q r.rpos) (-1) s) (M.pos Q r.rpos) < rr := by
      rw [Prod.dist_eq]; simp [rayPt, abs_of_pos hs]
      have := min_le_left (rr / 2) ((b - a) / 2); constructor <;> linarith
    have h := hsr _ hx hne hd
    rw [er] at h ⊢
    exact (Sweep.sideLeft_rayPt_iff _ _ _ (-1) hs one_pos).1 h
  refine ⟨⟨hpl, by show 1 ≤ r.h + 1; omega, by show r.h + 1 ≤ Q.n; omega, htl0, htl1, ?_, ?_⟩,
    ⟨hpr, by show 1 ≤ r.h + 1; omega, by show r.h + 1 ≤ Q.n; omega, htr0, htr1, ?_, ?_⟩,
    by rw [pl, hL], by rw [pr, hR]⟩
  · show (M.pos Q r.lpos).2 ≤ C.top.2
    rwx [pl]
  · show sideLeft M.W r.lp (M.param Q r.lpos) ((M.pos Q r.lpos).1 + dirOf 1, (M.pos Q r.lpos).2)
    rw [ray_one]; simpa [dirOf] using secL
  · show (M.pos Q r.rpos).2 ≤ C.top.2
    rwx [pr]
  · show sideLeft M.W r.rp (M.param Q r.rpos) ((M.pos Q r.rpos).1 + dirOf 0, (M.pos Q r.rpos).2)
    rw [ray_one]; simpa [dirOf] using secR

/-- **Equal chords have equal records** (for attached records of a model with the walk axioms and
a height polygon with distinct vertex heights): the heights fix `h`, the ends fix the points of
the positions, and an admissible chord is attached at most once at each of its points
(`WalkAx.attach_unique`).  So removing duplicate triples removes duplicate chords. -/
theorem rec_eq_of_toSet {M : Model} (hM : WalkAx M) {Q : Polygon} (hQ : DistinctHeights Q)
    {r r' : CRec} (hA : r.Attached M Q) (hA' : r'.Attached M Q) (hadm : r.toSet M Q ∈ M.Adm)
    (hh : r.h < Q.n) (hh' : r'.h < Q.n) (he : r.toSet M Q = r'.toSet M Q) :
    r.h = r'.h ∧ r.lp = r'.lp ∧ r.rp = r'.rp := by
  have hne : (M.pos Q r.lpos).1 ≤ (M.pos Q r.rpos).1 := by
    obtain ⟨⟨-, -, -, hml, -⟩, -⟩ := hA
    exact hml.2.1.trans hml.2.2
  obtain ⟨hy, hl, hr⟩ := hseg_inj hne he
  have hml := hA.1.2.2.2.1
  have hml' := hA'.1.2.2.2.1
  have hmr := hA.2.2.2.2.1
  have hmr' := hA'.2.2.2.2.1
  have el : ∀ (s : CRec), M.pos Q s.lpos = sidePt M.W s.lp (M.param Q s.lpos) := fun _ => rfl
  have er : ∀ (s : CRec), M.pos Q s.rpos = sidePt M.W s.rp (M.param Q s.rpos) := fun _ => rfl
  have pyl : (M.pos Q r.lpos).2 = (Q.vtx r.h).2 := by rw [el]; exact hml.1
  have pyl' : (M.pos Q r'.lpos).2 = (Q.vtx r'.h).2 := by rw [el]; exact hml'.1
  have pyr : (M.pos Q r.rpos).2 = (Q.vtx r.h).2 := by rw [er]; exact hmr.1
  have pyr' : (M.pos Q r'.rpos).2 = (Q.vtx r'.h).2 := by rw [er]; exact hmr'.1
  have hhh : r.h = r'.h := by
    by_contra hne'; exact hQ _ _ hh hh' hne' hy
  have ptl : sidePt M.W r.lp (M.param Q r.lpos) = sidePt M.W r'.lp (M.param Q r'.lpos) := by
    rw [← el, ← el]; exact Prod.ext hl (by rw [pyl, pyl', hhh])
  have ptr : sidePt M.W r.rp (M.param Q r.rpos) = sidePt M.W r'.rp (M.param Q r'.rpos) := by
    rw [← er, ← er]; exact Prod.ext hr (by rw [pyr, pyr', hhh])
  have hA'l  := he ▸ hA'.1
  have hA'r  := he ▸ hA'.2
  exact ⟨hhh, (hM.attach_unique hadm hA.1 hA'l ptl).1, (hM.attach_unique hadm hA.2 hA'r ptr).1⟩

/-- The side chains share the ambient polygon of the junction. -/
theorem sideChain_P (J : Merge.Junction) (i : ℕ) : (sideChain J i).P = J.P := by
  unfold sideChain; split_ifs <;> rfl

/-- The domain of `C` at heights `≤ top(Cᵢ)` lies in the domain of `Cᵢ`. -/
theorem dom_side (J : Merge.Junction) (i : ℕ) {x : Point} (hx : x ∈ J.whole.dom)
    (hx2 : x.2 ≤ (sideChain J i).top.2) : x ∈ (sideChain J i).dom := by
  unfold sideChain at hx2 ⊢
  split_ifs at hx2 ⊢
  · exact Sweep.dom_left J hx hx2
  · exact Sweep.dom_right J hx hx2

theorem lerp_rayPt (z : Point) (σ T s : ℝ) :
    Geometry.lerp z (rayPt z σ T) s = rayPt z σ (s * T) := by
  apply Geometry.point_ext <;> simp [Geometry.lerp, rayPt]; ring

/-- **A free direction at a point of `Cᵢ` has a departure position** in the walk of `Cᵢ`
(`arrivalPos` finds it): some position at the point has the direction in its left sector. -/
theorem arrival_of_free (J : Merge.Junction) (hP : J.P.Simple) (i : ℕ) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hz : z ∈ (sideChain J i).set) (hz2 : z.2 ≤ (sideChain J i).top.2)
    (hf : Merge.FreeAt J.whole z σ) :
    ∃ p t, Sweep.Arrival (chainModel (sideChain J i)).W z (-σ) p t := by
  set C := sideChain J i
  have hPC : C.P.Simple := by rwx [sideChain_P]
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hf
  have hu0 : (0 : ℝ) < u := hu
  set T := u / 2
  have hT : 0 < T := by positivity
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hee : z ≠ rayPt z σ T := by
    intro h
    have h' := congrArg Prod.fst h
    simp only [rayPt] at h'
    have hm0 : σ * T = 0 := by linarith
    rcases mul_eq_zero.1 hm0 with h1 | h1
    · exact hσ0 h1
    · linarith
  have hopen : ∀ s ∈ Set.Ioo (0 : ℝ) 1, Geometry.lerp z (rayPt z σ T) s ∈ C.dom := by
    intro s hs
    rw [lerp_rayPt]
    have hTu : T = u / 2 := rfl
    have hm : rayPt z σ (s * T) ∈ J.whole.dom := hsub ⟨mul_pos hs.1 hT, by
      have := hs.2; rwnl [hTu]⟩
    exact dom_side J i hm (by simpa [rayPt] using hz2)
  obtain ⟨p, t, hp, ht0, ht1, hpt, hl⟩ :=
    C.sideSees_chordEnd hPC C.sideBeta hee (by simp [rayPt]) hopen (Or.inl hz)
  have hpt' : sidePt (chainModel C).W p t = z := hpt
  have hl' : sideLeft (chainModel C).W p t (rayPt z σ T) := hl
  refine ⟨p, t, hp, ht0, ht1, hpt', ?_⟩
  rw [neg_neg]
  have h1 : sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) σ T) := by
    rwx [hpt']
  have := (Sweep.sideLeft_rayPt_iff _ p t σ hT one_pos).1 h1
  rwa [hpt'] at this

/-! ## Queries at points found by `arrivalPos` -/

/-- The parameter of the height code of the start vertex of a walk edge is `0`. -/
theorem param_of_vertex (M : Model) (Q : Polygon) (p h : ℕ) (hy : (Q.vtx h).2 = (M.wa p).2) :
    M.param Q ⟨p, h + 1⟩ = 0 := by
  unfold Model.param
  simp only
  split_ifs
  · rfl
  · rw [hy, sub_self, zero_div]

/-- **A query from a departure position**: a position with the direction `dirOf ρ` in its left
sector (`Sweep.Arrival` for `-dirOf ρ`, as `arrivalPos` reports it), written with the height code
`h + 1` of the point, is a valid sweep query at that point. -/
theorem queryOK_of_arrival (J : Merge.Junction) (Q : Polygon) (i : ℕ) {p h ρ : ℕ} {z : Point}
    {t : ℝ} (hA : Sweep.Arrival (chainModel (sideChain J i)).W z (-dirOf ρ) p t)
    (hpar : (chainModel (sideChain J i)).param Q ⟨p, h + 1⟩ = t) (hh : h + 1 ≤ Q.n)
    (hz2 : z.2 ≤ (sideChain J i).top.2) :
    QueryOK J Q i (p, h + 1, ρ) ∧ (chainModel (sideChain J i)).pos Q ⟨p, h + 1⟩ = z := by
  obtain ⟨hp, ht0, ht1, hpt, hl⟩ := hA
  have hpos : (chainModel (sideChain J i)).pos Q ⟨p, h + 1⟩ = z := by
    rw [Gran.pos_eq_sidePt]; simp only; rw [hpar, hpt]
  refine ⟨⟨hp, by show 1 ≤ h + 1; omega, hh, by simp only; rwx [hpar], by simp only; rwx [hpar],
    by simp only; rwx [hpos], ?_⟩, hpos⟩
  simp only
  rw [hpos, hpar, ray_one]
  simpa using hl

end

end FuseAsm

end Chazelle.Core
