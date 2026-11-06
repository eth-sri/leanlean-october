module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIface

/-!
# The sweep (WP-D), answers: side-generic lemmas, candidates, records from arrival positions

The answer stage of the sweep computes, for every query point `z` and direction `σ`, a set of
**candidate hits** (shots at arc lists in the models of `C₁` and `C₂`, chord ends read from the
records, stop and table chords) and answers the earliest one.  This file collects the
side-generic facts the answer lemmas share.

* `sideChain_one`, `seesInWhole_hit`, `seesInWhole_notFree'`: `SeesInWhole` for either side,
  from the first hit of `C` and the record data (`RecordData`), or for a direction that is not
  free.
* `whole_firstHit_of_mem` (**the candidate principle**): a set of points of the ray, each off the
  domain of `C`, `C₁` or `C₂` (below the respective top), containing the exit point of `C`, has
  its first hit at the exit point.
* `whole_of_genuine_above₁`: above the top of `C₁` the first hit of `C` is the one of `C₂`.
* `recordData_of_arrival`: the record of the chord of `C` seen from `z` from the arrival
  positions of its two ends in the walk of `C` (any height code at the right height).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideLeft sidePrev sideNext sideLeftOf sideCcw sideCross
  sideDot)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace Sweep

section Gen

variable (J : Merge.Junction)

section
variable (Q : Polygon) (i : ℕ) (q : ℕ × ℕ × ℕ) {z : Point} {σ : ℝ} (hzq : (chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩ = z) (hσq : dirOf q.2.2 = σ)
include hzq hσq
/-- **Answer of a free direction, either side**: flag `1`, the first hit parameter `T` of `C`, and
the record data. -/
theorem seesInWhole_hit
    (hzt : z.2 ≤ J.whole.top.2) {T : ℝ} (hhit : FreeAt J.whole z σ ∧ J.whole.hitParam z σ = T)
    {h pz pw lp rp : ℕ} (hR : RecordData J Q z σ T h pz pw lp rp) :
    SeesInWhole J Q i q (1, h, lp, rp) := by
  obtain ⟨hh, hz, hw, hAz, hAw, hl, hr⟩ := hR
  have hσ : σ = 1 ∨ σ = -1 := hσq ▸ dirOf_cases q.2.2
  obtain ⟨hT0, -, -⟩ := Merge.hit_of_freeAt J.whole hzt hσ hhit.1
  rw [hhit.2] at hT0
  obtain ⟨hs, hat⟩ := record_ok (chainModel J.whole) Q hσ hT0 hh hz hw hAz hAw ⟨hl, hr⟩
  refine seesInWhole_of_answer J Q i q _ ?_ ?_ <;> simp_all
  simp_all [Merge.shoot] 

/-- **Answer of a direction that is not free, either side**: any flag other than `1`. -/
theorem seesInWhole_notFree'
    (hnf : ¬ FreeAt J.whole z σ) (r : ℕ × ℕ × ℕ × ℕ) (hr : r.1 ≠ 1) : SeesInWhole J Q i q r := by
  core_grind

/-! ## The candidate principle -/


end

/-- **The first hit of `C` above the top of `C₁`** is the first hit of `C₂`. -/
theorem whole_of_genuine_above₁ {z : Point} (hz₂ : z.2 ≤ J.right.top.2)
    (hz₁ : J.left.top.2 < z.2) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {τ₂ : ℝ}
    (h₂ : Genuine J.right z σ τ₂) : FreeAt J.whole z σ ∧ J.whole.hitParam z σ = τ₂ := by
  obtain ⟨hf₂, he₂⟩ := (genuine_iff J.right hz₂ hσ).1 h₂
  refine ⟨?_, ?_⟩
  · rw [freeAt_whole_iff J (hz₂.trans J.right_top_le)]
    filter_upwards [hf₂] with t ht2
    refine ⟨J.right.dom_subset_box ht2, fun hmem => ?_, J.right.not_mem_set_of_mem_dom ht2⟩
    have := J.left.snd_le_top_of_mem_set hmem
    grind [rayPt_snd]
  · have e : J.whole.hitParam z σ = J.right.hitParam z σ := by
      rw [whole_hitParam_eq_min J (hz₂.trans J.right_top_le) hσ,
        rayHit_eq_empty_of_above J.left hz₁, right_hitParam_eq J hz₂]
      refine min_eq_right ?_
      rw [← right_hitParam_eq J hz₂]
      exact Merge.rayHit_anti (empty_subset _) z hσ
    rw [e, he₂]

end Gen

/-! ## Records from arrival positions -/

section Record

/-- **No horizontal ray in the left sector inside a horizontal edge.** -/
theorem not_sideLeft_horizontal {W : Polygon} {p : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hh : (W.vtx p).2 = (W.vtx ((p + 1) % W.n)).2) (σ : ℝ) :
    ¬ sideLeft W p t (rayPt (sidePt W p t) σ 1) := by
  intro hs
  unfold sideLeft sideLeftOf at hs
  have hprev : sidePrev W p t = W.vtx p := by unfold sidePrev; rw [ite_eq_right ht0.ne']
  rw [hprev] at hs
  set a := W.vtx p with ha
  set b := sideNext W p with hb
  have hb' : b = W.vtx ((p + 1) % W.n) := rfl
  set v := sidePt W p t with hv
  have hv1 : v.1 = a.1 + t * (b.1 - a.1) := by rw [hv, hb']; rfl
  have hv2 : v.2 = a.2 := by
    rw [hv]; show a.2 + t * ((W.vtx ((p + 1) % W.n)).2 - a.2) = a.2; simp_all
  
  have eB1 : (b - v).1 = (1 - t) * (b.1 - a.1) := by simp only [Prod.fst_sub]; grind
  have eB2 : (b - v).2 = 0 := by simp_all
  have eA1 : (a - v).1 = -t * (b.1 - a.1) := by simp_all
  have eA2 : (a - v).2 = 0 := by simp_all
  
  have hBA : sideCross (b - v) (a - v) = 0 := by simp_all [sideCross] 
  have hBX : sideCross (b - v) (rayPt v σ 1 - v) = 0 := by simp_all [sideCross] 
  have hdot : sideDot (b - v) (a - v) ≤ 0 := by
    unfold sideDot; rw [eB1, eB2, eA1, eA2]
    have h1 : 0 ≤ (1 - t) * t := mul_nonneg (by linarith) ht0.le
    nlinarith [sq_nonneg (b.1 - a.1)]
  unfold sideCcw at hs
  grind

variable {M : Model}

section
variable (Q : Polygon) {p : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {h : ℕ} (hy : (Q.vtx h).2 = (sidePt M.W p t).2) {σ : ℝ} (hsec : sideLeft M.W p t (rayPt (sidePt M.W p t) σ 1))
include ht0 ht1 hy σ hsec
/-- **The height code of a point**: at a position `(p, t)` whose point has the height of vertex
`h` of `Q`, the position with the height code `h + 1` on edge `p` is the same position (inside a
horizontal edge only the start vertex has a horizontal ray in its left sector). -/
theorem param_of_arrival :
    M.param Q ⟨p, h + 1⟩ = t := by
  by_cases hh : (M.wa p).2 = (M.wb p).2
  · have ht : t = 0 := by
      by_contra hne
      exact not_sideLeft_horizontal (lt_of_le_of_ne ht0 (Ne.symm hne)) ht1 hh σ hsec
    simp_all [Model.param] 
  · unfold Model.param
    simp only
    rw [ite_eq_right hh, hy]
    have : (M.wb p).2 - (M.wa p).2 ≠ 0 := sub_ne_zero.2 (Ne.symm hh)
    have e : (sidePt M.W p t).2 = (M.wa p).2 + t * ((M.wb p).2 - (M.wa p).2) := rfl
    simp_all

theorem pos_of_arrival :
    M.pos Q ⟨p, h + 1⟩ = sidePt M.W p t := by
  unfold Model.pos
  rw [param_of_arrival Q ht0 ht1 hy hsec]
  rfl


end

end Record

section RecordJ

variable (J : Merge.Junction)

/-- **The record of a chord of `C` from the arrival positions of its ends**: `(pz, tz)` a position
of the query point `z` whose left sector contains the ray, `(pw, tw)` an arrival position of the
hit point `w = rayPt z σ T`, `h` a vertex of `Q` at the height of `z`. -/
theorem recordData_of_arrival (Q : Polygon) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {T : ℝ}
    (hT : 0 < T) {h : ℕ} (hh : (Q.vtx h).2 = z.2) {pz pw : ℕ} {tz tw : ℝ}
    (hAz : Arrival (chainModel J.whole).W z (-σ) pz tz)
    (hAw : Arrival (chainModel J.whole).W (rayPt z σ T) σ pw tw) :
    RecordData J Q z σ T h pz pw (if σ = 1 then pz else pw) (if σ = 1 then pw else pz) := by
  set M := chainModel J.whole
  have hnσ : -σ = 1 ∨ -σ = -1 := by grind
  obtain ⟨hpz, htz0, htz1, hptz, hsecz⟩ := hAz
  obtain ⟨hpw, htw0, htw1, hptw, hsecw⟩ := hAw
  rw [neg_neg] at hsecz
  have hsz : sideLeft M.W pz tz (rayPt (sidePt M.W pz tz) σ 1) := by simp_all
  have hsw : sideLeft M.W pw tw (rayPt (sidePt M.W pw tw) (-σ) 1) := by simp_all
  have hyz : (Q.vtx h).2 = (sidePt M.W pz tz).2 := by simp_all
  have hyw : (Q.vtx h).2 = (sidePt M.W pw tw).2 := by simp_all
  have ez := param_of_arrival Q htz0 htz1 hyz hsz
  have ew := param_of_arrival Q htw0 htw1 hyw hsw
  -- the attachments
  have hw' : rayPt (rayPt z σ T) (-σ) T = z := by
    simp_all [rayPt] 
  have hAz' : Arrival M.W (rayPt (rayPt z σ T) (-σ) T) (-σ) pz tz := by
    grind [Chazelle.Core.Sweep.Arrival, neg_neg]
  have att_z := attach_left_of_arrival hnσ hT hAz'
  rw [hw', Geometry.segment_comm] at att_z
  have att_w := attach_left_of_arrival hσ hT ⟨hpw, htw0, htw1, hptw, hsecw⟩
  refine ⟨hh, ?_, ?_, ?_, ?_, fun h1 => ?_, fun h1 => ?_⟩
  · rw [pos_of_arrival Q htz0 htz1 hyz hsz, hptz]
  · rw [pos_of_arrival Q htw0 htw1 hyw hsw, hptw]
  all_goals grind

end RecordJ

end Sweep

end

end Chazelle.Core
