module

public import Chazelle.Core.SweepMachine10

/-!
# The sweep (WP-D), part 27: the abstract machine, the answer record of a query

`SeesInWhole` asks for the flag `1` iff the direction is free for `C`, and then for the record
`(h, lp, rp)` of the chord of `C` seen from the query point: its height index and the walk edges
of `C` at its two ends, with the height code `h + 1`, attached there.

* `record_ok`: from the first hit `T` of `C` and positions of `C` at the query point and at the hit
  point (with height code `h + 1`) at which the chord is attached, the record is the chord seen
  and is correctly attached.
* `seesInWhole_of_answer`: the flag and the record give `SeesInWhole`.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideCross freeIn regionsIn)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd hseg)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)

namespace Sweep

/-- **The answer record**: `z` the query point, `w = rayPt z σ T` the first hit, `h` a vertex of
`Q` at the height of `z`, `pz`, `pw` walk edges of the model `M` whose positions at the height code
`h + 1` are `z` and `w` and at which the segment `[z, w]` is attached; `lp` the edge at the left end,
`rp` at the right end. -/
theorem record_ok (M : Model) (Q : Polygon) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {T : ℝ}
    (hT : 0 < T) {h : ℕ} (hh : (Q.vtx h).2 = z.2) {pz pw lp rp : ℕ}
    (hz : M.pos Q ⟨pz, h + 1⟩ = z) (hw : M.pos Q ⟨pw, h + 1⟩ = rayPt z σ T)
    (hAz : SideAttach M.W (Chazelle.segment z (rayPt z σ T)) pz (M.param Q ⟨pz, h + 1⟩))
    (hAw : SideAttach M.W (Chazelle.segment z (rayPt z σ T)) pw (M.param Q ⟨pw, h + 1⟩))
    (hlr : (σ = 1 → lp = pz ∧ rp = pw) ∧ (σ = -1 → lp = pw ∧ rp = pz)) :
    (recOf (h, lp, rp)).toSet M Q = Chazelle.segment z (rayPt z σ T) ∧
      (recOf (h, lp, rp)).Attached M Q := by
  have hwpt : rayPt z σ T = ((z.1 + σ * T, z.2) : Point) :=
    point_ext (by simp [rayPt]) (by simp [rayPt])
  rcases hσ with rfl | rfl
  · obtain ⟨rfl, rfl⟩ := hlr.1 rfl
    have hset : (recOf (h, lp, rp)).toSet M Q = Chazelle.segment z (rayPt z 1 T) := by
      unfold CRec.toSet recOf CRec.lpos CRec.rpos
      simp only
      rw [hz, hw, hwpt, hh, FactsChain.hseg_eq_segment (by linarith)]
    refine ⟨hset, ?_, ?_⟩
    · rwa [hset]
    · rwa [hset]
  · obtain ⟨rfl, rfl⟩ := hlr.2 rfl
    have hset : (recOf (h, lp, rp)).toSet M Q = Chazelle.segment z (rayPt z (-1) T) := by
      unfold CRec.toSet recOf CRec.lpos CRec.rpos
      simp only
      rw [hz, hw, hwpt, hh, FactsChain.hseg_eq_segment (by linarith), Geometry.segment_comm]
    refine ⟨hset, ?_, ?_⟩
    · rwa [hset]
    · rwa [hset]

/-- **`SeesInWhole` from the answer**: the flag is `1` iff the direction is free for `C`, and when it
is, the record is the one of `record_ok` at the first hit of `C`. -/
theorem seesInWhole_of_answer (J : Merge.Junction) (Q : Polygon) (i : ℕ) (q : ℕ × ℕ × ℕ)
    (r : ℕ × ℕ × ℕ × ℕ)
    (hflag : r.1 = 1 ↔ FreeAt J.whole ((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩)
      (dirOf q.2.2))
    (hrec : r.1 = 1 → (recOf r.2).toSet (chainModel J.whole) Q =
        Merge.shoot J.whole ((chainModel (sideChain J i)).pos Q ⟨q.1, q.2.1⟩) (dirOf q.2.2) ∧
      (recOf r.2).Attached (chainModel J.whole) Q) :
    SeesInWhole J Q i q r :=
  ⟨hflag, hrec⟩

end Sweep

end

end Chazelle.Core
