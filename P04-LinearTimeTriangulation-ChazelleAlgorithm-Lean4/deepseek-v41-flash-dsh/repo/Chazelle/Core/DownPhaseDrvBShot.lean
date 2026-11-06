module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvBGeo
public import Chazelle.Core.DownPhaseBaseFull
public import Chazelle.Core.DownPhaseMathHost

/-!
# Down-phase base (D9), geometry part 2: the far end of a vertex chord, and its record

The base case shoots from a vertex `v_i` of `Q` in a direction `σ = ±1` entering the interior.
The far end `z = chordEnd Q i σ` of the vertex chord is found by a scan over a set of edges of
`Q` that contains the edge carrying `z`: a **candidate** edge `q` straddles the height of `v_i`
strictly and crosses it strictly on the side `σ` (`Cand`), at the symbolic point `.onEdge q i`.

* `cand_le`: every candidate crossing is on `∂Q`, hence not strictly before `z` (the open chord is
  interior);
* `far_cand`: `z` lies in the open part of an edge `q*` of `Q`, which is a candidate crossing
  at `z` (distinct heights);
* `cand_min`: a candidate that is not after `z` crosses at `z`, in the open part of its edge;
  **`scan_min`**: a σ-nearest candidate among a set of walk edges containing the walk edge of `z`
  carries `z`.

The record of the chord (`vtrip`): the height vertex `i`, the walk edge `ivB i` starting at the
vertex, and the walk edge `w` carrying `z`, in the order (left end, right end).  **`vtrip_ok`**:
the record describes the chord, is attached at both ends (`WalkAx.ends` and the uniqueness of
walk positions), and both ends are proper positions.
-/

namespace Chazelle.Core

namespace DrvB

@[expose] public section

open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Visibility (DirInterior rayPt chordEnd chordSet chordParam chords hseg OpenEdgePt
  edgeX edgeBot edgeTop NonHoriz)
open Chazelle.Jordan (simple_three_le simple_vtx_ne simple_vtx_succ_ne)
open DrvR (ivB qE)

/-- The direction of the code `d`: `1` for `d = 0`, `-1` otherwise. -/
def sgnD (d : ℕ) : ℝ := if d = 0 then 1 else -1

theorem sgnD_cases (d : ℕ) : sgnD d = 1 ∨ sgnD d = -1 := by
  unfold sgnD; split_ifs <;> simp

theorem sgnD_mul_self (d : ℕ) : sgnD d * sgnD d = 1 := by
  rcases sgnD_cases d with h | h <;> rw [h] <;> norm_num

/-! ## Candidates -/

variable {Q : Polygon}

/-- Edge `q` of `Q` straddles the height of vertex `i` strictly. -/
def Strad (Q : Polygon) (q i : ℕ) : Prop :=
  ((Q.vtx q).2 < (Q.vtx i).2 ∧ (Q.vtx i).2 < (Q.vtx ((q + 1) % Q.n)).2) ∨
    ((Q.vtx ((q + 1) % Q.n)).2 < (Q.vtx i).2 ∧ (Q.vtx i).2 < (Q.vtx q).2)

/-- **A candidate** for the far end of the chord of vertex `i` in direction `σ`: edge `q`
straddles the height of `v_i` strictly and crosses it strictly on the side `σ`. -/
def Cand (Q : Polygon) (i : ℕ) (σ : ℝ) (q : ℕ) : Prop :=
  q < Q.n ∧ Strad Q q i ∧ 0 < σ * (edgeXAt Q q i - (Q.vtx i).1)

theorem strad_nonHoriz {q i : ℕ} (h : Strad Q q i) : NonHoriz Q q := by
  unfold NonHoriz; rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> intro e <;> linarith

/-- A straddling edge crosses the height of `v_i` in its open part. -/
theorem strad_open {q i : ℕ} (h : Strad Q q i) :
    OpenEdgePt Q q ((edgeXAt Q q i, (Q.vtx i).2) : Point) := by
  Ξ Visibility.openEdgePt_iff_edgeX (strad_nonHoriz h)
  refine ⟨?_, rfl⟩
  unfold edgeBot edgeTop
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨lt_of_le_of_lt (min_le_left _ _) h1, lt_of_lt_of_le h2 (le_max_right _ _)⟩
  · exact ⟨lt_of_le_of_lt (min_le_right _ _) h1, lt_of_lt_of_le h2 (le_max_left _ _)⟩

/-- A point of the open part of edge `q` is in no other open edge part. -/
theorem openEdge_unique (hQ : Q.Simple) {q q' : ℕ} (hq : q < Q.n) (hq' : q' < Q.n) {z : Point}
    (h : OpenEdgePt Q q z) (h' : OpenEdgePt Q q' z) : q = q' := by
  by_contra hne
  obtain ⟨t, ht, rfl⟩ := h
  exact Chazelle.Jordan.simple_openEdge_not_mem_other hQ hq ht hq' (Ne.symm hne) h'.mem_edge

/-- The ray point at the crossing abscissa. -/
theorem rayPt_cross {v : Point} {σ x : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    rayPt v σ (σ * (x - v.1)) = ((x, v.2) : Point) := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  ext
  · simp only [Visibility.rayPt_fst]; rw [← mul_assoc, hσσ]; ring
  · ϴ Visibility.rayPt_snd

/-- **No candidate crossing is strictly before the far end.** -/
theorem cand_le (hQ : Q.Simple) {i : ℕ} (hi : i < Q.n) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hdir : DirInterior Q i σ) {q : ℕ} (hc : Cand Q i σ q) :
    σ * (chordEnd Q i σ).1 ≤ σ * edgeXAt Q q i := by
  obtain ⟨hq, hs, hside⟩ := hc
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hX : ((edgeXAt Q q i, (Q.vtx i).2) : Point) ∈ Q.boundary :=
    (strad_open hs).mem_boundary hq
  have hle : chordParam Q i σ ≤ σ * (edgeXAt Q q i - (Q.vtx i).1) := by
    by_contra hlt
    push Not at hlt
    have := (Visibility.chord_spec hQ hi hdir).2.2 _ hside hlt
    Ξ' rayPt_cross hσ at this
    exact this.2 hX
  have e : σ * (chordEnd Q i σ).1 = σ * (Q.vtx i).1 + chordParam Q i σ := by
    Ξ Visibility.chordEnd_fst, mul_add, ← mul_assoc, hσσ, one_mul
  Ξ e
  nlinarith

/-- **The far end is a candidate crossing**, in the open part of its edge. -/
theorem far_cand (hQ : Q.Simple) (hDH : DistinctHeights Q) {i : ℕ} (hi : i < Q.n) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hdir : DirInterior Q i σ) :
    ∃ q, Cand Q i σ q ∧ edgeXAt Q q i = (chordEnd Q i σ).1 ∧ OpenEdgePt Q q (chordEnd Q i σ) := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  set z := chordEnd Q i σ with hz
  have hzb : z ∈ Q.boundary := Visibility.chordEnd_mem_boundary hQ hi hdir
  have hnv : ∀ j, j < Q.n → z ≠ Q.vtx j := by
    intro j hj e
    have hy : (Q.vtx j).2 = (Q.vtx i).2 := by rw [← e]; rfl
    have hji : j = i := by
      by_contra hne; exact hDH _ _ hj hi hne hy
    subst hji
    exact Visibility.chordEnd_ne_vtx hQ hi hdir e
  obtain ⟨q, hq, t, ht, hzt⟩ := Chazelle.Jordan.exists_openEdge_of_mem_boundary Q hzb hnv
  have hop : OpenEdgePt Q q z := ⟨t, ht, hzt⟩
  have hn3 := simple_three_le hQ
  have hNH : NonHoriz Q q := by
    unfold NonHoriz
    refine hDH _ _ hq (Nat.mod_lt _ (⋄)) ?_
    intro e
    by_cases h : q + 1 < Q.n
    · Ξ' Nat.mod_eq_of_lt h at e; omega
    · Ξ' show q + 1 = Q.n by omega, Nat.mod_self at e; omega
  obtain ⟨⟨hb, ht'⟩, hx⟩ := (Visibility.openEdgePt_iff_edgeX hNH).1 hop
  have hz2 : z.2 = (Q.vtx i).2 := rfl
  Ξ' hz2 at hb ht' hx
  have hxq : edgeXAt Q q i = z.1 := hx.symm
  refine ⟨q, ⟨hq, ?_, ?_⟩, hxq, hop⟩
  · unfold edgeBot at hb
    unfold edgeTop at ht'
    rcases le_total (Q.vtx q).2 (Q.vtx ((q + 1) % Q.n)).2 with h | h
    · Ξ' min_eq_left h at hb; Ξ' max_eq_right h at ht'
      exact Or.inl ⟨hb, ht'⟩
    · Ξ' min_eq_right h at hb; Ξ' max_eq_left h at ht'
      exact Or.inr ⟨hb, ht'⟩
  · Ξ hxq, hz, Visibility.chordEnd_fst, add_sub_cancel_left, ← mul_assoc, hσσ, one_mul
    exact Visibility.chordParam_pos hQ hi hdir

/-- **A candidate not after the far end carries it.** -/
theorem cand_min (hQ : Q.Simple) {i : ℕ} (hi : i < Q.n) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hdir : DirInterior Q i σ) {q : ℕ} (hc : Cand Q i σ q)
    (hmin : σ * edgeXAt Q q i ≤ σ * (chordEnd Q i σ).1) :
    OpenEdgePt Q q (chordEnd Q i σ) := by
  have h1 := cand_le hQ hi hσ hdir hc
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hx : edgeXAt Q q i = (chordEnd Q i σ).1 :=
    mul_left_cancel₀ hσ0 (le_antisymm hmin h1)
  have := strad_open hc.2.1
  Ξ' hx at this
  exact this

/-! ## Walk edges -/

/-- `qE` on walk edges is injective. -/
theorem qE_inj {li : Bool} {n w w' : ℕ} (hw : w < n) (hw' : w' < n) (h : qE li n w = qE li n w') :
    w = w' := by
  unfold qE at h; cases li <;> simp at h <;> first | omega | (split_ifs at h <;> omega)

/-- The walk edge of an edge of `Q`. -/
def qEi (li : Bool) (n q : ℕ) : ℕ := if li then q else if q + 1 < n then n - 2 - q else n - 1

theorem qEi_lt (li : Bool) {n q : ℕ} (hq : q < n) : qEi li n q < n := by
  unfold qEi; split_ifs <;> omega

theorem qE_qEi (li : Bool) {n q : ℕ} (hn : 2 ≤ n) (hq : q < n) : qE li n (qEi li n q) = q := by
  unfold qE qEi; cases li <;> simp; split_ifs <;> omega

/-- **A σ-nearest candidate among walk edges** (a set `ES` containing a walk edge whose edge of
`Q` carries the far end) carries the far end. -/
theorem scan_min (hQ : Q.Simple) (hDH : DistinctHeights Q) {i : ℕ} (hi : i < Q.n) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hdir : DirInterior Q i σ) {li : Bool} {ES : ℕ → Prop} {w₀ w : ℕ}
    (hw₀ : w₀ < Q.n) (hw₀E : ES w₀) (hz₀ : OpenEdgePt Q (qE li Q.n w₀) (chordEnd Q i σ))
    (_hwE : ES w) (hc : Cand Q i σ (qE li Q.n w))
    (hmin : ∀ w', ES w' → w' < Q.n → Cand Q i σ (qE li Q.n w') →
      σ * edgeXAt Q (qE li Q.n w) i ≤ σ * edgeXAt Q (qE li Q.n w') i) :
    OpenEdgePt Q (qE li Q.n w) (chordEnd Q i σ) := by
  obtain ⟨q, hcq, hxq, hoq⟩ := far_cand hQ hDH hi hσ hdir
  have hq₀ : q = qE li Q.n w₀ :=
    openEdge_unique hQ hcq.1 (DownMath.qE_lt li hw₀) hoq hz₀
  subst hq₀
  have := hmin w₀ hw₀E hw₀ hcq
  Ξ' hxq at this
  exact cand_min hQ hi hσ hdir hc this

/-! ## The record of a vertex chord -/

/-- **The record of the vertex chord** of `i` in direction `sgnD d` whose far end is on walk edge
`w`: height vertex `i`, the walk edge starting at `v_i` and `w`, as (left end, right end). -/
def vtrip (li : Bool) (n i d w : ℕ) : ℕ × ℕ × ℕ :=
  if d = 0 then (i, ivB li n i, w) else (i, w, ivB li n i)

theorem ivB_ivB (li : Bool) {n i : ℕ} (hi : i < n) : ivB li n (ivB li n i) = i := by
  unfold ivB; cases li <;> simp; omega

theorem wStart_eq_ivB (li : Bool) (n p : ℕ) : DownBase.wStart li n p = ivB li n p := rfl

/-- A point of the open part of edge `qE w` of `Q` is a point of walk edge `w` at a parameter in
`(0, 1)`. -/
theorem openEdge_walk {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) (hn : 3 ≤ Q.n)
    {w : ℕ} (hw : w < Q.n) {z : Point} (hz : OpenEdgePt Q (qE li Q.n w) z) :
    ∃ t ∈ Ioo (0 : ℝ) 1, sidePt (interiorWalk Q) w t = z := by
  obtain ⟨s, hs, rfl⟩ := hz
  have hw1 : (w + 1) % Q.n < Q.n := Nat.mod_lt _ (⋄)
  have hv0 := DownMath.walk_vtx hli hw
  have hv1 := DownMath.walk_vtx hli hw1
  have hWn : (interiorWalk Q).n = Q.n := DownMath.walk_n Q
  rcases DownMath.edge_ends li (⋄) hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨s, hs, ?_⟩
    unfold sidePt; Ξ hWn, hv0, hv1, h1, h2
  · refine ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
    unfold sidePt; Ξ hWn, hv0, hv1, h1, h2, ← Geometry.lerp_symm

/-- **The record of a vertex chord.**  If the far end of the chord of vertex `i` in direction
`sgnD d` lies in the open part of edge `qE w` of `Q`, the record `vtrip li n i d w` describes the
chord, is attached at both ends, and both of its ends are proper positions. -/
theorem vtrip_ok (hQ : Q.Simple) (hDH : DistinctHeights Q) {li : Bool}
    (hli : li = true ↔ Mountain.LeftInside Q) {i d w : ℕ} (hi : i < Q.n) (_hd : d ≤ 1)
    (hdir : DirInterior Q i (sgnD d)) (hw : w < Q.n)
    (hz : OpenEdgePt Q (qE li Q.n w) (chordEnd Q i (sgnD d))) :
    (recOf (vtrip li Q.n i d w)).toSet (interiorModel Q) Q = chordSet Q i (sgnD d) ∧
      (recOf (vtrip li Q.n i d w)).Attached (interiorModel Q) Q ∧
      ProperPos (interiorModel Q) Q Q.n (recOf (vtrip li Q.n i d w)).lpos ∧
      ProperPos (interiorModel Q) Q Q.n (recOf (vtrip li Q.n i d w)).rpos ∧
      (vtrip li Q.n i d w).1 < Q.n := by
  set I := interiorModel Q with hI
  set W := interiorWalk Q with hWdef
  set σ := sgnD d with hσdef
  have hσ := sgnD_cases d
  have hn3 := simple_three_le hQ
  have hWn : W.n = Q.n := DownMath.walk_n Q
  have hWs : W.Simple := (FactsInterior.interiorWalk_spec hQ).1
  set wv := ivB li Q.n i with hwv
  have hwvn : wv < Q.n := DownMath.ivB_lt li hi
  -- the vertex end
  have hWv : W.vtx wv = Q.vtx i := by
    rw [hWdef, DownMath.walk_vtx hli hwvn, hwv, ivB_ivB li hi]
  have hst : i = DownBase.wStart li Q.n wv := by rw [wStart_eq_ivB, hwv, ivB_ivB li hi]
  have hposv : I.pos Q ⟨wv, i + 1⟩ = Q.vtx i := DownBase.pos_start hQ hDH hli hwvn hst
  have hparv : I.param Q ⟨wv, i + 1⟩ = 0 := by
    rw [DownBase.param_eq hQ hDH hli hwvn, DownBase.wa_eq hQ hDH hli hwvn, ← hst, sub_self,
      zero_div]
  -- the far end
  set z := chordEnd Q i σ with hzdef
  obtain ⟨t, ht, hzt⟩ := openEdge_walk hli hn3 hw hz
  have hne := DownBase.wa_wb_snd_ne hQ hDH hli hw
  have hd0 : (I.wb w).2 - (I.wa w).2 ≠ 0 := sub_ne_zero.2 hne.symm
  have hzt' : Geometry.lerp (I.wa w) (I.wb w) t = z := hzt
  have hpart : I.param Q ⟨w, i + 1⟩ = t := by
    rw [DownBase.param_eq hQ hDH hli hw]
    have hy := congrArg Prod.snd hzt'
    simp only [Geometry.lerp_snd] at hy
    have hz2 : z.2 = (Q.vtx i).2 := rfl
    rw [hz2] at hy
    rw [← hy]
    field_simp
    ring
  have hposz : I.pos Q ⟨w, i + 1⟩ = z := by
    simp only [Model.pos]; rw [hpart]; exact hzt'
  -- the chord as a segment between its two ends
  have hc : chordSet Q i σ ∈ chords Q := ⟨i, σ, hi, hσ, hdir, rfl⟩
  have hHC := FullDegInt.hc_full hQ hc
  have hadm := hHC
  have hM := walkAx_interiorModel hQ
  obtain ⟨A, B, hAB, hcAB, -, hopen, hWA, hWB⟩ := hM.ends _ hadm
  have hσσ : σ * σ = 1 := sgnD_mul_self d
  have hpos := Visibility.chordParam_pos hQ hi hdir
  have hvb : Q.vtx i ∈ Q.boundary := ⟨i, hi, Geometry.left_mem_segment _ _⟩
  have hzb : z ∈ Q.boundary := Visibility.chordEnd_mem_boundary hQ hi hdir
  have hD : I.D = Q.filled \ Q.boundary := rfl
  have hend : ∀ x ∈ chordSet Q i σ, x ∈ Q.boundary → x = A ∨ x = B := by
    intro x hx hxb
    rw [hcAB] at hx
    obtain ⟨s, hs0, hs1, hs⟩ := Geometry.mem_segment_iff_lerp.1 hx
    rcases hs0.lt_or_eq with hs0 | hs0
    · rcases hs1.lt_or_eq with hs1 | hs1
      · exact absurd hxb (hs ▸ (hopen s ⟨hs0, hs1⟩).2)
      · right; rw [hs, hs1, Geometry.lerp_one]
    · left; rw [hs, ← hs0, Geometry.lerp_zero]
  have hvA := hend _ (Geometry.left_mem_segment _ _) hvb
  have hzA := hend _ (Geometry.right_mem_segment _ _) hzb
  have hvz : Q.vtx i ≠ z := (Visibility.chordEnd_ne_vtx hQ hi hdir).symm
  have hWEv : WalkEnd I.W (chordSet Q i σ) (Q.vtx i) := by
    rcases hvA with h | h <;> rw [h] <;> assumption
  have hWEz : WalkEnd I.W (chordSet Q i σ) z := by
    rcases hzA with h | h <;> rw [hzdef, h] <;> assumption
  -- the attachments
  have hIW : I.W = W := rfl
  have attv : SideAttach W (chordSet Q i σ) wv 0 := by
    obtain ⟨p, s, hA, hps⟩ := hWEv.1
    rw [hIW] at hA hps
    obtain ⟨hp, hs0, hs1, -⟩ := id hA
    have := FactsInterior.pos_unique hWs hp (by rw [hWn]; exact hwvn) hs0 hs1 le_rfl one_pos
      (by rw [hps, Chazelle.Chain.sidePt_zero, hWv])
    obtain ⟨rfl, rfl⟩ := this
    exact hA
  have attz : SideAttach W (chordSet Q i σ) w t := by
    obtain ⟨p, s, hA, hps⟩ := hWEz.1
    rw [hIW] at hA hps
    obtain ⟨hp, hs0, hs1, -⟩ := id hA
    have := FactsInterior.pos_unique hWs hp (by rw [hWn]; exact hw) hs0 hs1 ht.1.le ht.2
      (by rw [hps, hzt])
    obtain ⟨rfl, rfl⟩ := this
    exact hA
  have pv : ProperPos I Q Q.n ⟨wv, i + 1⟩ := ⟨by rw [hparv], by rw [hparv]; exact one_pos, hi⟩
  have pz : ProperPos I Q Q.n ⟨w, i + 1⟩ := ⟨by rw [hpart]; exact ht.1.le,
    by rw [hpart]; exact ht.2, hi⟩
  have hv1 : (Q.vtx i).1 = ((Q.vtx i).1, (Q.vtx i).2).1 := rfl
  -- the two directions
  unfold vtrip
  by_cases hd0 : d = 0
  · rw [ite_eq_left hd0]
    have hσ1 : σ = 1 := by rw [hσdef, hd0]; rfl
    have hlt : (Q.vtx i).1 < z.1 := by
      rw [hzdef, Visibility.chordEnd_fst,
        show σ * chordParam Q i σ = chordParam Q i σ by rw [hσ1, one_mul]]
      linarith
    have hset : (recOf (i, wv, w)).toSet I Q = chordSet Q i σ := by
      show hseg (Q.vtx i).2 (I.pos Q ⟨wv, i + 1⟩).1 (I.pos Q ⟨w, i + 1⟩).1 = _
      rw [hposv, hposz, Visibility.chordSet_eq_hseg, ← hzdef, min_eq_left hlt.le,
        max_eq_right hlt.le]
    refine ⟨hset, ?_, pv, pz, hi⟩
    unfold CRec.Attached
    rw [hset]
    refine ⟨?_, ?_⟩
    · show SideAttach W _ wv (I.param Q ⟨wv, i + 1⟩); rw [hparv]; exact attv
    · show SideAttach W _ w (I.param Q ⟨w, i + 1⟩); rw [hpart]; exact attz
  · rw [ite_eq_right hd0]
    have hσ1 : σ = -1 := by rw [hσdef]; unfold sgnD; rw [ite_eq_right hd0]
    have hlt : z.1 < (Q.vtx i).1 := by
      rw [hzdef, Visibility.chordEnd_fst,
        show σ * chordParam Q i σ = -chordParam Q i σ by rw [hσ1, neg_one_mul]]
      linarith
    have hset : (recOf (i, w, wv)).toSet I Q = chordSet Q i σ := by
      show hseg (Q.vtx i).2 (I.pos Q ⟨w, i + 1⟩).1 (I.pos Q ⟨wv, i + 1⟩).1 = _
      rw [hposv, hposz, Visibility.chordSet_eq_hseg, ← hzdef, min_eq_right hlt.le,
        max_eq_left hlt.le]
    refine ⟨hset, ?_, pz, pv, hi⟩
    unfold CRec.Attached
    rw [hset]
    refine ⟨?_, ?_⟩
    · show SideAttach W _ w (I.param Q ⟨w, i + 1⟩); rw [hpart]; exact attz
    · show SideAttach W _ wv (I.param Q ⟨wv, i + 1⟩); rw [hparv]; exact attv

end

end DrvB

end Chazelle.Core
