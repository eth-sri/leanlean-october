module

public import Chazelle.Core.OracleRamEdge

/-!
# Lemma 3.6 (WP-H), part 12: the meaning of the scan steps

`OracleR.upd1` is one step of the scan of the query program (keep the best chain edge hit so
far).  This file proves what it computes: for the ray from `z` at the height of vertex `hz`,

* `hit_chainEdge`: the answer for one chain edge is `some (vOf ci)` if `HitC ci`, `none`
  otherwise (for a symbolic origin, and for a box origin on the side the ray comes from);
* `fold_step`: if `best` answers the first hit on `S`, then `upd1 best ci` answers it on
  `S ∪ chainEdge ci`.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open OracleQ OracleR

namespace OracleQ

variable (Q : Polygon) (s hz : ℕ) (σ : ℝ) (z : Point)

open Classical in
/-- The parameter of the point of chain edge `ci` at the height of the ray (`-1`, never a hit
parameter, if the edge does not span that height: so a recorded best edge is spanning). -/
noncomputable def vOf (ci : ℕ) : ℝ :=
  if Spans Q (eIdx Q.n s ci) hz then σ * (xe Q (eIdx Q.n s ci) hz - z.1) else -1

/-- The parameter of a best chain edge. -/
noncomputable def bestVal (best : Option ℕ) : Option ℝ := best.map (vOf Q s hz σ z)

variable {Q s hz σ z}

theorem vOf_of_spans {ci : ℕ} (h : Spans Q (eIdx Q.n s ci) hz) :
    vOf Q s hz σ z ci = σ * (xe Q (eIdx Q.n s ci) hz - z.1) := by
  classical
  unfold vOf; rw [ite_eq_left h]

theorem spans_of_vOf_pos {ci : ℕ} (h : 0 < vOf Q s hz σ z ci) : Spans Q (eIdx Q.n s ci) hz := by
  classical
  by_contra hn
  unfold vOf at h; rw [ite_eq_right hn] at h; norm_num at h

/-- **The origin data of the scan**: a symbolic origin `z` (`some z`), or a box origin on the
side the ray comes from (`none`). -/
def ZoOK (C : Chain) (σ : ℝ) (z : Point) (zo : Option Point) : Prop :=
  zo = some z ∨ (zo = none ∧ z.1 = -σ * C.radius)

open Classical in
/-- **The answer for one chain edge.** -/
theorem hit_chainEdge {C : Chain} (hCQ : C.P = Q) (hs : C.s = s) (hD : DistinctHeights Q)
    {ci : ℕ} (hci : ci < C.m) (hzy : z.2 = (Q.vtx hz).2) (hσ : σ = 1 ∨ σ = -1)
    {zo : Option Point} (hzo : ZoOK C σ z zo) :
    Sweep.FirstHitOpt (C.chainEdge ci) z σ
      (if HitC Q s hz σ zo ci then some (vOf Q s hz σ z ci) else none) := by
  classical
  have hn2 : 2 ≤ Q.n := by rw [← hCQ]; have := C.add_one_le; have := C.one_le; omega
  have he : C.chainEdge ci = Q.edge (eIdx Q.n s ci) := by
    unfold Chain.chainEdge Chain.edgeIdx eIdx; rw [hCQ, hs]
  set e := eIdx Q.n s ci with he_def
  have hen : e < Q.n := Nat.mod_lt _ (by omega)
  have hne : (Q.vtx e).2 ≠ (Q.vtx ((e + 1) % Q.n)).2 := by
    refine hD _ _ hen (Nat.mod_lt _ (by omega)) ?_
    intro h
    rcases Nat.lt_or_ge (e + 1) Q.n with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at h; omega
    · rw [show e + 1 = Q.n by omega, Nat.mod_self] at h; omega
  have hspec := edgeHit_spec Q hne hzy hσ
  rw [he]
  suffices hiff : (Spans Q e hz ∧ 0 < σ * (xe Q e hz - z.1)) ↔ HitC Q s hz σ zo ci by
    unfold edgeHit at hspec
    by_cases h : HitC Q s hz σ zo ci
    · rw [ite_eq_left h, vOf_of_spans h.1]; rwa [ite_eq_left (hiff.2 h)] at hspec
    · rw [ite_eq_right h]; rwa [ite_eq_right (fun h' => h (hiff.1 h'))] at hspec
  unfold HitC
  rw [← he_def]
  rcases hzo with rfl | ⟨rfl, hz1⟩
  · simp only [Ahead]
    rw [ahead_iff hσ]
  · simp only [Ahead, and_true]
    constructor
    · exact fun h => h.1
    · intro hsp
      refine ⟨hsp, ?_⟩
      -- the point is on the chain, hence in the box
      have hmem : ((xe Q e hz, (Q.vtx hz).2) : Point) ∈ C.chainEdge ci := by
        rw [he]
        have := (rayPt_mem_edge_iff Q hne (z := ((xe Q e hz, (Q.vtx hz).2) : Point)) rfl
          (Or.inl rfl) 0).2 ⟨hsp, by simp⟩
        simpa [rayPt] using this
      have hbox := C.set_subset_box ⟨ci, hci, hmem⟩
      have hx := (abs_lt.1 hbox.1)
      simp only at hx
      rw [hz1]
      rcases hσ with rfl | rfl
      · linarith [hx.1]
      · linarith [hx.2]

open Classical in
/-- **One step of the scan.** -/
theorem fold_step {C : Chain} (hCQ : C.P = Q) (hs : C.s = s) (hD : DistinctHeights Q)
    {ci : ℕ} (hci : ci < C.m) (hzy : z.2 = (Q.vtx hz).2) (hσ : σ = 1 ∨ σ = -1)
    {zo : Option Point} (hzo : ZoOK C σ z zo) {S : Set Point} {best : Option ℕ}
    (hS : Sweep.FirstHitOpt S z σ (bestVal Q s hz σ z best)) :
    Sweep.FirstHitOpt (S ∪ C.chainEdge ci) z σ
      (bestVal Q s hz σ z (upd1 Q s hz σ zo best ci)) := by
  classical
  have hu := Sweep.firstHitOpt_union hS (hit_chainEdge hCQ hs hD hci hzy hσ hzo)
  convert hu using 1
  unfold upd1
  by_cases hh : HitC Q s hz σ zo ci
  · rw [ite_eq_left hh]
    by_cases hall : ∀ cb, best = some cb → BetterC Q s hz σ ci cb
    · rw [ite_eq_left ⟨hh, hall⟩]
      rcases best with _ | cb
      · rfl
      · have hb := hall cb rfl
        have hcb := spans_of_vOf_pos (show FirstHit S z σ (vOf Q s hz σ z cb) from hS).1
        have hlt : vOf Q s hz σ z ci < vOf Q s hz σ z cb := by
          rwa [vOf_of_spans hh.1, vOf_of_spans hcb, better_iff hσ]
        show some (vOf Q s hz σ z ci) = some (min (vOf Q s hz σ z cb) (vOf Q s hz σ z ci))
        rw [min_eq_right hlt.le]
    · rw [ite_eq_right (fun h => hall h.2)]
      push Not at hall
      obtain ⟨cb, rfl, hnb⟩ := hall
      have hcb := spans_of_vOf_pos (show FirstHit S z σ (vOf Q s hz σ z cb) from hS).1
      have hle : vOf Q s hz σ z cb ≤ vOf Q s hz σ z ci := by
        by_contra hc
        push Not at hc
        rw [vOf_of_spans hh.1, vOf_of_spans hcb] at hc
        exact hnb (by rwa [better_iff hσ] at hc)
      show some (vOf Q s hz σ z cb) = some (min (vOf Q s hz σ z cb) (vOf Q s hz σ z ci))
      rw [min_eq_left hle]
  · rw [ite_eq_right hh, ite_eq_right (fun h => hh h.1)]
    rcases best with _ | cb <;> rfl

end OracleQ

end

end Chazelle.Core
