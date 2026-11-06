module

public import Chazelle.Core.SweepIoSpec
public import Chazelle.Core.RestoreTestMath
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `0`, mathematics

Facts used by the driver `cand0` (`SweepIoCand0.lean`):

* `onCB_left`, `onCB_right`: candidates of `C₁`, `C₂` are candidates of `C`;
* `whole_eq_min`, `whole_eq_left`: the first hit of `C` from the first hits of `C₁`, `C₂`
  (both bits `1`; above the top of `C₂`);
* `logIdx_exists`: the log entry of a key on the `C₁` part exists;
* `shared_iff₁`: the shared vertex among the positions of the model of `C₁` (index tests);
* `lhGeo_query`, `lhGeo_box`, `lhGeo_arr`: the geometric conditions of the local hit at the
  query position, at its box twin, at an arrival position.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc sidePrev sideNext)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {J : Merge.Junction}

/-! ## Candidates -/

theorem onCB_left {x : Point} (h : OnCB J.left x) : OnCB J.whole x := by
  rcases h with h | h | h
  · exact Or.inl (J.left_set_subset h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem onCB_right {x : Point} (h : OnCB J.right x) : OnCB J.whole x := by
  rcases h with h | h | h
  · exact Or.inl (J.right_set_subset h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **Both bits `1`**: the first hit of `C` is the earlier of the first hits of `C₁`, `C₂`. -/
theorem whole_eq_min {z : Point} (h₁ : z.2 ≤ J.left.top.2) (h₂ : z.2 ≤ J.right.top.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) :
    J.whole.hitParam z σ = min (J.left.hitParam z σ) (J.right.hitParam z σ) := by
  rw [whole_hitParam_eq_min J (h₁.trans J.left_top_le) hσ, left_hitParam_eq J h₁,
    right_hitParam_eq J h₂]

/-- **Above the top of `C₂`**: the first hit of `C` is the first hit of `C₁`. -/
theorem whole_eq_left {z : Point} (h₁ : z.2 ≤ J.left.top.2) (h₂ : J.right.top.2 < z.2) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) : J.whole.hitParam z σ = J.left.hitParam z σ := by
  rw [whole_hitParam_eq_min J (h₁.trans J.left_top_le) hσ, left_hitParam_eq J h₁,
    rayHit_eq_empty_of_above J.right h₂]
  refine min_eq_left ?_
  rw [← left_hitParam_eq J h₁]
  exact Merge.rayHit_anti (Set.empty_subset _) z hσ

/-- A membership of the first hit of `C` from those of `C₁` and `C₂` (both bits `1`). -/
theorem whole_mem_of_both {z : Point} (h₁ : z.2 ≤ J.left.top.2) (h₂ : z.2 ≤ J.right.top.2)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {L : Set ℝ} (hl : J.left.hitParam z σ ∈ L)
    (hr : J.right.hitParam z σ ∈ L) : J.whole.hitParam z σ ∈ L := by
  rw [whole_eq_min h₁ h₂ hσ]
  rcases min_choice (J.left.hitParam z σ) (J.right.hitParam z σ) with h | h <;> rw [h]
  · exact hl
  · exact hr

/-- Freeness for `C` gives freeness for `C₂` below the top of `C₂`. -/
theorem freeAt_right_of_whole {z : Point} (h₂ : z.2 ≤ J.right.top.2) {σ : ℝ}
    (h : FreeAt J.whole z σ) : FreeAt J.right z σ := by
  unfold FreeAt at h ⊢
  filter_upwards [h] with t ht
  exact dom_right J ht (by rwx [Chazelle.Visibility.rayPt_snd])

/-! ## The log entry -/

/-- **The log entry of a key on the `C₁` part exists.** -/
theorem logIdx_exists {Q : Polygon} {N : NF} {S₂ : Set (Set Point)}
    {ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)} (hlog : LogOK J S₂ (logOf J Q N ls)) {x : ℝ}
    (hx : (Lst J : ℝ) ≤ oW J x) : ∃ i, LogIdx J Q N ls x i := by
  obtain ⟨hne, -, hhead, -⟩ := hlog
  have hlen : 0 < ls.length := by
    rcases ls with _ | ⟨a, ls⟩
    · exact absurd rfl hne
    · simp
  have h0 : oW J (logKey J Q N ls 0) ≤ oW J x := by
    rcases ls with _ | ⟨a, ls⟩
    · simp at hlen
    · simp only [logOf, List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq,
        forall_eq'] at hhead
      unfold logKey
      simp only [logOf, List.map_cons, List.getD_cons_zero]
      rwx [hhead]
  classical
  set p : ℕ → Prop := fun i => oW J (logKey J Q N ls i) ≤ oW J x
  refine ⟨Nat.findGreatest p (ls.length - 1), by
    have := Nat.findGreatest_le (P := p) (ls.length - 1); omega,
    Nat.findGreatest_spec (P := p) (m := 0) (Nat.zero_le _) h0, fun hi => ?_⟩
  have := Nat.findGreatest_is_greatest (P := p) (n := ls.length - 1) (k := Nat.findGreatest p (ls.length - 1) + 1)
    (by omega) (by omega)
  simp only [p, not_le] at this
  exact this

/-! ## The shared vertex among the positions of `M₁` -/

theorem cstL_one : cstL J 1 = 6 + tpos J.left J.m₁ := rfl
theorem cstR_one : cstR J 1 = 6 + tpos J.right 0 := rfl

/-- **The shared vertex in the model of `C₁`**: parameter `0`, and the edge is `cstL 1` or the
last walk edge when `cstL 1 = 6`. -/
theorem shared_iff₁ (hP : J.P.Simple) (Q : Polygon) {x : WPos}
    (hx : x.edge < (chainModel J.left).W.n) (h0 : 0 ≤ (chainModel J.left).param Q x)
    (h1 : (chainModel J.left).param Q x < 1) :
    (chainModel J.left).pos Q x = J.shared ↔ (chainModel J.left).param Q x = 0 ∧
      (x.edge = cstL J 1 ∨ (x.edge + 1 = 2 * J.m₁ + 7 ∧ cstL J 1 = 6)) := by
  have e : J.shared = J.left.vertex J.left.m := rfl
  rw [e, atEnd_iff J.left hP (Or.inr rfl) Q hx h0 h1, cstL_one]
  have hm : J.left.m = J.m₁ := rfl
  rw [hm]
  constructor
  · rintro ⟨ht, h | ⟨h, h'⟩⟩
    · exact ⟨ht, Or.inl (by omega)⟩
    · exact ⟨ht, Or.inr ⟨by omega, by omega⟩⟩
  · rintro ⟨ht, h | ⟨h, h'⟩⟩
    · exact ⟨ht, Or.inl (by omega)⟩
    · exact ⟨ht, Or.inr ⟨by omega, by omega⟩⟩

/-! ## The geometric conditions of the local hits -/

theorem sideChain_zero' : sideChain J 0 = J.left := ite_eq_left rfl

/-- **The query position** of side `0` satisfies `LHGeo` in the model of `C₁`. -/
theorem lhGeo_query {P : Polygon} {q : ℕ × ℕ × ℕ} (hq : QueryOK J (Qof P) 0 q)
    (hht : ((chainModel J.left).pos (Qof P) ⟨q.1, q.2.1⟩).2 = ((Qof P).vtx (q.2.1 - 1)).2) :
    LHGeo P J.left ⟨q.1, q.2.1⟩ q.2.2 := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  obtain ⟨-, hh1, hh2, -, -, htop, hsec⟩ := hq
  simp only [sideChain_zero'] at htop hsec
  refine ⟨q.2.1 - 1, by sio only, by rwo [← hQn], hht.symm, ?_, htop⟩
  have e : rayPt ((chainModel J.left).pos (Qof P) ⟨q.1, q.2.1⟩) (dirOf q.2.2) 1 =
      (((chainModel J.left).pos (Qof P) ⟨q.1, q.2.1⟩).1 + dirOf q.2.2,
        ((chainModel J.left).pos (Qof P) ⟨q.1, q.2.1⟩).2) := by
    simp [rayPt]
  rwx [e]

/-- `sideLeft` at a position depends only on the edge ends when the parameter is positive. -/
theorem sideLeft_congr {W W' : Polygon} {p p' : ℕ} {t : ℝ} (ht : t ≠ 0)
    (ha : W.vtx p = W'.vtx p') (hb : W.vtx ((p + 1) % W.n) = W'.vtx ((p' + 1) % W'.n))
    (x : Point) : sideLeft W p t x ↔ sideLeft W' p' t x := by
  unfold sideLeft sidePrev sideNext sidePt
  rw [ite_eq_right ht, ite_eq_right ht, ha, hb]

/-- **The box twin**: a query position on a vertical side of the box satisfies `LHGeo` in the
model of `C₂` when it is not above the top of `C₂`. -/
theorem lhGeo_box {P : Polygon} {x : WPos} {d : ℕ} (he : x.edge = 1 ∨ x.edge = 3)
    (hg : LHGeo P J.left x d)
    (hy : |((chainModel J.left).pos (Qof P) x).2| < J.left.radius)
    (h₂ : ((chainModel J.left).pos (Qof P) x).2 ≤ J.right.top.2) :
    LHGeo P J.right x d ∧
      (chainModel J.right).pos (Qof P) x = (chainModel J.left).pos (Qof P) x := by
  obtain ⟨ha, hb, hpar, hpos⟩ := boxTwin_pos (C₁ := J.left) (C₂ := J.right) rfl he (Qof P) x.hgt
  obtain ⟨h, hxh, hhn, hyz, hsec, -⟩ := hg
  have hR := J.left.radius_pos
  have ht : (chainModel J.left).param (Qof P) x ≠ 0 := by
    intro h0
    have e : (chainModel J.left).pos (Qof P) x = (chainModel J.left).wa x.edge := by
      unfold Model.pos; rw [h0]; simp [Geometry.lerp]
    rw [e] at hy
    have hW : (chainModel J.left).W = J.left.sideWalk J.left.sideBeta := rfl
    unfold Model.wa at hy
    rw [hW] at hy
    rcases he with h' | h' <;> rw [h'] at hy
    · rw [J.left.sideWalk_vtx_one] at hy; simp [abs_of_pos hR] at hy
    · rw [J.left.sideWalk_vtx_three] at hy; simp [abs_of_pos hR] at hy
  have hx : (chainModel J.right).pos (Qof P) ⟨x.edge, x.hgt⟩ =
      (chainModel J.left).pos (Qof P) ⟨x.edge, x.hgt⟩ := hpos.symm
  refine ⟨⟨h, hxh, hhn, ?_, ?_, ?_⟩, hx⟩
  · rwx [hx]
  · rw [hx, show (chainModel J.right).param (Qof P) x = (chainModel J.left).param (Qof P) x
      from hpar.symm]
    exact (sideLeft_congr ht ha hb _).1 hsec
  · rwx [hx]

/-- **An arrival position** at a point with a height code naming its height satisfies `LHGeo`
with that code. -/
theorem lhGeo_arr {P : Polygon} {C : Chain} {z : Point} {σ : ℝ} {p : ℕ} {t : ℝ}
    (harr : Arrival (chainModel C).W z (-σ) p t) {h : ℕ} (hh : h < P.n)
    (hhz : ((Qof P).vtx h).2 = z.2) (htop : z.2 ≤ C.top.2) {d : ℕ} (hd : dirOf d = σ) :
    LHGeo P C ⟨p, h + 1⟩ d ∧ (chainModel C).pos (Qof P) ⟨p, h + 1⟩ = z ∧
      (chainModel C).param (Qof P) ⟨p, h + 1⟩ = t := by
  obtain ⟨hp, ht0, ht1, hpt, hsec⟩ := harr
  rw [neg_neg] at hsec
  have hsec' : sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) σ 1) := by
    rwx [hpt]
  have hy : ((Qof P).vtx h).2 = (sidePt (chainModel C).W p t).2 := by rwx [hpt]
  have epar := param_of_arrival (Qof P) ht0 ht1 hy hsec'
  have epos := pos_of_arrival (Qof P) ht0 ht1 hy hsec'
  rw [hpt] at epos
  refine ⟨⟨h, rfl, hh, by rwx [epos], ?_, by rwx [epos]⟩, epos, epar⟩
  simp only
  rwx [epos, epar, hd]


/-! ## Positions -/

/-- A position of the class off the box is a point of the chain. -/
theorem posClass_mem {C : Chain} {Q : Polygon} {x : WPos} (hx : PosClass C Q x) (h6 : 6 ≤ x.edge)
    (h0 : 0 ≤ (chainModel C).param Q x) (h1 : (chainModel C).param Q x < 1) :
    (chainModel C).pos Q x ∈ C.set := by
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  rw [pos_eq_sidePt' C Q x, hW]
  rcases hx with (h | h) | ⟨-, hlt⟩ | ⟨hend, hz⟩
  · omega
  · omega
  · have := C.sideWalk_tour_pt_mem C.sideBeta (i := x.edge - 6) (t := (chainModel C).param Q x)
      (by omega) (fun h => by omega) h0 h1
    rwa [show x.edge - 6 + 6 = x.edge by omega] at this
  · rw [hend, hz]
    exact C.sideWalk_tour_pt_mem C.sideBeta (i := 2 * C.m) (t := 0) le_rfl (fun _ => rfl) le_rfl
      one_pos

/-- **The shared vertex in the model of `C₂`**: the position `(cstR 1, h + 1)` (`cstR 1` the tour
edge starting at vertex `0` of `C₂`) with a height code naming the height of the shared vertex. -/
theorem shared_pos₂ (hP : J.P.Simple) (Q : Polygon) {h : ℕ} (hh : (Q.vtx h).2 = J.shared.2) :
    cstR J 1 < (chainModel J.right).W.n ∧
      (chainModel J.right).param Q ⟨cstR J 1, h + 1⟩ = 0 ∧
      (chainModel J.right).pos Q ⟨cstR J 1, h + 1⟩ = J.shared := by
  have hn := cm_n J.right
  have hτ := tpos_lt J.right 0
  have hlt : cstR J 1 < (chainModel J.right).W.n := by rwo [cstR_one, hn]
  have hwa : (chainModel J.right).wa (cstR J 1) = J.shared := by
    have := (vtx_pos_iff J.right hP (k := 0) (Nat.zero_le _) (p := cstR J 1) hlt le_rfl
      one_pos).2 ⟨rfl, tpos J.right 0, by omega, by rwring [cstR_one],
        (endIdx J.right (Or.inl rfl) (by omega)).2 (Or.inl rfl)⟩
    rw [Chazelle.Chain.sidePt_zero] at this
    rwx [← J.right_vertex_zero]
  have hpar : (chainModel J.right).param Q ⟨cstR J 1, h + 1⟩ = 0 := by
    unfold Model.param
    simp only
    split_ifs
    · rfl
    · rws [hwa, hh]
  refine ⟨hlt, hpar, ?_⟩
  unfold Model.pos; rw [hpar]; simp only [Geometry.lerp]; simpa using hwa


/-- A position on a vertical side of the box is not a point of the chain. -/
theorem box_not_mem {C : Chain} {Q : Polygon} {x : WPos} (he : x.edge = 1 ∨ x.edge = 3)
    (hm : (chainModel C).pos Q x ∈ C.set) : False := by
  have hR := C.radius_pos
  have hb := (C.abs_le_coordBound_of_mem_set hm).1
  have hc := C.coordBound_lt_radius
  rw [pos_eq_sidePt' C Q x] at hb
  obtain ⟨-, b1, -, b3, -, -, -⟩ := C.sidePt_box C.sideBeta ((chainModel C).param Q x)
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  rw [hW] at hb
  rcases he with h | h <;> rw [h] at hb
  · rw [b1] at hb; simp only at hb; rwli [abs_neg, abs_of_pos hR] at hb
  · rw [b3] at hb; simp only at hb; rwli [abs_of_pos hR] at hb

end

end SweepIo

end Chazelle.Core
