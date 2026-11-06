module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoCand1E

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `1`, the classes of a query

Geometry of the classes of a side-1 query position `x` in the model of `C₂`:

* `tour_set`: a position of the class off the box walls is a point of `C₂`;
* `shared_iffR`, `top_iffR`: the shared vertex and the top of `C₂` among the positions (index
  tests);
* `shared_posL`: the vertex position of the shared vertex in the model of `C₁`;
* `lhGeo_boxL`: the box twin in the model of `C₁`; `lhGeo_arr`: an arrival position;
* `endQ_facts`: an endpoint query starts at `endOrigin` in the direction `endDir`;
* `whole_mem`: the first hit of `C` from those of `C₂` and (below the top of `C₁`) `C₁`.
-/

namespace Chazelle.Core

namespace SweepIo

open Set
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sidePrev sideNext)
open Chazelle.Merge (FreeAt)

@[expose] public section

namespace Cand1

variable {J : Merge.Junction}

/-- **A position of the class off the box walls** is a point of the chain, on a tour edge. -/
theorem tour_set (C : Chain) (Q : Polygon) {x : WPos} (hc : PosClass C Q x)
    (hb : ¬ (x.edge = 1 ∨ x.edge = 3)) (h0 : 0 ≤ (chainModel C).param Q x)
    (h1 : (chainModel C).param Q x < 1) :
    (chainModel C).pos Q x ∈ C.set ∧ 6 ≤ x.edge ∧
      ((6 ≤ x.edge ∧ x.edge < 2 * C.m + 6) ∨
        (x.edge = 2 * C.m + 6 ∧ (chainModel C).param Q x = 0)) := by
  rcases hc with hc | hc | hc
  · omega
  · refine ⟨?_, hc.1, Or.inl hc⟩
    rw [pos_eq_sidePt' C Q x]
    have e : x.edge = (x.edge - 6) + 6 := by omega
    rw [e]
    exact C.sideWalk_tour_pt_mem C.sideBeta (by omega) (fun h => by omega) h0 h1
  · refine ⟨?_, by omega, Or.inr hc⟩
    rw [pos_eq_sidePt' C Q x, hc.1, hc.2]
    exact C.sideWalk_tour_pt_mem C.sideBeta (i := 2 * C.m) le_rfl (fun _ => rfl) le_rfl one_pos

section
variable (hP : J.P.Simple) (Q : Polygon) {x : WPos} (hx : x.edge < (chainModel J.right).W.n) (h0 : 0 ≤ (chainModel J.right).param Q x) (h1 : (chainModel J.right).param Q x < 1)
include hP hx h0 h1
/-- **The shared vertex in the model of `C₂`**: parameter `0`, and the edge is `cstR 1` or the
last walk edge when `cstR 1 = 6`. -/
theorem shared_iffR :
    (chainModel J.right).pos Q x = J.shared ↔ (chainModel J.right).param Q x = 0 ∧
      (x.edge = cstR J 1 ∨ (x.edge + 1 = 2 * J.m₂ + 7 ∧ cstR J 1 = 6)) := by
  rw [← J.right_vertex_zero, atEnd_iff J.right hP (Or.inl rfl) Q hx h0 h1]
  have e : cstR J 1 = 6 + tpos J.right 0 := rfl
  simp_all

/-- **The top of `C₂`** among the positions of its model. -/
theorem top_iffR :
    (chainModel J.right).pos Q x = J.right.top ↔ (chainModel J.right).param Q x = 0 ∧
      (x.edge = 6 ∨ x.edge + 1 = 2 * J.m₂ + 7 ∨ x.edge = 6 + midT J.right) := by
  rw [atTop_iff J.right hP Q hx h0 h1]
  simp_all


end

theorem param_hgt0 (M : Model) (Q : Polygon) (e : ℕ) : M.param Q ⟨e, 0⟩ = 0 := rfl

/-- **The vertex position of the shared vertex in the model of `C₁`.** -/
theorem shared_posL (hP : J.P.Simple) (Q : Polygon) (n : ℕ) :
    cstL J 1 < (chainModel J.left).W.n ∧ ProperPos (chainModel J.left) Q n ⟨cstL J 1, 0⟩ ∧
      (chainModel J.left).pos Q ⟨cstL J 1, 0⟩ = J.shared := by
  have hp0 := param_hgt0 (chainModel J.left) Q (cstL J 1)
  have hn := cm_n J.left
  have ht := tpos_lt J.left J.m₁
  have e : cstL J 1 = 6 + tpos J.left J.m₁ := rfl
  have hlt : cstL J 1 < (chainModel J.left).W.n := by omega
  refine ⟨hlt, ⟨by rw [hp0], by simp_all, Nat.zero_le _⟩, ?_⟩
  rw [show J.shared = J.left.vertex J.left.m from rfl,
    atEnd_iff J.left hP (Or.inr rfl) Q hlt (by rw [hp0]) (by simp_all)]
  simp_all

/-- `sideLeft` at a position depends only on the edge ends when the parameter is positive. -/
theorem sideLeft_congr {W W' : Polygon} {p p' : ℕ} {t : ℝ} (ht : t ≠ 0)
    (ha : W.vtx p = W'.vtx p') (hb : W.vtx ((p + 1) % W.n) = W'.vtx ((p' + 1) % W'.n))
    (x : Point) : sideLeft W p t x ↔ sideLeft W' p' t x := by
  simp_all [sideLeft, sidePrev, sideNext, sidePt] 

/-- **The box twin**: a query position on a vertical side of the box satisfies `LHGeo` in the
model of `C₁` when it is not above the top of `C₁`. -/
theorem lhGeo_boxL {P : Polygon} {x : WPos} {d : ℕ} (he : x.edge = 1 ∨ x.edge = 3)
    (hg : LHGeo P J.right x d)
    (hy : |((chainModel J.right).pos (Qof P) x).2| < J.right.radius)
    (h₁ : ((chainModel J.right).pos (Qof P) x).2 ≤ J.left.top.2) :
    LHGeo P J.left x d ∧
      (chainModel J.left).pos (Qof P) x = (chainModel J.right).pos (Qof P) x ∧
      (chainModel J.left).param (Qof P) x = (chainModel J.right).param (Qof P) x := by
  obtain ⟨ha, hb, hpar, hpos⟩ := boxTwin_pos (C₁ := J.right) (C₂ := J.left) rfl he (Qof P) x.hgt
  obtain ⟨h, hxh, hhn, hyz, hsec, -⟩ := hg
  have hR := J.right.radius_pos
  have ht : (chainModel J.right).param (Qof P) x ≠ 0 := by
    intro h0
    have e : (chainModel J.right).pos (Qof P) x = (chainModel J.right).wa x.edge := by
      simp_all [Model.pos, Geometry.lerp] 
    rw [e] at hy
    have hW : (chainModel J.right).W = J.right.sideWalk J.right.sideBeta := rfl
    unfold Model.wa at hy
    rw [hW] at hy
    rcases he with h' | h' <;> rw [h'] at hy
    · rw [J.right.sideWalk_vtx_one] at hy; grind
    · rw [J.right.sideWalk_vtx_three] at hy; grind
  have hx : (chainModel J.left).pos (Qof P) ⟨x.edge, x.hgt⟩ =
      (chainModel J.right).pos (Qof P) ⟨x.edge, x.hgt⟩ := hpos.symm
  have hp : (chainModel J.left).param (Qof P) x = (chainModel J.right).param (Qof P) x :=
    hpar.symm
  refine ⟨⟨h, hxh, hhn, ?_, ?_, ?_⟩, hx, hp⟩
  · rw [hx]; exact hyz
  · rw [hx, hp]
    exact (sideLeft_congr ht ha hb _).1 hsec
  · rw [hx]; exact h₁

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
    simp_all
  have hy : ((Qof P).vtx h).2 = (sidePt (chainModel C).W p t).2 := by simp_all
  have epar := param_of_arrival (Qof P) ht0 ht1 hy hsec'
  have epos := pos_of_arrival (Qof P) ht0 ht1 hy hsec'
  ram_grind

/-- **An endpoint query** starts at the origin `endOrigin j` in the direction `endDir j`. -/
theorem endQ_facts {Q : Polygon} {N : NF} (hN : IsNF (chainModel J.right) Q N) {j : ℕ}
    (hj : j < 2 * N.nChords) {e h d : ℕ}
    (hq : (e, h, d) = (sweepEndQ N.chords).getD j (0, 0, 0)) :
    (chainModel J.right).pos Q ⟨e, h⟩ = endOrigin J Q N j ∧ dirOf d = endDir j := by
  obtain ⟨h1, h2⟩ := endOrigin_eq J hN hj
  have hl : N.nChords = N.chords.length := rfl
  have hj' : j < 2 * N.chords.length := by omega
  unfold sweepEndQ at hq
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj'] at hq
  simp only [Option.map_some, Option.getD_some] at hq
  rw [h1]
  unfold endPos endDir
  have hc : N.chords.getD (j / 2) ⟨0, 0, 0, 0, 0⟩ = N.chord (j / 2) := rfl
  rw [hc] at hq
  by_cases hp : j % 2 = 0
  · rw [ite_eq_left hp] at hq
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    aesop (add simp [dirOf]) (add safe (by omega))
  · rw [ite_eq_right hp] at hq
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    rw [ite_eq_right (show ¬ j % 2 = 0 from hp), ite_eq_right (show j % 2 ≠ 0 from hp)]
    exact ⟨rfl, by simp [dirOf]⟩

/-- **The first hit of `C`** is a candidate when that of `C₂` is and, below the top of `C₁`,
that of `C₁` is. -/
theorem whole_mem {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hz₂ : z.2 ≤ J.right.top.2)
    (hf : FreeAt J.whole z σ) {L : Set ℝ} (h2 : J.right.hitParam z σ ∈ L)
    (h1 : z.2 ≤ J.left.top.2 → J.left.hitParam z σ ∈ L) : J.whole.hitParam z σ ∈ L := by
  by_cases hz₁ : z.2 ≤ J.left.top.2
  · rcases whole_hit_cases J hσ hz₁ hz₂ with e | e <;> rw [e]
    all_goals simp_all
  · rw [whole_hit_above J hσ hz₂ (not_le.1 hz₁) (freeAt_right_of J hz₂ hf)]
    exact h2

/-- A point of `C₂` other than the shared vertex is not a point of `C₁`. -/
theorem not_mem_left (hP : J.P.Simple) {z : Point} (h2 : z ∈ J.right.set) (hs : z ≠ J.shared) :
    z ∉ J.left.set := fun h1 => by
  have h : z ∈ J.left.set ∩ J.right.set := ⟨h1, h2⟩
  rw [J.left_inter_right hP] at h
  exact hs h

/-- A point of `C₂` is strictly inside the box. -/
theorem abs_lt_whole {z : Point} (h : z ∈ J.right.set) :
    |z.1| < J.whole.radius ∧ |z.2| < J.whole.radius := by
  have h' := J.whole.abs_le_coordBound_of_mem_set (J.right_set_subset h)
  have := J.whole.coordBound_lt_radius
  ram_grind

end Cand1

end

end SweepIo

end Chazelle.Core
