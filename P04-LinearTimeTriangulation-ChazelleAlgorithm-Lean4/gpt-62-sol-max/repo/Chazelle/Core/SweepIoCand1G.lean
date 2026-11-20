module

public import Chazelle.Core.SweepIoCand1E

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `1`, the classes of a query

Geometry of the classes of a side-1 query position `x` in the model of `C₂`:

* `tour_set`: a position of the class off the box walls is a point of `C₂`;
* `shared_iffR`, `top_iffR`: the shared vertex and the top of `C₂` among the positions (index
  tests);
* `shared_posL`: the vertex position of the shared vertex in the model of `C₁`;
* use `lhGeo_boxTwin` and `lhGeo_arr` for the box and arrival cases;
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
  · exact absurd hc hb
  · refine ⟨?_, hc.1, Or.inl hc⟩
    rw [pos_eq_sidePt' C Q x]
    have e : x.edge = (x.edge - 6) + 6 := by omega
    rw [e]
    exact C.sideWalk_tour_pt_mem C.sideBeta (by omega) (fun h => by omega) h0 h1
  · refine ⟨?_, by omega, Or.inr hc⟩
    rw [pos_eq_sidePt' C Q x, hc.1, hc.2]
    exact C.sideWalk_tour_pt_mem C.sideBeta (i := 2 * C.m) le_rfl (fun _ => rfl) le_rfl one_pos

section

variable (hP : J.P.Simple) (Q : Polygon) {x : WPos}
    (hx : x.edge < J.rightModel.W.n) (h0 : 0 ≤ J.rightModel.param Q x)
    (h1 : J.rightModel.param Q x < 1)
include hP hx h0 h1

/-- **The shared vertex in the model of `C₂`**: parameter `0`, and the edge is `cstR 1` or the
last walk edge when `cstR 1 = 6`. -/
theorem shared_iffR :
    J.rightModel.pos Q x = J.shared ↔ J.rightModel.param Q x = 0 ∧
      (x.edge = cstR J 1 ∨ (x.edge + 1 = 2 * J.m₂ + 7 ∧ cstR J 1 = 6)) := by
  rw [← J.right_vertex_zero, atEnd_iff J.right hP (Or.inl rfl) Q hx h0 h1]
  have e : cstR J 1 = 6 + tpos J.right 0 := rfl
  have hm : J.right.m = J.m₂ := rfl
  simp_all

/-- **The top of `C₂`** among the positions of its model. -/
theorem top_iffR :
    J.rightModel.pos Q x = J.right.top ↔ J.rightModel.param Q x = 0 ∧
      (x.edge = 6 ∨ x.edge + 1 = 2 * J.m₂ + 7 ∨ x.edge = 6 + midT J.right) := by
  rw [atTop_iff J.right hP Q hx h0 h1]
  have hm : J.right.m = J.m₂ := rfl
  rw [hm]
  constructor
  · rintro ⟨ht, h | h | h⟩
    · exact ⟨ht, Or.inl h⟩
    · exact ⟨ht, Or.inr (Or.inl (by omega))⟩
    · exact ⟨ht, Or.inr (Or.inr h)⟩
  · rintro ⟨ht, h | h | h⟩
    · exact ⟨ht, Or.inl h⟩
    · exact ⟨ht, Or.inr (Or.inl (by omega))⟩
    · exact ⟨ht, Or.inr (Or.inr h)⟩

end

abbrev param_hgt0 := @Chazelle.Core.IOrc.param_zero

/-- **The vertex position of the shared vertex in the model of `C₁`.** -/
theorem shared_posL (hP : J.P.Simple) (Q : Polygon) (n : ℕ) :
    cstL J 1 < J.leftModel.W.n ∧ ProperPos J.leftModel Q n ⟨cstL J 1, 0⟩ ∧
      J.leftModel.pos Q ⟨cstL J 1, 0⟩ = J.shared := by
  have hp0 := param_hgt0 J.leftModel Q (cstL J 1)
  have hn := cm_n J.left
  have ht := tpos_lt J.left J.m₁
  have e : cstL J 1 = 6 + tpos J.left J.m₁ := rfl
  have hlt : cstL J 1 < J.leftModel.W.n := by rw [hn, e]; omega
  refine ⟨hlt, ⟨by rw [hp0], by rw [hp0]; norm_num, Nat.zero_le _⟩, ?_⟩
  rw [show J.shared = J.left.vertex J.left.m from rfl,
    atEnd_iff J.left hP (Or.inr rfl) Q hlt (by rw [hp0]) (by rw [hp0]; norm_num)]
  exact ⟨hp0, Or.inl e⟩

/-- **An endpoint query** starts at the origin `endOrigin j` in the direction `endDir j`. -/
theorem endQ_facts {Q : Polygon} {N : NF} (hN : IsNF J.rightModel Q N) {j : ℕ}
    (hj : j < 2 * N.nChords) {e h d : ℕ}
    (hq : (e, h, d) = (sweepEndQ N.chords).getD j (0, 0, 0)) :
    J.rightModel.pos Q ⟨e, h⟩ = endOrigin J Q N j ∧ dirOf d = endDir j := by
  obtain ⟨h1, h2⟩ := endOrigin_eq J hN hj
  have hl : N.nChords = N.chords.length := rfl
  have hj' : j < 2 * N.chords.length := by rwa [← hl]
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
    rw [ite_eq_left hp, ite_eq_left hp]
    exact ⟨rfl, by simp [dirOf]⟩
  · rw [ite_eq_right hp] at hq
    simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl⟩ := hq
    rw [ite_eq_right (hp), ite_eq_right (hp)]
    exact ⟨rfl, by simp [dirOf]⟩

/-- **The first hit of `C`** is a candidate when that of `C₂` is and, below the top of `C₁`,
that of `C₁` is. -/
theorem whole_mem {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hz₂ : z.2 ≤ J.right.top.2)
    (hf : FreeAt J.whole z σ) {L : Set ℝ} (h2 : J.right.hitParam z σ ∈ L)
    (h1 : z.2 ≤ J.left.top.2 → J.left.hitParam z σ ∈ L) : J.whole.hitParam z σ ∈ L := by
  by_cases hz₁ : z.2 ≤ J.left.top.2
  · rcases whole_hit_cases J hσ hz₁ hz₂ with e | e <;> rw [e]
    · exact h1 hz₁
    · exact h2
  · rwa [whole_hit_above J hσ hz₂ (not_le.1 hz₁) (freeAt_right_of J hz₂ hf)]

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
  exact ⟨lt_of_le_of_lt h'.1 this, lt_of_le_of_lt h'.2 this⟩

end Cand1

end

end SweepIo

end Chazelle.Core
