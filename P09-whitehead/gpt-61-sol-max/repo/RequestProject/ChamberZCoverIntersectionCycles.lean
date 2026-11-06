import Mathlib.Tactic

import RequestProject.PosetCoverRoofCycles
import RequestProject.ChamberZCoverOrdinaryCycles

/-! Actual finite fillings in lifted attaching intersections. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

theorem strict_oneCycle_cover_attaching_intersection (hf : IsPosetCover f)
    (w : CayGroup A) (hw : w ≠ 1)
    (c : StrictOrdEdge {p : P // ZJSet w (f p)} →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx {p : P // ZJSet w (f p)}) c = 0) :
    ∃ y : StrictOrdTri {p : P // ZJSet w (f p)} →₀ ℤ,
      Comb.bdry2 (strictOrderCx {p : P // ZJSet w (f p)}) y = c := by
  let S : Set (Zpos A X M att) := {z | ZJSet w z}
  let e := zJSetOrderIso (A := A) (X := X) (M := M) (att := att) w
  let g  := fun q => e.symm (interRho (e q))
  let b  := e.symm (interTop hw)
  have hmono : Monotone g := fun _ _ h =>
    e.symm.monotone (interRho_mono (e.monotone h))
  have hg : ∀ q, g q ≤ q := by
    intro q
    have h := e.symm.monotone (interRho_le (e q))
    simpa only [OrderIso.symm_apply_apply] using h
  have hb  := fun q =>
    e.symm.monotone (interRho_le_top hw (e q))
  exact strict_oneCycle_cover_roof (IsPosetCover.restriction f S hf)
    g hmono hg b hb c hc

end FiniteChains.Davis
