import Mathlib.Tactic

import RequestProject.QCubeFacetIndex
import RequestProject.QCubeEdgeChainEmbedding
import RequestProject.QCubeThreeSubdivision

/-! Actual codimension-two faces and their coordinate signs. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

  (c : QCube A)
  (a b : V)
def qCubeDoubleFacet   (s t : ZMod 2)  :=
  qCubeFacet (qCubeFacet c a s) b t

@[simp] theorem qCubeDoubleFacet_sgn_first   (hne : a ≠ b)
    (s t : ZMod 2) : (qCubeDoubleFacet c a b s t).sgn a = s := by
  simp [qCubeDoubleFacet, qCubeFacet, hne]

@[simp] theorem qCubeDoubleFacet_sgn_second  
    (s t : ZMod 2) : (qCubeDoubleFacet c a b s t).sgn b = t := by
  simp [qCubeDoubleFacet]

theorem qCubeDoubleFacet_signs_injective   (hne : a ≠ b) :
    Function.Injective (fun i : ZMod 2 × ZMod 2 => qCubeDoubleFacet c a b i.1 i.2) := by
  intro ⟨s, t⟩ ⟨u, v⟩ h
  grind [qCubeDoubleFacet_sgn_first, qCubeDoubleFacet_sgn_second]

theorem qCubeDoubleFacet_spx   (s t : ZMod 2) :
    (qCubeDoubleFacet c a b s t).spx = (c.spx.erase a).erase b := rfl

variable (u v w : V)
def qThreeEdgeCell   (i : Fin 3 × ZMod 2 × ZMod 2)  :=
  if i.1 = 0 then qCubeDoubleFacet c u v i.2.1 i.2.2
  else if i.1 = 1 then qCubeDoubleFacet c u w i.2.1 i.2.2
  else qCubeDoubleFacet c v w i.2.1 i.2.2

theorem qThreeEdgeCell_spx  
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (i : Fin 3 × ZMod 2 × ZMod 2) :
    (qThreeEdgeCell c u v w i).spx = if i.1 = 0 then {w} else if i.1 = 1 then {v} else {u} := by
  aesop (add simp [qThreeEdgeCell, qCubeDoubleFacet_spx])

theorem qThreeEdgeCell_injective  
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    Function.Injective (qThreeEdgeCell c u v w) := by
  intro ⟨e, s, t⟩ ⟨f, a, b⟩ h
  have he := congrArg QCube.spx h
  rw [qThreeEdgeCell_spx c u v w huv huw hvw hs,
    qThreeEdgeCell_spx c u v w huv huw hvw hs] at he
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases e <;> fin_cases f
  · have hp := qCubeDoubleFacet_signs_injective c u v huv h
    exact Prod.ext rfl hp
  · simp_all
  · simp_all
  · simp_all
  · have hp := qCubeDoubleFacet_signs_injective c u w huw h
    exact Prod.ext rfl hp
  · simp_all
  · simp_all
  · simp_all
  · classical solve_by_elim (transparency := .default) [FiniteChains.Davis.qCubeDoubleFacet_signs_injective, Prod.ext, rfl]

/-- Each indexed codimension-two face is an actual edge cube. -/
def qThreeEdge  
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})
    (i : Fin 3 × ZMod 2 × ZMod 2) : QEdge A :=
  ⟨qThreeEdgeCell c u v w i, by
    aesop (add simp [qThreeEdgeCell_spx])⟩

theorem qThreeEdge_injective  
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :
    Function.Injective (qThreeEdge c u v w huv huw hvw hs) := by
  intro i j h
  exact qThreeEdgeCell_injective c u v w huv huw hvw hs (congrArg Subtype.val h)

end FiniteChains.Davis
