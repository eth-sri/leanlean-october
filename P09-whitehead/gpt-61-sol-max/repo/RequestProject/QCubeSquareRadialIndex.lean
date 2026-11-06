import Mathlib.Tactic

import RequestProject.QCubeSquareCorners

/-! Faithful indexing of the eight internal radial edges of a square subdivision. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

  (c : QCube A)
  (a b : V)
def squareFacetIndex   (i : Bool × ZMod 2)  :=
  if i.1 then qCubeFacet c a i.2 else qCubeFacet c b i.2

theorem squareFacetIndex_spx   (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2) :
    (squareFacetIndex c a b i).spx = if i.1 then {b} else {a} := by
  obtain ⟨e, s⟩ := i
  cases e
  · exact squareFacet_v_spx c hne hs s
  · exact squareFacet_w_spx c hne hs s

theorem squareFacetIndex_lt   (hs : c.spx = {a, b})
    (i : Bool × ZMod 2) : squareFacetIndex c a b i < c := by
  obtain ⟨e, s⟩ := i
  cases e
  · exact qCubeFacet_lt c b s (by rw [hs]; simp)
  · exact qCubeFacet_lt c a s (by rw [hs]; simp)

theorem squareFacetIndex_injective   (hne : a ≠ b)
    (hs : c.spx = {a, b}) : Function.Injective (squareFacetIndex c a b) := by
  intro ⟨e, s⟩ ⟨f, t⟩ h
  have hf := congrArg QCube.spx h
  rw [squareFacetIndex_spx c a b hne hs, squareFacetIndex_spx c a b hne hs] at hf
  cases e <;> cases f
  · classical grind [FiniteChains.Davis.qCubeFacet_sgn_self, squareFacetIndex]
  · simp_all
  · simp_all
  · classical grind [FiniteChains.Davis.qCubeFacet_sgn_self, squareFacetIndex]

abbrev SquareRadialIndex := (Bool × ZMod 2) ⊕ (ZMod 2 × ZMod 2)

def squareRadialCell   : SquareRadialIndex → QCube A
  | .inl i => squareFacetIndex c a b i
  | .inr i => squareCorner c a b i.1 i.2

theorem squareRadialCell_injective   (hne : a ≠ b)
    (hs : c.spx = {a, b}) : Function.Injective (squareRadialCell c a b) := by
  intro i j h
  have hf := congrArg (fun d : QCube A => d.spx.card) h
  cases i with
  | inl i =>
    grind [squareFacetIndex_injective, squareRadialCell, squareFacetIndex_spx, squareCorner_spx]
  | inr i =>
    cases j with
    | inl j =>
      grind [squareRadialCell, squareFacetIndex_spx, squareCorner_spx]
    | inr j => exact congrArg Sum.inr (squareCorner_injective c a b hne h)

def squareRadialEdge   (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : SquareRadialIndex) : (strictOrderCx (QCube A)).E :=
  ⟨(squareRadialCell c a b i, c), by
    cases i with
    | inl i => exact squareFacetIndex_lt c a b hs i
    | inr i => exact squareCorner_lt c a b hne hs i.1 i.2⟩

theorem squareRadialEdge_injective   (hne : a ≠ b)
    (hs : c.spx = {a, b}) : Function.Injective (squareRadialEdge c a b hne hs) := by
  intro i j h
  exact squareRadialCell_injective c a b hne hs
    (congrArg (fun e : (strictOrderCx (QCube A)).E => e.1.1) h)

end FiniteChains.Davis
