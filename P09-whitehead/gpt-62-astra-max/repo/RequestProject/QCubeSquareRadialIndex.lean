module

public import RequestProject.QCubeSquareCorners

@[expose] public section

/-! Faithful indexing of the eight internal radial edges of a square subdivision. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

variable (c : QCube A) (a b : V)

def squareFacetIndex (i : Bool × ZMod 2) :=
  if i.1 then qCubeFacet c a i.2 else qCubeFacet c b i.2

theorem squareFacetIndex_spx (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : Bool × ZMod 2) :
    (squareFacetIndex c a b i).spx = if i.1 then {b} else {a} := by
  obtain ⟨e, s⟩ := i
  cases e
  · apply squareFacet_v_spx <;> assumption
  · apply squareFacet_w_spx <;> assumption

theorem squareFacetIndex_lt (hs : c.spx = {a, b})
    (i : Bool × ZMod 2) : squareFacetIndex c a b i < c := by
  obtain ⟨e, s⟩ := i
  cases e
  · exact qCubeFacet_lt c b s (by simp_all)
  · exact qCubeFacet_lt c a s (by simp_all)

theorem squareFacetIndex_injective (hne : a ≠ b)
    (hs : c.spx = {a, b}) : Function.Injective (squareFacetIndex c a b) := by
  intro ⟨e, s⟩ ⟨f, t⟩ h
  have hf := congrArg QCube.spx h
  rw [squareFacetIndex_spx c a b hne hs, squareFacetIndex_spx c a b hne hs] at hf
  cases e <;> cases f
  · have hst : s = t := by simpa [squareFacetIndex] using (congrArg (fun d : QCube A => d.sgn b) h)
    exact Prod.ext rfl hst
  · simp_all
  · simp_all
  · have hst : s = t := by simpa [squareFacetIndex] using (congrArg (fun d : QCube A => d.sgn a) h)
    exact Prod.ext rfl hst

abbrev SquareRadialIndex := (Bool × ZMod 2) ⊕ (ZMod 2 × ZMod 2)

variable (c : QCube A) (a b : V)

def squareRadialCell : SquareRadialIndex → QCube A
  | .inl i => squareFacetIndex c a b i
  | .inr i => squareCorner c a b i.1 i.2

variable (hne : a ≠ b) (hs : c.spx = {a, b})
include hne hs

theorem squareRadialCell_injective : Function.Injective (squareRadialCell c a b) := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => solve_by_elim [squareFacetIndex_injective]
    | inr j =>
      grind [squareRadialCell, squareFacetIndex_spx, squareCorner_spx, Finset.card_empty]
  | inr i =>
    cases j with
    | inl j =>
      grind [squareRadialCell, squareFacetIndex_spx, squareCorner_spx, Finset.card_empty]
    | inr j => solve_by_elim [squareCorner_injective]

def squareRadialEdge (i : SquareRadialIndex) : (strictOrderCx (QCube A)).E :=
  ⟨(squareRadialCell c a b i, c), by
    cases i with
    | inl i => apply squareFacetIndex_lt <;> assumption
    | inr i => apply squareCorner_lt <;> assumption⟩

theorem squareRadialEdge_injective : Function.Injective (squareRadialEdge c a b hne hs) := by
  intro i j h
  exact squareRadialCell_injective c a b hne hs
    (congrArg (fun e : (strictOrderCx (QCube A)).E => e.1.1) h)

end FiniteChains.Davis
