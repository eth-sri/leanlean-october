import RequestProject.QCubeSquareCorners


/-! Faithful indexing of the eight internal radial edges of a square subdivision. -/
namespace FiniteChains.Davis
open RACG Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def squareFacetIndex (c : QCube A) (a b : V) (i : Bool × ZMod 2) :=
  if i.1 then qCubeFacet c a i.2 else qCubeFacet c b i.2

theorem squareFacetIndex_spx (c : QCube A) a b (hne : a ≠ b)
    (hs : c.spx = {a, b}) i :
    (squareFacetIndex c a b i).spx = if i.1 then {b} else {a} := by
  cases' i with e s
  cases e
  · exact squareFacet_v_spx c hne hs s
  · exact squareFacet_w_spx c hne hs s

theorem squareFacetIndex_lt (c : QCube A) a b (hs : c.spx = {a, b})
    i : squareFacetIndex c a b i < c := by
  cases' i with e s
  cases e
  · exact qCubeFacet_lt c b s (by simp_all)
  · exact qCubeFacet_lt c a s (by simp_all)

theorem squareFacetIndex_injective (c : QCube A) a b (hne : a ≠ b)
    (hs : c.spx = {a, b}) : Function.Injective (squareFacetIndex c a b) := by
  intro ⟨e, s⟩ ⟨f, t⟩ h
  have hf := congrArg QCube.spx h
  rw [squareFacetIndex_spx c a b hne hs, squareFacetIndex_spx c a b hne hs] at hf
  cases e <;> cases f
  · have he := congrArg (·.sgn b) h
    have hst : s = t := by simpa [squareFacetIndex] using he
    simp_all
  · simp_all
  · simp_all
  · have he := congrArg (·.sgn a) h
    have hst : s = t := by simpa [squareFacetIndex] using he
    simp_all

abbrev SquareRadialIndex := (Bool × ZMod 2) ⊕ (ZMod 2 × ZMod 2)

def squareRadialCell (c : QCube A) (a b : V) : SquareRadialIndex → QCube A
  | .inl i => squareFacetIndex c a b i
  | .inr i => squareCorner c a b i.1 i.2

theorem squareRadialCell_injective (c : QCube A) a b (hne : a ≠ b)
    (hs : c.spx = {a, b}) : Function.Injective (squareRadialCell c a b) := by
  intro i j h
  have hf := congrArg (·.spx.card) h
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (squareFacetIndex_injective c a b hne hs h)
    | inr j =>
      grind [squareRadialCell, squareFacetIndex_spx c a b hne hs, squareCorner_spx c a b hne hs, Finset.card_empty]
  | inr i =>
    cases j with
    | inl j =>
      grind [squareRadialCell, squareFacetIndex_spx c a b hne hs, squareCorner_spx c a b hne hs, Finset.card_empty]
    | inr j => exact congrArg Sum.inr (squareCorner_injective c a b hne h)

def squareRadialEdge (c : QCube A) a b (hne : a ≠ b)
    (hs : c.spx = {a, b}) (i : SquareRadialIndex) : (strictOrderCx (QCube A)).E :=
  ⟨(squareRadialCell c a b i, c), by
    cases i with
    | inl i => exact squareFacetIndex_lt c a b hs i
    | inr i => exact squareCorner_lt c a b hne hs i.1 i.2⟩

theorem squareRadialEdge_injective (c : QCube A) a b hne
    hs : Function.Injective (squareRadialEdge c a b hne hs) := by
  intro i j h
  exact squareRadialCell_injective c a b hne hs
    (congrArg (·.1.1) h)
