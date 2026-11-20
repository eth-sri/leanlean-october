module

public import RequestProject.QCubeSquareFlagIndex

@[expose] public section

/-! The four actual corners of a square, with their faithful coordinate index. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

variable (c : QCube A) (a b : V)

def squareCorner (s t : ZMod 2) :=
  qCubeFacet (qCubeFacet c a s) b t

@[simp] theorem squareCorner_sgn_left (hne : a ≠ b)
    (s t : ZMod 2) : (squareCorner c a b s t).sgn a = s := by
  simp [squareCorner, qCubeFacet, hne]

@[simp] theorem squareCorner_sgn_right
    (s t : ZMod 2) : (squareCorner c a b s t).sgn b = t := by
  simp [squareCorner]

variable (hne : a ≠ b)
include hne

section

variable (hs : c.spx = {a, b}) (s t : ZMod 2)
include hs

theorem squareCorner_spx : (squareCorner c a b s t).spx = ∅ := by
  change (c.spx.erase a).erase b = ∅
  simp_all

theorem squareCorner_lt : squareCorner c a b s t < c :=
  (qCubeFacet_lt _ b t (by grind [squareFacet_w_spx])).trans
    (qCubeFacet_lt c a s (by simp_all))

end

theorem squareCorner_injective :
    Function.Injective (fun i : ZMod 2 × ZMod 2 => squareCorner c a b i.1 i.2) := by
  intro ⟨s, t⟩ ⟨u, v⟩ h
  grind [squareCorner_sgn_left, squareCorner_sgn_right]

section

variable (hs : c.spx = {a, b}) (s : ZMod 2)
include hs

theorem squareCorner_positive :
    squareCorner c a b s 0 = cubePositiveVertex (qCubeFacet c a s) :=
  qCubeFacet_zero_of_singleton _ b (squareFacet_w_spx c hne hs s)

theorem squareCorner_negative :
    squareCorner c a b s 1 = cubeNegativeVertex (qCubeFacet c a s) b :=
  by simp_all [squareCorner, cubeNegativeVertex, qCubeFacet]

end

theorem squareCorner_swap (s t : ZMod 2) :
    squareCorner c a b s t = squareCorner c b a t s :=
  qCubeFacet_comm c hne s t

end FiniteChains.Davis
