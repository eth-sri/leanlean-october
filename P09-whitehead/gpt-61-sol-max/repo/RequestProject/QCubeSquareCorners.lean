import Mathlib.Tactic

import RequestProject.QCubeSquareFlagIndex

/-! The four actual corners of a square, with their faithful coordinate index. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

  (c : QCube A)
  (a b : V)
def squareCorner   (s t : ZMod 2)  :=
  qCubeFacet (qCubeFacet c a s) b t

@[simp] theorem squareCorner_sgn_left   (hne : a ≠ b)
    (s t : ZMod 2) : (squareCorner c a b s t).sgn a = s := by
  simp [squareCorner, qCubeFacet, hne]

@[simp] theorem squareCorner_sgn_right  
    (s t : ZMod 2) : (squareCorner c a b s t).sgn b = t := by
  simp [squareCorner]

theorem squareCorner_spx   (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s t : ZMod 2) : (squareCorner c a b s t).spx = ∅ := by
  change (c.spx.erase a).erase b = ∅
  simp [*]

abbrev squareCorner_lt   (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s t : ZMod 2)  :=
  (qCubeFacet_lt _ b t (by rw [squareFacet_w_spx c hne hs s]; simp)).trans
    (qCubeFacet_lt c a s (by rw [hs]; simp))

theorem squareCorner_injective   (hne : a ≠ b) :
    Function.Injective (fun i : ZMod 2 × ZMod 2 => squareCorner c a b i.1 i.2) := by
  intro ⟨s, t⟩ ⟨u, v⟩ h
  have hl := congrArg (fun x : QCube A => x.sgn a) h
  have hr := congrArg (fun x : QCube A => x.sgn b) h
  simp [squareCorner_sgn_left _ _ _ hne] at hl
  simp  at hr
  exact Prod.ext hl hr

abbrev squareCorner_positive   (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s : ZMod 2)  :=
  qCubeFacet_zero_of_singleton _ b (squareFacet_w_spx c hne hs s)

abbrev squareCorner_negative   (hne : a ≠ b)
    (hs : c.spx = {a, b}) (s : ZMod 2)  :=
  qCubeFacet_one_of_singleton _ b (squareFacet_w_spx c hne hs s)

abbrev squareCorner_swap   (hne : a ≠ b) (s t : ZMod 2)  :=
  FiniteChains.Davis.qCubeFacet_comm c hne s t

end FiniteChains.Davis
