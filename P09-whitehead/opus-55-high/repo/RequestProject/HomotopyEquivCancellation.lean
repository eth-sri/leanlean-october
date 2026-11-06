import Mathlib.Topology.Homotopy.Equiv


/-! Cancellation and two-of-six with prescribed continuous forward maps.
All inverse maps and their two homotopies are constructed explicitly from the
given composite equivalences.  Pending Lean verification. -/

namespace ContinuousMap.HomotopyEquiv


variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]

/-- A left homotopy inverse and a possibly different right homotopy inverse
agree up to homotopy.  The result retains exactly the specified forward map. -/
def ofLeftRightHomotopyInverse f (l r : C(Y, X))
    (hl : (l.comp f).Homotopic (ContinuousMap.id X))
    (hr : (f.comp r).Homotopic (ContinuousMap.id Y)) : HomotopyEquiv X Y where
  toFun := f
  invFun := l
  left_inv := hl
  right_inv := by
    have hlr :=
      ((Homotopic.refl l).comp hr.symm).trans (hl.comp (Homotopic.refl r))
    exact ((Homotopic.refl f).comp hlr).trans hr


/-- If `C ∘ F` is homotopic to the identity and `C` is an equivalence, then
`F` is its homotopy inverse.  The forward map is literally `F`. -/
def ofHomotopicSection (C : HomotopyEquiv Y X) F
    (H : (C.toFun.comp F).Homotopic (ContinuousMap.id X)) : HomotopyEquiv X Y where
  toFun := F
  invFun := C.toFun
  left_inv := H
  right_inv := by
    have hF :=
      (C.left_inv.symm.comp (Homotopic.refl F)).trans
        ((Homotopic.refl C.invFun).comp H)
    exact (hF.comp (Homotopic.refl C.toFun)).trans C.left_inv



variable (f : C(X, Y)) (g : C(Y, Z)) (h : C(Z, W))
  (E : HomotopyEquiv X Z) (hE : E.toFun = g.comp f)
  (D : HomotopyEquiv Y W) (hD : D.toFun = h.comp g)

/-- Two-of-six, middle map.  The inverse supplied by `D` is a left inverse
of `g`, and the inverse supplied by `E` gives a right inverse. -/
def twoOfSixMiddle :=
  ofLeftRightHomotopyInverse g (D.invFun.comp h) (f.comp E.invFun)
    (by
      change (D.invFun.comp (h.comp g)).Homotopic (ContinuousMap.id Y)
      rw [← hD]
      exact D.left_inv)
    (by
      change ((g.comp f).comp E.invFun).Homotopic (ContinuousMap.id Z)
      rw [← hE]
      exact E.right_inv)



/-- Two-of-six, left map, with forward map exactly `f` and inverse
`E.invFun ∘ g`. -/
def twoOfSixLeft :=
  ofHomotopicSection ((twoOfSixMiddle f g h E hE D hD).trans E.symm) f (by
    change (E.invFun.comp (g.comp f)).Homotopic (ContinuousMap.id X)
    rw [← hE]
    exact E.left_inv)



/-- Two-of-six, right map, retaining the specified `h`. -/
def twoOfSixRight :=
  ofHomotopicSection (D.symm.trans (twoOfSixMiddle f g h E hE D hD)) h ((twoOfSixMiddle f g h E hE D hD).right_inv)
