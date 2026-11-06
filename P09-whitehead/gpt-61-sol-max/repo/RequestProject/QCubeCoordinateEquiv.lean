import Mathlib.Tactic

import RequestProject.ChamberQuotient
import RequestProject.TruncatedCube
import RequestProject.CmpNerve

/-! The quotient cube cells are the actual coordinate cubes used in the geometric collapse. -/

namespace FiniteChains.Davis
open RACG Mirror
variable {V : Type} [DecidableEq V] [Fintype V] {A : CommRel V}

  (c : QCube A)
/-- Zero parity is the positive corner, consistently with the corner removed in `QOld`. -/
def qCubeToCoordinate   := fun v =>
  if v ∈ c.spx then CubeCoord.free else if c.sgn v = 0 then CubeCoord.pos else CubeCoord.neg

@[simp] theorem freeSet_qCubeToCoordinate  :
    freeSet (qCubeToCoordinate c) = c.spx := by
  aesop (add simp [qCubeToCoordinate])

/-- The same admissible cells as the cube-poset quotient, expressed in coordinates. -/
def CoordinateCube (A : CommRel V) := {c : Cube V // IsSimplex A (freeSet c)}

def coordinateToQCube (c : CoordinateCube A) : QCube A where
  spx := freeSet c.1
  sgn v := match c.1 v with
    | CubeCoord.neg => 1
    | _ => 0
  isSimplex := c.2
  sgn_eq_zero v hv := by
    rw [mem_freeSet] at hv
    simp [hv]

@[simp] theorem coordinateToQCube_toCoordinate (c : CoordinateCube A) :
    qCubeToCoordinate (coordinateToQCube c) = c.1 := by
  funext v
  cases h : c.1 v <;> simp [qCubeToCoordinate, coordinateToQCube, h]

/-- The coordinate identification is an actual equivalence of cell sets. -/
def qCubeCoordinateEquiv : QCube A ≃ CoordinateCube A where
  toFun c := ⟨qCubeToCoordinate c, by simpa using c.isSimplex⟩
  invFun := coordinateToQCube
  left_inv c := by
    apply QCube.ext'
    · exact freeSet_qCubeToCoordinate c
    · intro v hv
      change (match qCubeToCoordinate c v with | CubeCoord.neg => 1 | _ => 0) = c.sgn v
      have hz : c.sgn v = 0 ∨ c.sgn v = 1 := by
        generalize c.sgn v = z
        revert z
        decide
      rcases hz with hz | hz <;> simp [qCubeToCoordinate, hv, hz]
  right_inv c := Subtype.ext (coordinateToQCube_toCoordinate c)

omit [Fintype V] in
/-- The positive corner cubes of the quotient are precisely the cubes meeting the cut. -/
theorem qCubeToCoordinate_sgn_zero  (hc : c.sgn = 0) :
    qCubeToCoordinate c = posCube c.spx := by
  funext v
  simp [qCubeToCoordinate, posCube, hc]

/-- Recover the parity sign from the actual fixed coordinate. -/
theorem qCubeToCoordinate_parity  (v : V) :
    (match qCubeToCoordinate c v with | CubeCoord.neg => (1 : ZMod 2) | _ => 0) =
      c.sgn v := congrArg (fun d : QCube A => d.sgn v) (qCubeCoordinateEquiv.left_inv c)

/-- A coordinate cube is a face of another when each coordinate of the larger cube is
 free or agrees with the smaller cube. -/
def CoordinateFace (c d : Cube V)  := ∀ v, d v = CubeCoord.free ∨ c v = d v

/-- The face order on coordinate cubes, shared by their boundary regions. -/
abbrev coordinateFaceOrder : PartialOrder (Cube V) where
  le := CoordinateFace
  le_refl c v := Or.inr rfl
  le_trans c d e hcd hde v := by
    rcases hde v with he | he
    · exact Or.inl he
    · rcases hcd v with hd | hd
      · exact Or.inl (he.symm.trans hd)
      · exact Or.inr (hd.trans he)
  le_antisymm c d hcd hdc := by
    funext v
    rcases hcd v with hd | hd
    · rcases hdc v with hc | hc
      · exact hc.trans hd.symm
      · exact hc.symm
    · exact hd

/-- The poset used in the full Davis nerve is exactly the coordinate-cube face poset. -/
theorem qCubeToCoordinate_face_iff (c d : QCube A) :
    c ≤ d ↔ CoordinateFace (qCubeToCoordinate c) (qCubeToCoordinate d) := by
  constructor
  · intro h v
    by_cases hv : v ∈ d.spx
    · simp_all [qCubeToCoordinate]
    · right
      have hvc : v ∉ c.spx := fun hc => hv (h.1 hc)
      simp [qCubeToCoordinate, hv, hvc, h.2 v hv]
  · intro h
    refine ⟨?_, ?_⟩
    · intro v hv
      have hc : qCubeToCoordinate c v = CubeCoord.free := by
        simp [qCubeToCoordinate, hv]
      have hd : qCubeToCoordinate d v = CubeCoord.free := by
        rcases h v with hd | hd
        · exact hd
        · exact hd.symm.trans hc
      have hm  := mem_freeSet.mpr hd
      simpa using hm
    · intro v hv
      have hd : qCubeToCoordinate d v ≠ CubeCoord.free := by
        intro he
        have hm := mem_freeSet.mpr he
        rw [freeSet_qCubeToCoordinate] at hm
        exact hv hm
      have he  := (h v).resolve_left hd
      rw [← qCubeToCoordinate_parity c v, ← qCubeToCoordinate_parity d v, he]

instance : PartialOrder (CoordinateCube A) :=
  @Subtype.partialOrder _ coordinateFaceOrder _

end FiniteChains.Davis








