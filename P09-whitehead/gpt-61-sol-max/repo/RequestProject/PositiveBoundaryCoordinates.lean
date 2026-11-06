import Mathlib.Tactic

import RequestProject.CutPuncturedBoundary
import RequestProject.VertexPunctureIntersection
import RequestProject.OrderComplexPi1Transfer
import RequestProject.OrderComplexRetraction
import RequestProject.OrderComplexGluing

/-! Coordinate restriction and extension on a positive three-cube's retained boundary. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

  (t : QOld A)
  (ht : t.1.sgn = 0)
include ht in
omit [Fintype V] in
theorem retainedBoundary_coordinate_outside  
    (c : RetainedProperBoundary t) {v : V} (hv : v ∉ t.1.spx) :
    qCubeToCoordinate c.1.1 v = CubeCoord.pos := by
  have hc : v ∉ c.1.1.spx := fun h => hv (c.2.le.1 h)
  have hs  := (c.2.le.2 v hv).trans (congrFun ht v)
  simp [qCubeToCoordinate, hc, hs]

theorem old_coordinate_not_all_positive (c : QOld A) :
    qCubeToCoordinate c.1 ≠ (fun _ => CubeCoord.pos) := by
  intro he
  have hspx : c.1.spx = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := congrFun he v
    simp only [qCubeToCoordinate, if_pos hv] at hh
    cases hh
  have hs : c.1.sgn = 0 := by
    funext v
    have hh := qCubeToCoordinate_parity c.1 v
    rw [he] at hh
    exact hh.symm
  exact c.2 ⟨hspx, hs⟩

include ht in
def positiveBoundaryRestriction  
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : RetainedProperBoundary t) :
    VertexPuncturedCube := by
  let f  := fun i => qCubeToCoordinate c.1.1 (e i).1
  refine ⟨f, ?_, ?_⟩
  · intro he
    have hc : qCubeToCoordinate c.1.1 = qCubeToCoordinate t.1 := by
      funext v
      by_cases hv : v ∈ t.1.spx
      · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
        have hh := congrFun he i
        have hiv  := congrArg Subtype.val hi
        change qCubeToCoordinate c.1.1 (e i).1 = CubeCoord.free at hh
        rw [hiv] at hh
        simpa only [qCubeToCoordinate, if_pos hv] using hh
      · rw [retainedBoundary_coordinate_outside t ht c hv]
        simp [qCubeToCoordinate, hv, ht]
    exact c.2.ne (Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext hc)))
  · intro he
    apply old_coordinate_not_all_positive c.1
    funext v
    by_cases hv : v ∈ t.1.spx
    · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
      have hh := congrFun he i
      have hiv  := congrArg Subtype.val hi
      change qCubeToCoordinate c.1.1 (e i).1 = CubeCoord.pos at hh
      rwa [hiv] at hh
    · classical simp_all [FiniteChains.Davis.retainedBoundary_coordinate_outside]

variable (e : Fin 3 ≃ {v : V // v ∈ t.1.spx})
variable (c : Cube (Fin 3))
include e in
def extendPositiveCoordinates 
       :=
  fun v => if hv : v ∈ t.1.spx then c (e.symm ⟨v, hv⟩) else CubeCoord.pos

include e in
omit [Fintype V] in
theorem extendPositiveCoordinates_inside 
      (i : Fin 3) :
    extendPositiveCoordinates t e c (e i).1 = c i := by simp_all [extendPositiveCoordinates]

include ht in
def positiveBoundaryExtension  
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : VertexPuncturedCube) :
    RetainedProperBoundary t := by
  classical
  let f := extendPositiveCoordinates t e c.1
  have hsub : freeSet f ⊆ t.1.spx := by
    classical grind [FiniteChains.mem_freeSet, FiniteChains.Davis.extendPositiveCoordinates.eq_1, extendPositiveCoordinates]
  let d  := coordinateToQCube ⟨f, isSimplex_subset A hsub t.1.isSimplex⟩
  have hd : qCubeToCoordinate d = f := coordinateToQCube_toCoordinate _
  have hdt : d ≤ t.1 := by
    apply (qCubeToCoordinate_face_iff d t.1).mpr
    intro v
    rw [hd, qCubeToCoordinate_sgn_zero t.1 ht]
    classical aesop (add simp [posCube, f, extendPositiveCoordinates])
  have hold : ¬ (d.spx = ∅ ∧ d.sgn = 0) := by
    rintro ⟨hspx, hs⟩
    apply c.2.2
    funext i
    have hi := extendPositiveCoordinates_inside t e c.1 i
    change f (e i).1 = c.1 i at hi
    rw [← hd] at hi
    rw [← hi]
    simp [qCubeToCoordinate, hspx, hs]
  let w : QOld A := ⟨d, hold⟩
  refine ⟨w, lt_of_le_of_ne hdt ?_⟩
  intro he
  apply c.2.1
  funext i
  have hi := extendPositiveCoordinates_inside t e c.1 i
  change f (e i).1 = c.1 i at hi
  rw [← hd] at hi
  have hraw : d = t.1 := congrArg Subtype.val he
  rw [hraw] at hi
  rw [← hi]
  simp [qCubeToCoordinate, (e i).2]

include ht in
theorem positiveBoundaryExtension_coordinates  
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : VertexPuncturedCube) :
    qCubeToCoordinate (positiveBoundaryExtension t ht e c).1.1 =
      extendPositiveCoordinates t e c.1 := coordinateToQCube_toCoordinate _

include ht in
def positiveBoundaryOrderIso  
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) :
    RetainedProperBoundary t ≃o VertexPuncturedCube where
  toFun := positiveBoundaryRestriction t ht e
  invFun := positiveBoundaryExtension t ht e
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    apply qCubeCoordinateEquiv.injective
    apply Subtype.ext
    funext v
    change qCubeToCoordinate (positiveBoundaryExtension t ht e
      (positiveBoundaryRestriction t ht e c)).1.1 v = qCubeToCoordinate c.1.1 v
    rw [positiveBoundaryExtension_coordinates]
    by_cases hv : v ∈ t.1.spx
    · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
      have hiv : (e i).1 = v := congrArg Subtype.val hi
      rw [← hiv, extendPositiveCoordinates_inside]
      rfl
    · simp_all [retainedBoundary_coordinate_outside, extendPositiveCoordinates]
  right_inv c := by
    apply Subtype.ext
    funext i
    change qCubeToCoordinate (positiveBoundaryExtension t ht e c).1.1 (e i).1 = c.1 i
    rw [positiveBoundaryExtension_coordinates, extendPositiveCoordinates_inside]
  map_rel_iff' := by
    intro c d
    change CoordinateFace (positiveBoundaryRestriction t ht e c).1
      (positiveBoundaryRestriction t ht e d).1 ↔ c.1.1 ≤ d.1.1
    rw [qCubeToCoordinate_face_iff]
    constructor
    · intro h v
      by_cases hv : v ∈ t.1.spx
      · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
        have hh := h i
        have hiv  := congrArg Subtype.val hi
        aesop
      simp_all [retainedBoundary_coordinate_outside]
    · intro h i
      exact h (e i).1

variable (hcard : t.1.spx.card = 3)
noncomputable def positiveThreeCubeCoordinates   :
    Fin 3 ≃ {v : V // v ∈ t.1.spx} :=
  (Fintype.equivFinOfCardEq (by simpa using hcard)).symm

include ht in
abbrev positiveRetainedBoundary_simplyConnected 
       :=
  FiniteChains.Comb.simplyConnected_orderCx_of_orderIso
    (FiniteChains.Davis.positiveBoundaryOrderIso t ht (FiniteChains.Davis.positiveThreeCubeCoordinates t hcard))
    FiniteChains.Davis.vertexPuncturedCube_simplyConnected

include ht in
abbrev positiveRetainedBoundary_connected 
       :=
  FiniteChains.Comb.isConnected_orderCx_of_orderIso
    (FiniteChains.Davis.positiveBoundaryOrderIso t ht (FiniteChains.Davis.positiveThreeCubeCoordinates t hcard))
    FiniteChains.Davis.vertexPuncturedCube_connected

variable (hne : t.1.spx.Nonempty)
  (ht : t.1.sgn = 0)
variable (hcard : t.1.spx.card = 3)
include hne in
abbrev positiveCutPuncturedBoundary_simplyConnected 
        :=
  FiniteChains.Davis.cutPuncturedBoundary_simplyConnected_of_retained t hne
    (FiniteChains.Davis.positiveRetainedBoundary_simplyConnected t ht hcard)

include hne in
abbrev positiveCutPuncturedBoundary_connected 
        :=
  FiniteChains.Davis.cutPuncturedBoundary_connected_of_retained t hne
    (FiniteChains.Davis.positiveRetainedBoundary_connected t ht hcard)

include hne in
def swappedCutBoundaryOrderIso   :
    {x : TruncatedCell A // x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t} ≃o
      CutPuncturedBoundary t hne where
  toFun x := ⟨x.1, x.2.2, x.2.1⟩
  invFun x := ⟨x.1, x.2.2, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

include hne in
abbrev positiveCutPuncturedBoundary_connectedIn 
        :=
  FiniteChains.Comb.connectedIn_of_isConnected
    (FiniteChains.Comb.isConnected_orderCx_of_orderIso (FiniteChains.Davis.swappedCutBoundaryOrderIso t hne)
      (FiniteChains.Davis.positiveCutPuncturedBoundary_connected t hne ht hcard))

include hne in
abbrev positiveCutPuncturedBoundary_simplyConnectedIn 
        :=
  FiniteChains.Comb.simplyConnectedIn_of_simplyConnected
    (FiniteChains.Comb.simplyConnected_orderCx_of_orderIso (FiniteChains.Davis.swappedCutBoundaryOrderIso t hne)
      (FiniteChains.Davis.positiveCutPuncturedBoundary_simplyConnected t hne ht hcard))

end FiniteChains.Davis
