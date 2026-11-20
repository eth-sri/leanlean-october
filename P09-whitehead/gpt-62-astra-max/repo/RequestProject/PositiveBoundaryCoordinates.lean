module

public import RequestProject.CutPuncturedBoundary
public import RequestProject.VertexPunctureIntersection




@[expose] public section

/-! Coordinate restriction and extension on a positive three-cube's retained boundary. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

omit [Fintype V] in
theorem retainedBoundary_coordinate_outside (t : QOld A) (ht : t.1.sgn = 0)
    (c : RetainedProperBoundary t) {v : V} (hv : v ∉ t.1.spx) :
    qCubeToCoordinate c.1.1 v = CubeCoord.pos := by
  have hc : v ∉ c.1.1.spx := fun h => hv (c.2.le.1 h)
  simp [qCubeToCoordinate, hc, ((c.2.le.2 v hv).trans (congrFun ht v))]

theorem old_coordinate_not_all_positive (c : QOld A) :
    qCubeToCoordinate c.1 ≠ (fun _ => CubeCoord.pos) := by
  intro he
  have hspx : c.1.spx = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := congrFun he v
    simp_all [qCubeToCoordinate, if_pos]
  have hs : c.1.sgn = 0 := by
    funext v
    have hh := qCubeToCoordinate_parity c.1 v
    simp_all
  exact c.2 ⟨hspx, hs⟩

variable (t : QOld A)

def positiveBoundaryRestriction (ht : t.1.sgn = 0)
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : RetainedProperBoundary t) :
    VertexPuncturedCube := by
  refine ⟨(fun i => qCubeToCoordinate c.1.1 (e i).1), ?_, ?_⟩
  · intro he
    have hc : qCubeToCoordinate c.1.1 = qCubeToCoordinate t.1 := by
      funext v
      by_cases hv : v ∈ t.1.spx
      · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
        have hh := congrFun he i
        change qCubeToCoordinate _ (e i).1 = CubeCoord.free at hh
        simp_all [(congrArg Subtype.val hi), qCubeToCoordinate, if_pos]
      · rw [retainedBoundary_coordinate_outside t ht c hv]
        simp [qCubeToCoordinate, hv, ht]
    exact c.2.ne (Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext hc)))
  · intro he
    apply old_coordinate_not_all_positive c.1
    funext v
    by_cases hv : v ∈ t.1.spx
    · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
      have hh := congrFun he i
      change qCubeToCoordinate _ (e i).1 = CubeCoord.pos at hh
      simp_all
    · apply retainedBoundary_coordinate_outside <;> assumption

variable (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : Cube (Fin 3))

def extendPositiveCoordinates : Cube V :=
  fun v => if hv : v ∈ t.1.spx then c (e.symm ⟨v, hv⟩) else CubeCoord.pos

omit [Fintype V] in
theorem extendPositiveCoordinates_inside (i : Fin 3) :
    extendPositiveCoordinates t e c (e i).1 = c i := by
  simp [extendPositiveCoordinates]

variable (ht : t.1.sgn = 0) (e : Fin 3 ≃ {v : V // v ∈ t.1.spx})

variable (c : VertexPuncturedCube)

def positiveBoundaryExtension :
    RetainedProperBoundary t := by
  classical
  let f := extendPositiveCoordinates t e c.1
  have hsub : freeSet f ⊆ t.1.spx := by
    intro v hv
    by_contra hn
    simp_all [f, extendPositiveCoordinates, dif_neg]
  let d := coordinateToQCube ⟨f, isSimplex_subset A hsub t.1.isSimplex⟩
  have hd : qCubeToCoordinate d = f := coordinateToQCube_toCoordinate _
  have hdt : d ≤ t.1 := by
    apply (qCubeToCoordinate_face_iff d t.1).mpr
    intro v
    rw [hd, qCubeToCoordinate_sgn_zero t.1 ht]
    by_cases hv : v ∈ t.1.spx
    · simp [posCube, hv]
    · simp [f, extendPositiveCoordinates, posCube, hv]
  have hold : ¬ (d.spx = ∅ ∧ d.sgn = 0) := by
    rintro ⟨hspx, hs⟩
    apply c.2.2
    funext i
    have hi := extendPositiveCoordinates_inside t e c.1 i
    change f _ = c.1 i at hi
    rw [← hd] at hi
    simp_all [hi, qCubeToCoordinate, hspx, hs]
  refine ⟨(⟨d, hold⟩), lt_of_le_of_ne hdt ?_⟩
  intro he
  apply c.2.1
  funext i
  have hi := extendPositiveCoordinates_inside t e c.1 i
  change f _ = c.1 i at hi
  rw [← hd] at hi
  have hraw := congrArg Subtype.val he
  simp_all [hraw, hi, qCubeToCoordinate]

theorem positiveBoundaryExtension_coordinates :
    qCubeToCoordinate (positiveBoundaryExtension t ht e c).1.1 =
      extendPositiveCoordinates t e c.1 := coordinateToQCube_toCoordinate _

def positiveBoundaryOrderIso :
    RetainedProperBoundary t ≃o VertexPuncturedCube where
  toFun := positiveBoundaryRestriction t ht e
  invFun := positiveBoundaryExtension t ht e
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    apply qCubeCoordinateEquiv.injective
    apply Subtype.ext
    funext v
    change qCubeToCoordinate _ v = qCubeToCoordinate _ v
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
    change qCubeToCoordinate _ (e i).1 = c.1 i
    rw [positiveBoundaryExtension_coordinates, extendPositiveCoordinates_inside]
  map_rel_iff' := by
    intro c d
    change CoordinateFace _
      _ ↔ c.1.1 ≤ d.1.1
    rw [qCubeToCoordinate_face_iff]
    constructor
    · intro h v
      by_cases hv : v ∈ t.1.spx
      · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
        have hh := h i
        change qCubeToCoordinate _ (e i).1 = CubeCoord.free ∨
          qCubeToCoordinate _ (e i).1 = qCubeToCoordinate _ (e i).1 at hh
        simp_all
      · simp_all [retainedBoundary_coordinate_outside]
    · solve_by_elim

noncomputable def positiveThreeCubeCoordinates (hcard : t.1.spx.card = 3) :
    Fin 3 ≃ {v : V // v ∈ t.1.spx} :=
  (Fintype.equivFinOfCardEq (by simp_all)).symm

section

variable (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3)
include ht hcard

theorem positiveRetainedBoundary_simplyConnected :
    SimplyConnected (orderCx (RetainedProperBoundary t)) :=
  simplyConnected_orderCx_of_orderIso
    (positiveBoundaryOrderIso t ht (positiveThreeCubeCoordinates t hcard))
    vertexPuncturedCube_simplyConnected

theorem positiveRetainedBoundary_connected :
    IsConnected (orderCx (RetainedProperBoundary t)) :=
  isConnected_orderCx_of_orderIso
    (positiveBoundaryOrderIso t ht (positiveThreeCubeCoordinates t hcard))
    vertexPuncturedCube_connected

end

variable (hne : t.1.spx.Nonempty)

theorem positiveCutPuncturedBoundary_simplyConnected (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    SimplyConnected (orderCx (CutPuncturedBoundary t hne)) :=
  cutPuncturedBoundary_simplyConnected_of_retained t hne
    (positiveRetainedBoundary_simplyConnected t ht hcard)

theorem positiveCutPuncturedBoundary_connected (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    IsConnected (orderCx (CutPuncturedBoundary t hne)) :=
  cutPuncturedBoundary_connected_of_retained t hne
    (positiveRetainedBoundary_connected t ht hcard)

def swappedCutBoundaryOrderIso :
    {x : TruncatedCell A // x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t} ≃o
      CutPuncturedBoundary t hne where
  toFun x := ⟨x.1, x.2.2, x.2.1⟩
  invFun x := ⟨x.1, x.2.2, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by rfl

theorem positiveCutPuncturedBoundary_connectedIn (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    ConnectedIn (fun x : TruncatedCell A =>
      x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t) := by
  apply connectedIn_of_isConnected
  exact isConnected_orderCx_of_orderIso (swappedCutBoundaryOrderIso t hne)
    (positiveCutPuncturedBoundary_connected t hne ht hcard)

theorem positiveCutPuncturedBoundary_simplyConnectedIn (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    SimplyConnectedIn (fun x : TruncatedCell A =>
      x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t) := by
  apply simplyConnectedIn_of_simplyConnected
  exact simplyConnected_orderCx_of_orderIso (swappedCutBoundaryOrderIso t hne)
    (positiveCutPuncturedBoundary_simplyConnected t hne ht hcard)

end FiniteChains.Davis
