module

public import RequestProject.CutPuncturedBoundary
public import RequestProject.VertexPunctureIntersection
public import RequestProject.OrderComplexPi1Transfer
public import RequestProject.OrderComplexRetraction
public import RequestProject.OrderComplexGluing

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

omit [Fintype V] in
theorem retainedBoundary_coordinate_outside (t : QOld A) (ht : t.1.sgn = 0)
    (c : RetainedProperBoundary t) {v : V} (hv : v ∉ t.1.spx) :
    qCubeToCoordinate c.1.1 v = CubeCoord.pos := by
  have hc : v ∉ c.1.1.spx := fun h => hv (c.2.le.1 h)
  have hs : c.1.1.sgn v = 0 := (c.2.le.2 v hv).trans (congrFun ht v)
  simp [qCubeToCoordinate, hc, hs]

def positiveBoundaryRestriction (t : QOld A) (ht : t.1.sgn = 0)
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : RetainedProperBoundary t) :
    VertexPuncturedCube := by
  refine ⟨fun i => qCubeToCoordinate c.1.1 (e i).1, fun he => ?_, fun he => ?_⟩
  · have hc : qCubeToCoordinate c.1.1 = qCubeToCoordinate t.1 := funext fun v => by
      by_cases hv : v ∈ t.1.spx
      · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
        have hh : qCubeToCoordinate c.1.1 (e i).1 = CubeCoord.free := congrFun he i
        rw [congrArg Subtype.val hi] at hh
        simpa only [qCubeToCoordinate, if_pos hv] using hh
      · rw [retainedBoundary_coordinate_outside t ht c hv]
        simp [qCubeToCoordinate, hv, ht]
    exact c.2.ne (Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext hc)))
  · have hall : qCubeToCoordinate c.1.1 = fun _ => CubeCoord.pos := funext fun v => by
      by_cases hv : v ∈ t.1.spx
      · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
        have hh : qCubeToCoordinate c.1.1 (e i).1 = CubeCoord.pos := congrFun he i
        rwa [congrArg Subtype.val hi] at hh
      · exact retainedBoundary_coordinate_outside t ht c hv
    exact c.1.2 ⟨Finset.eq_empty_iff_forall_notMem.mpr (fun v hv => by
        have hh := congrFun hall v; simp only [qCubeToCoordinate, if_pos hv] at hh; cases hh),
      funext fun v => by
        have hh := qCubeToCoordinate_parity c.1.1 v; rw [hall] at hh; exact hh.symm⟩

def extendPositiveCoordinates (t : QOld A)
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : Cube (Fin 3)) : Cube V :=
  fun v => if hv : v ∈ t.1.spx then c (e.symm ⟨v, hv⟩) else CubeCoord.pos

omit [Fintype V] in
theorem extendPositiveCoordinates_inside (t : QOld A)
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : Cube (Fin 3)) (i : Fin 3) :
    extendPositiveCoordinates t e c (e i).1 = c i := by
  simp [extendPositiveCoordinates, (e i).2]

def positiveBoundaryExtension (t : QOld A) (ht : t.1.sgn = 0)
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) (c : VertexPuncturedCube) :
    RetainedProperBoundary t := by
  classical
  let f := extendPositiveCoordinates t e c.1
  let d : QCube A := coordinateToQCube ⟨f, isSimplex_subset A (fun v hv => by
    by_contra hn
    have hh := mem_freeSet.mp hv
    simp only [f, extendPositiveCoordinates, dif_neg hn] at hh; cases hh) t.1.isSimplex⟩
  have hd : qCubeToCoordinate d = f := coordinateToQCube_toCoordinate _
  have hdt : d ≤ t.1 := (qCubeToCoordinate_face_iff d t.1).mpr fun v => by
    rw [hd, qCubeToCoordinate_sgn_zero t.1 ht]
    by_cases hv : v ∈ t.1.spx
    · exact .inl (by simp [posCube, hv])
    · exact .inr (by simp [f, extendPositiveCoordinates, posCube, hv])
  let w : QOld A := ⟨d, fun ⟨hspx, hs⟩ => c.2.2 (funext fun i => by
    have hi : f (e i).1 = c.1 i := extendPositiveCoordinates_inside t e c.1 i
    rw [← hd] at hi; rw [← hi]; simp [qCubeToCoordinate, hspx, hs])⟩
  refine ⟨w, lt_of_le_of_ne hdt fun he => c.2.1 (funext fun i => ?_)⟩
  have hi : f (e i).1 = c.1 i := extendPositiveCoordinates_inside t e c.1 i
  have hraw : d = t.1 := congrArg Subtype.val he
  rw [← hd, hraw] at hi; rw [← hi]
  simp [qCubeToCoordinate, (e i).2]

def positiveBoundaryOrderIso (t : QOld A) (ht : t.1.sgn = 0)
    (e : Fin 3 ≃ {v : V // v ∈ t.1.spx}) :
    RetainedProperBoundary t ≃o VertexPuncturedCube where
  toFun := positiveBoundaryRestriction t ht e
  invFun := positiveBoundaryExtension t ht e
  left_inv c := Subtype.ext <| Subtype.ext <| qCubeCoordinateEquiv.injective <|
    Subtype.ext <| funext fun v => by
      change qCubeToCoordinate (positiveBoundaryExtension t ht e
        (positiveBoundaryRestriction t ht e c)).1.1 v = qCubeToCoordinate c.1.1 v
      rw [show qCubeToCoordinate (positiveBoundaryExtension t ht e
          (positiveBoundaryRestriction t ht e c)).1.1 =
        extendPositiveCoordinates t e (positiveBoundaryRestriction t ht e c).1 from
        coordinateToQCube_toCoordinate _]
      by_cases hv : v ∈ t.1.spx
      · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
        have hiv : (e i).1 = v := congrArg Subtype.val hi
        rw [← hiv, extendPositiveCoordinates_inside]; rfl
      · rw [retainedBoundary_coordinate_outside t ht c hv]
        simp [extendPositiveCoordinates, hv]
  right_inv c := Subtype.ext <| funext fun i => by
    change qCubeToCoordinate (positiveBoundaryExtension t ht e c).1.1 (e i).1 = c.1 i
    rw [show qCubeToCoordinate (positiveBoundaryExtension t ht e c).1.1 =
      extendPositiveCoordinates t e c.1 from coordinateToQCube_toCoordinate _,
      extendPositiveCoordinates_inside]
  map_rel_iff' := by
    intro c d
    change CoordinateFace (positiveBoundaryRestriction t ht e c).1
      (positiveBoundaryRestriction t ht e d).1 ↔ c.1.1 ≤ d.1.1
    rw [qCubeToCoordinate_face_iff]
    refine ⟨fun h v => ?_, fun h i => h (e i).1⟩
    by_cases hv : v ∈ t.1.spx
    · obtain ⟨i, hi⟩ := e.surjective ⟨v, hv⟩
      have hh : qCubeToCoordinate d.1.1 (e i).1 = CubeCoord.free ∨
          qCubeToCoordinate c.1.1 (e i).1 = qCubeToCoordinate d.1.1 (e i).1 := h i
      rwa [congrArg Subtype.val hi] at hh
    · exact .inr ((retainedBoundary_coordinate_outside t ht c hv).trans
        (retainedBoundary_coordinate_outside t ht d hv).symm)

noncomputable def positiveThreeCubeCoordinates (t : QOld A) (hcard : t.1.spx.card = 3) :
    Fin 3 ≃ {v : V // v ∈ t.1.spx} :=
  (Fintype.equivFinOfCardEq (by simpa using hcard)).symm

def swappedCutBoundaryOrderIso (t : QOld A) (hne : t.1.spx.Nonempty) :
    {x : TruncatedCell A // x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t} ≃o
      CutPuncturedBoundary t hne where
  toFun x := ⟨x.1, x.2.2, x.2.1⟩
  invFun x := ⟨x.1, x.2.2, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem positiveCutPuncturedBoundary_connectedIn (t : QOld A)
    (hne : t.1.spx.Nonempty) (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    ConnectedIn (fun x : TruncatedCell A =>
      x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t) :=
  connectedIn_of_isConnected (isConnected_orderCx_of_orderIso (swappedCutBoundaryOrderIso t hne)
    (cutPuncturedBoundary_connected_of_retained t hne
      (isConnected_orderCx_of_orderIso
        (positiveBoundaryOrderIso t ht (positiveThreeCubeCoordinates t hcard))
        vertexPuncturedCube_connected)))

theorem positiveCutPuncturedBoundary_simplyConnectedIn (t : QOld A)
    (hne : t.1.spx.Nonempty) (ht : t.1.sgn = 0) (hcard : t.1.spx.card = 3) :
    SimplyConnectedIn (fun x : TruncatedCell A =>
      x ≠ Sum.inr (fullCutCell t hne) ∧ x < Sum.inl t) :=
  simplyConnectedIn_of_simplyConnected
    (simplyConnected_orderCx_of_orderIso (swappedCutBoundaryOrderIso t hne)
      (cutPuncturedBoundary_simplyConnected_of_retained t hne
        (simplyConnected_orderCx_of_orderIso
          (positiveBoundaryOrderIso t ht (positiveThreeCubeCoordinates t hcard))
          vertexPuncturedCube_simplyConnected)))

end FiniteChains.Davis
