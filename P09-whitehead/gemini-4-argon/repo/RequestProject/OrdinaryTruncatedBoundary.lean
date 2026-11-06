module

public import RequestProject.TruncatedCubePoset
public import RequestProject.TruncatedCellIncidence
public import RequestProject.PuncturedCubeBoundary
public import RequestProject.OrderComplexPi1Transfer

@[expose] public section

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [Fintype V] [DecidableEq V] {A : CommRel V}

def OldPuncturedBoundary (f t : QOld A) :=
  {c : TruncatedCell A // c < Sum.inl t ∧ c ≠ Sum.inl f}

instance (f t : QOld A) : PartialOrder (OldPuncturedBoundary f t) := Subtype.partialOrder _

def boundaryOldCell {f t : QOld A} (ht : t.1.sgn ≠ 0) : OldPuncturedBoundary f t → QOld A
  | ⟨Sum.inl d, _⟩ => d
  | ⟨Sum.inr _, hc⟩ => False.elim (ht hc.1.le.2)

omit [Fintype V] in
theorem boundaryOldCell_eq {f t : QOld A} (ht : t.1.sgn ≠ 0) :
    ∀ c : OldPuncturedBoundary f t, c.1 = Sum.inl (boundaryOldCell ht c)
  | ⟨Sum.inl _, _⟩ => rfl
  | ⟨Sum.inr _, hc⟩ => False.elim (ht hc.1.le.2)

def ordinaryBoundaryToCoordinate {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (j : V) (b : CubeCoord) (hf : qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1))
    (c : OldPuncturedBoundary f t) : PuncturedCubeFace (qCubeToCoordinate t.1) j b :=
  let d := boundaryOldCell ht c
  have hd := boundaryOldCell_eq ht c
  ⟨qCubeToCoordinate d.1, (qCubeToCoordinate_face_iff d.1 t.1).mp (by have h := c.2.1.le; rwa [hd] at h),
    fun he => c.2.1.ne (hd.trans (congrArg Sum.inl (Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext he))))),
    fun he => c.2.2 (hd.trans (congrArg Sum.inl (Subtype.ext (qCubeCoordinateEquiv.injective (Subtype.ext (he.trans hf.symm))))))⟩

def coordinateBoundaryToOrdinary {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (j : V) (b : CubeCoord) (hf : qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1))
    (c : PuncturedCubeFace (qCubeToCoordinate t.1) j b) : OldPuncturedBoundary f t := by
  let d : QCube A := coordinateToQCube ⟨c.1, isSimplex_subset A (fun v hv => by
    have hvc := mem_freeSet.mp hv
    have hvt : v ∈ freeSet (qCubeToCoordinate t.1) :=
      (c.2.1 v).elim mem_freeSet.mpr fun he => mem_freeSet.mpr (he.symm.trans hvc)
    simpa using hvt) t.1.isSimplex⟩
  have hd : qCubeToCoordinate d = c.1 := coordinateToQCube_toCoordinate _
  have hdt : d ≤ t.1 := (qCubeToCoordinate_face_iff d t.1).mpr (hd ▸ c.2.1)
  let w : QOld A := ⟨d, fun ⟨_, hz⟩ => ht (qCube_sgn_zero_of_face hdt hz)⟩
  exact ⟨Sum.inl w,
    lt_of_le_of_ne hdt fun he => c.2.2.1 (hd.symm.trans (congrArg (fun x : QOld A => qCubeToCoordinate x.1) (Sum.inl.inj he))),
    fun he => c.2.2.2 (hd.symm.trans ((congrArg (fun x : QOld A => qCubeToCoordinate x.1) (Sum.inl.inj he)).trans hf))⟩

def ordinaryTruncatedBoundaryOrderIso {f t : QOld A} (ht : t.1.sgn ≠ 0)
    (j : V) (b : CubeCoord) (hf : qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1)) :
    OldPuncturedBoundary f t ≃o PuncturedCubeFace (qCubeToCoordinate t.1) j b where
  toFun := ordinaryBoundaryToCoordinate ht j b hf
  invFun := coordinateBoundaryToOrdinary ht j b hf
  left_inv c := Subtype.ext <| by
    rw [boundaryOldCell_eq ht (coordinateBoundaryToOrdinary ht j b hf
      (ordinaryBoundaryToCoordinate ht j b hf c)), boundaryOldCell_eq ht c]
    exact congrArg Sum.inl (Subtype.ext (qCubeCoordinateEquiv.injective
      (Subtype.ext (coordinateToQCube_toCoordinate _))))
  right_inv c := Subtype.ext (coordinateToQCube_toCoordinate _)
  map_rel_iff' := by
    intro c d
    change CoordinateFace (qCubeToCoordinate (boundaryOldCell ht c).1)
      (qCubeToCoordinate (boundaryOldCell ht d).1) ↔ c.1 ≤ d.1
    rw [boundaryOldCell_eq ht c, boundaryOldCell_eq ht d]
    exact (qCubeToCoordinate_face_iff (boundaryOldCell ht c).1 (boundaryOldCell ht d).1).symm

theorem exists_facet_coordinates_of_inc {L : ASC V} (f t : QOld A)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate f.1))) :
    ∃ j : V, ∃ b : CubeCoord, b ≠ CubeCoord.free ∧
      qCubeToCoordinate t.1 j = CubeCoord.free ∧
      qCubeToCoordinate f.1 = coordinateFix j b (qCubeToCoordinate t.1) := by
  classical
  have hm : qCubeToCoordinate t.1 ∈ cofaces L (qCubeToCoordinate f.1) := by
    simp only [spineInc] at hi
    split at hi
    · exact hi
    · exact (Finset.notMem_empty _ hi).elim
  obtain ⟨j, hj, _, he⟩ := mem_cofaces.mp hm
  refine ⟨j, qCubeToCoordinate f.1 j, hj, by rw [he]; exact Function.update_self _ _ _, funext fun v => ?_⟩
  by_cases hv : v = j
  · subst v; exact (Function.update_self j (qCubeToCoordinate f.1 j) (qCubeToCoordinate t.1)).symm
  · simp only [coordinateFix, Function.update_of_ne hv, he]

def swappedBoundaryOrderIso (f t : QOld A) :
    {x : TruncatedCell A // x ≠ Sum.inl f ∧ x < Sum.inl t} ≃o OldPuncturedBoundary f t where
  toFun x := ⟨x.1, x.2.2, x.2.1⟩
  invFun x := ⟨x.1, x.2.2, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem ordinaryTruncatedBoundary_connectedIn {L : ASC V} {f t : QOld A}
    (ht : t.1.sgn ≠ 0)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate f.1))) :
    ConnectedIn (fun x : TruncatedCell A => x ≠ Sum.inl f ∧ x < Sum.inl t) := by
  obtain ⟨j, b, hb, htj, hf⟩ := exists_facet_coordinates_of_inc f t hi
  exact connectedIn_of_isConnected (isConnected_orderCx_of_orderIso (swappedBoundaryOrderIso f t)
    (isConnected_orderCx_of_orderIso (ordinaryTruncatedBoundaryOrderIso ht j b hf)
      (ordinary_puncturedCubeBoundary_connected _ j b hb htj)))

theorem ordinaryTruncatedBoundary_simplyConnectedIn {L : ASC V} {f t : QOld A}
    (ht : t.1.sgn ≠ 0)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate f.1))) :
    SimplyConnectedIn (fun x : TruncatedCell A => x ≠ Sum.inl f ∧ x < Sum.inl t) := by
  obtain ⟨j, b, hb, htj, hf⟩ := exists_facet_coordinates_of_inc f t hi
  exact simplyConnectedIn_of_simplyConnected
    (simplyConnected_orderCx_of_orderIso (swappedBoundaryOrderIso f t)
      (simplyConnected_orderCx_of_orderIso (ordinaryTruncatedBoundaryOrderIso ht j b hf)
        (ordinary_puncturedCubeBoundary_simplyConnected _ j b hb htj)))

end FiniteChains.Davis
