module

public import GS.NonmanifoldFinal.SphereCoordinates
public import GS.NonmanifoldObstruction.PuncturedNeighbourhood

@[expose] public section



/-!
# Transport the existing sphere retract to all finite column sets

The d+2 convention of the old section is eliminated by an explicit equivalence.
The resulting retract has a genuine Fin-indexed Euclidean sphere as its source.
-/
noncomputable section
open GS GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

variable {A A' B B' X Y : Type*}
  [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B]
  [TopologicalSpace B'] [TopologicalSpace X] [TopologicalSpace Y]

/-- Transport BOTH maps, including the left-inverse identity. -/
def transportSectionPair (p : ContinuousSectionPair A B)
    (hA : A' ≃ₜ A) (hB : B ≃ₜ B') : ContinuousSectionPair A' B' where
  sectionMap a := hB (p.sectionMap (hA a))
  retractionMap b := hA.symm (p.retractionMap (hB.symm b))
  section_continuous := by have := p.section_continuous; fun_prop
  retraction_continuous := by have := p.retraction_continuous; fun_prop
  retraction_section a := by simp [p.retraction_section]

/-- Remove a SINGLE marked point from an open subset. -/
abbrev PuncturedIn (U : Set X) (x : X) := {p : X // p ∈ U ∧ p ≠ x}

def puncturedImage (h : X ≃ₜ Y) (U : Set X) (x : X) :
    PuncturedIn U x ≃ₜ PuncturedIn (h '' U) (h x) where
  toFun p := ⟨h p.val,by grind, by aesop⟩
  invFun p := ⟨h.symm p.val,by aesop, by aesop⟩
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- No restriction to an artificially selected cone branch occurs here. -/
theorem every_punctured_cone_open_has_standard_sphere_retract
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (hκ : 2 ≤ Fintype.card κ) (U : Set (ConeSpace ι κ))
    (hU : IsOpen U) (hzero : productZero ∈ U) :
    Nonempty (ContinuousSectionPair
      (UnitSphere (Fin (Fintype.card ι + 2))) (PuncturedIn U productZero)) := by
  obtain ⟨p⟩ := punctured_open_has_sphere_retract (ι := ι) _ _ ((coneCoordinatesExtra hκ).isOpenMap U hU)
    ⟨_, hzero, rfl⟩
  exact ⟨transportSectionPair p planeSphereFinHomeomorph.symm (puncturedImage (coneCoordinatesExtra hκ) U productZero).symm⟩

end GS.NonmanifoldFinal
