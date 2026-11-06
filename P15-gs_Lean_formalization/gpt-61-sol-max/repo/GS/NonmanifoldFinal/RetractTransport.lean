
import GS.NonmanifoldFinal.FiniteCoordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension
import GS.Topology.IsolatedRetraction



/-!
# Transport the existing sphere retract to all finite column sets

The d+2 convention of the old section is eliminated by an explicit equivalence.
The resulting retract has a genuine Fin-indexed Euclidean sphere as its source.
-/
open GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

/-- No restriction to an artificially selected cone branch occurs here. -/
theorem every_punctured_cone_open_has_standard_sphere_retract
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (hκ : 2 ≤ Fintype.card κ) (U : Set (ConeSpace ι κ))
    (hU : IsOpen U) (hzero : productZero ∈ U) :
    Nonempty (ContinuousSectionPair
      (UnitSphere (Fin (Fintype.card ι + 2))) (PuncturedIn U productZero)) := by
  let d := Fintype.card κ - 2
  let e : ConeSpace ι κ ≃ₜ ConeSpace ι (Fin (d+2)) := coneCoordinatesExtra hκ
  let V := e '' U
  have he0 : e productZero = productZero := rfl
  let h : PlaneSpace ι ≃L[ℝ] EuclideanSpace ℝ (Fin (Fintype.card ι + 2)) :=
    ContinuousLinearEquiv.ofFinrankEq (by aesop)
  have h0 := map_zero h
  let r : GS.UnitaryTopology.IsolatedEuclideanRetract
      (ConeSpace ι (Fin (d+2))) productZero (Fintype.card ι + 2) := {
    sectionMap := productSection d ∘ h.symm
    projectionMap := h ∘ productRetraction
    section_continuous := (continuous_productSection d).comp h.symm.continuous
    projection_continuous := h.continuous.comp continuous_productRetraction
    projection_section := fun x => by simp
    section_zero := by aesop
    projection_zero_iff := by
      intro p
      change h (productRetraction p) = 0 ↔ _
      rw [← h0,h.injective.eq_iff]
      rcases p with ⟨x,W⟩
      change (x,coneToPlane W) = (0,0) ↔ (x,W) = (0,coneZero)
      simp only [Prod.mk.injEq,coneToPlane_zero_iff] }
  obtain ⟨p⟩ := r.punctured_sphere V (e.isOpenMap U hU) ⟨productZero,hzero,he0⟩
  have hp : PuncturedIn U productZero ≃ₜ PuncturedIn V productZero := by
    have hh := puncturedImage e U productZero
    
    exact hh
  exact ⟨transportSectionPair p (Homeomorph.refl _) hp.symm⟩

end GS.NonmanifoldFinal
