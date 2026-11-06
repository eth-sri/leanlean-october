import Mathlib.Tactic

import GS.NonmanifoldClosure.PuncturedBall
import GS.Topology.SphereApproximation
import GS.Topology.SphereNoncontractible
import GS.Topology.BrouwerFixedPoint



/-!
# Sphere retractions determine the dimension of a punctured ball

Radial normalization turns a strict section pair for a punctured ball into a
homotopy section pair for its sphere. If the two sphere dimensions differ,
one of its two maps goes from a lower-dimensional sphere to a higher-dimensional
sphere and is nullhomotopic. The composite identity would then be nullhomotopic,
contradicting the closed-ball fixed-point theorem.

No homology computations or invariance-of-domain theorem are used.
-/

open GS.NonmanifoldClosure GS.NonmanifoldFinal GS.NonmanifoldObstruction

namespace GS.Topology

variable (m n : ℕ)

/-- Radial conversion preserves the section identity up to an explicit homotopy. -/
theorem sphere_retract_ball_dimension_of_fixedPoint 
    [BrouwerFixedPoint (EuclideanSpace ℝ (Fin m))]
    {r : ℝ} (hr : 0 < r)
    (p : ContinuousSectionPair (UnitSphere (Fin m))
      (PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r)) : n = m := by
  let a : C(UnitSphere (Fin m), PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r) :=
    ⟨p.sectionMap, p.section_continuous⟩
  let b : C(PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r, UnitSphere (Fin m)) :=
    ⟨p.retractionMap, p.retraction_continuous⟩
  let v :=
    (⟨normSphereStandard n, (normSphereStandard n).continuous⟩ :
      C(NormSphere (EuclideanSpace ℝ (Fin n)), UnitSphere (Fin n))).comp
      ⟨ballNormalize, continuous_ballNormalize r⟩
  let w :=
    (⟨ballSection hr, continuous_ballSection hr⟩ :
      C(NormSphere (EuclideanSpace ℝ (Fin n)),
        PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r)).comp
      ⟨(normSphereStandard n).symm, (normSphereStandard n).symm.continuous⟩
  let s := v.comp a
  let t := b.comp w
  have hid : ContinuousMap.Homotopic (t.comp s) (ContinuousMap.id (UnitSphere (Fin m))) := by
    refine ⟨((ContinuousMap.Homotopy.refl b).comp
      ((puncturedBallHomotopy hr).compContinuousMap a)).cast ?_ ?_⟩
    · rfl
    · apply ContinuousMap.ext
      exact p.retraction_section
  by_contra hne
  have hnull : (t.comp s).Nullhomotopic := by
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · exact (sphereMap_nullhomotopic_of_finrank_lt
        (by simpa using hnm) t).comp_left s
    · exact (sphereMap_nullhomotopic_of_finrank_lt
        (by simpa using hmn) s).comp_right t
  obtain ⟨c, hc⟩ := hnull
  have hId : (ContinuousMap.id (UnitSphere (Fin m))).Nullhomotopic :=
    ⟨c, hid.symm.trans hc⟩
  exact sphere_id_not_nullhomotopic_of_fixedPoint
    (fun f => BrouwerFixedPoint.brouwer_fixed_point f f.continuous) hId



end GS.Topology
