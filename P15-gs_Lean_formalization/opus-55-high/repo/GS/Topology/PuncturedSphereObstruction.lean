module

public import GS.NonmanifoldClosure.PuncturedBall
public import GS.Topology.SphereApproximation
public import GS.Topology.SphereNoncontractible

@[expose] public section



/-!
# Sphere retractions determine the dimension of a punctured ball

Radial normalization turns a strict section pair for a punctured ball into a
homotopy section pair for its sphere. If the two sphere dimensions differ,
one of its two maps goes from a lower-dimensional sphere to a higher-dimensional
sphere and is nullhomotopic. The composite identity would then be nullhomotopic,
contradicting the closed-ball fixed-point theorem.

No homology computations or invariance-of-domain theorem are used.
-/

noncomputable section

open GS.NonmanifoldClosure GS.NonmanifoldFinal GS.NonmanifoldObstruction

namespace GS.Topology

theorem sphere_retract_ball_dimension (m n : ℕ) {r : ℝ} (hr : 0 < r)
    (p : ContinuousSectionPair (UnitSphere (Fin m))
      (PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r)) : n = m := by
  let a : C(UnitSphere (Fin m), PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r) := ⟨_, p.section_continuous⟩
  let b : C(PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r, UnitSphere (Fin m)) := ⟨_, p.retraction_continuous⟩
  let v : C(PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r, UnitSphere (Fin n)) :=
    ⟨_, (normSphereStandard n).continuous.comp (continuous_ballNormalize r)⟩
  let w : C(UnitSphere (Fin n), PuncturedNormBall (EuclideanSpace ℝ (Fin n)) r) :=
    ⟨_, (continuous_ballSection hr).comp (normSphereStandard n).symm.continuous⟩
  have hid : ((b.comp w).comp (v.comp a)).Homotopic (.id _) := by
    convert ((ContinuousMap.Homotopic.refl b).comp ⟨puncturedBallHomotopy hr⟩).comp (.refl a) using 1
    · rfl
    · ext x : 1; exact (p.retraction_section x).symm
  by_contra hne
  obtain ⟨c, hc⟩ : ((b.comp w).comp (v.comp a)).Nullhomotopic := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact (sphereMap_nullhomotopic_of_finrank_lt (by simp_all) _).comp_left _
    · exact (sphereMap_nullhomotopic_of_finrank_lt (by simp_all) _).comp_right _
  exact sphere_id_not_nullhomotopic ⟨c, hid.symm.trans hc⟩

end GS.Topology
