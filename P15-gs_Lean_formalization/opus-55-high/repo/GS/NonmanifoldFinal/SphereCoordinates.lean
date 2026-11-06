module

public import GS.NonmanifoldFinal.FiniteCoordinates
public import GS.Topology.EuclideanSphere

@[expose] public section



/-!
# Identify the explicit auxiliary sphere with a genuine Euclidean unit sphere

The plain finite function type has its default sup norm. EuclideanSpace carries
its L2 norm. The homeomorphism below explicitly passes through EuclideanSpace.equiv
and proves the norm-square identity; it does not identify these two norms.
-/
noncomputable section
open GS GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

variable {ι : Type*} [Fintype ι]


/-- The auxiliary sphere is exactly a standard Fin-indexed sphere. -/
def planeSphereFinHomeomorph :
    PlaneSphere ι ≃ₜ UnitSphere (Fin (Fintype.card ι + 2)) :=
  ((sumCoordinates.trans (EuclideanSpace.equiv (ι ⊕ Fin 2) ℝ).symm.toHomeomorph).subtype fun p => by
    rw [mem_sphere_zero_iff_norm, ← pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero, EuclideanSpace.real_norm_sq_eq]
    aesop : PlaneSphere ι ≃ₜ UnitSphere (ι ⊕ Fin 2)).trans ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    ((Fintype.equivFin (ι ⊕ Fin 2)).trans (Equiv.cast (by simp)))).toHomeomorph.subtype (by simp))

end GS.NonmanifoldFinal
