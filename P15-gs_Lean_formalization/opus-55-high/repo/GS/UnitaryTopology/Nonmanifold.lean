module

public import GS.NonmanifoldClosure.RegularConeChart
public import GS.UnitaryTopology.QuaternionRetraction
public import GS.UnitaryTopology.ProductRetraction
public import GS.UnitaryTopology.IndexTransport

@[expose] public section


/-!
# Unconditional topological obstruction at widths divisible by four

This is a topological, not differentiable, conclusion. A hypothetical vertex
chart would have dimension e+4r from an explicit Clifford sphere retract, but
its overlapping regular chart has dimension e+4r+2. The contradiction uses
the already proved sphere-dimension theorem. No homology profile, manifold
obstruction, or local GS-family model is assumed.

The present mechanism covers positive widths divisible by four. Its transfer
to the unitary GS matrix family requires the separate local-model theorem.
-/
noncomputable section
open Matrix GS GS.NonmanifoldObstruction GS.NonmanifoldFinal GS.NonmanifoldClosure
namespace GS.UnitaryTopology

theorem rankThreeProduct_not_euclidean_of_four_dvd (e d : ℕ)
    (hd : 0<d) (hdiv : 4∣d) :
    ¬ EuclideanAt ((0,rankThreeZero) : (Fin e → ℝ) × RankThreeCone (Fin d)) := by
  obtain ⟨r,rfl⟩ := hdiv
  intro he
  refine not_euclidean_of_retract_regular_charts
    { sectionMap x := (((pairCoordinatesEuclidean e r).symm x).1, firstRowSection ((pairCoordinatesEuclidean e r).symm x).2)
      projectionMap p := pairCoordinatesEuclidean e r (p.1, quaternionContraction p.2.val)
      section_continuous := by have := continuous_firstRowSection (κ := Fin r × Fin 4); fun_prop
      projection_continuous := by have := continuous_quaternionContraction r; fun_prop
      projection_section x := by simp
      section_zero := by
        simp [(pairCoordinatesEuclidean e r).symm_apply_eq.mpr (pairCoordinatesEuclidean_zero e r).symm]
      projection_zero_iff p := by
        rw [← pairCoordinatesEuclidean_zero e r, (pairCoordinatesEuclidean e r).injective.eq_iff]
        simp [Prod.ext_iff, quaternionContraction_zero_iff] }
    (Fintype.card (Fin e)+Fintype.card (Fin r × Fin 4)+2) (by simp) (fun U hU h0 => ?_)
    ((euclideanAt_homeomorph (productRankThreeReindex e (finProdFinEquiv.trans (finCongr (mul_comm r 4))))
      (0,rankThreeZero)).mpr (by aesop))
  obtain ⟨p,hp,hpc⟩ := exists_regular_in_open (ι := Fin e) ((⟨0,by omega⟩, 0) : Fin r × Fin 4) U hU h0
  grind

end GS.UnitaryTopology
