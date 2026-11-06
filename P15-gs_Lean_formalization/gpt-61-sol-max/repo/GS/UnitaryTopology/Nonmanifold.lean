
import GS.UnitaryTopology.RegularChart
import GS.UnitaryTopology.ProductRetraction
import GS.UnitaryTopology.IndexTransport



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
open GS.NonmanifoldFinal
namespace GS.UnitaryTopology

variable (e r d : ℕ)

theorem rankThreeProduct_not_euclidean_blocks  (hr : 0<r) :
    ¬ EuclideanAt ((0,rankThreeZero) : (Fin e → ℝ) × RankThreeCone (Fin r × Fin 4)) := by
  apply GS.NonmanifoldTopology.not_euclidean_of_sphereRetractions
    (fun U hU hx _ => (quaternionProductRetract e r).punctured_sphere U hU hx)
    (Fintype.card (Fin e)+Fintype.card (Fin r × Fin 4)+2) (by simp)
  intro U hU h0
  let j : Fin r × Fin 4 := (⟨0,hr⟩,0)
  obtain ⟨p,hp,hpc⟩ := GS.Topology.exists_regular 2 (ι := Fin e) j U hU h0
  exact ⟨GS.Topology.rankPivotChart 2 (ι := Fin e) j,p,hp,hpc⟩

theorem rankThreeProduct_not_euclidean_of_four_dvd 
    (hd : 0<d) (hdiv : 4∣d) :
    ¬ EuclideanAt ((0,rankThreeZero) : (Fin e → ℝ) × RankThreeCone (Fin d)) := by
  obtain ⟨r,rfl⟩ := hdiv
  have hr : 0<r := by omega
  rw [Nat.mul_comm 4]
  let h := productRankThreeReindex e (finProdFinEquiv : Fin r × Fin 4 ≃ Fin (r*4))
  intro he
  apply rankThreeProduct_not_euclidean_blocks e r hr
  apply (euclideanAt_homeomorph h (0,rankThreeZero)).mpr
  exact he

end GS.UnitaryTopology
