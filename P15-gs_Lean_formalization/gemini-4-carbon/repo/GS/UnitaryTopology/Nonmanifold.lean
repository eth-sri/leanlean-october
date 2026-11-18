module

public import GS.UnitaryTopology.RegularChart
public import GS.UnitaryTopology.ProductRetraction
public import GS.UnitaryTopology.IndexTransport

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

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

theorem rankThreeProduct_not_euclidean_blocks (e r : ℕ) (hr : 0<r) :
    ¬ EuclideanAt ((0,rankThreeZero) : (Fin e → ℝ) × RankThreeCone (Fin r × Fin 4)) := by
  apply not_euclidean_of_retract_regular_charts (quaternionProductRetract e r)
    (Fintype.card (Fin e)+Fintype.card (Fin r × Fin 4)+2) (by simp)
  intro U hU h0
  let j : Fin r × Fin 4 := (⟨0,hr⟩,0)
  obtain ⟨p,hp,hpc⟩ := exists_regular_in_open3 (ι := Fin e) j U hU h0
  exact ⟨pivotProductChart3 (ι := Fin e) j,p,hp,hpc⟩

theorem rankThreeProduct_not_euclidean_mul_four (e r : ℕ) (hr : 0<r) :
    ¬ EuclideanAt ((0,rankThreeZero) : (Fin e → ℝ) × RankThreeCone (Fin (r*4))) := by
  let h := productRankThreeReindex e (finProdFinEquiv : Fin r × Fin 4 ≃ Fin (r*4))
  intro he
  apply rankThreeProduct_not_euclidean_blocks e r hr
  apply (euclideanAt_homeomorph h (0,rankThreeZero)).mpr
  simpa only [h,productRankThreeReindex_zero] using he

theorem rankThreeProduct_not_euclidean_of_four_dvd (e d : ℕ)
    (hd : 0<d) (hdiv : 4∣d) :
    ¬ EuclideanAt ((0,rankThreeZero) : (Fin e → ℝ) × RankThreeCone (Fin d)) := by
  obtain ⟨r,hr⟩ := hdiv
  have hd' : d=r*4 := by omega
  have hrpos : 0<r := by omega
  rw [hd']
  apply rankThreeProduct_not_euclidean_mul_four e r
  exact hrpos

end GS.UnitaryTopology
