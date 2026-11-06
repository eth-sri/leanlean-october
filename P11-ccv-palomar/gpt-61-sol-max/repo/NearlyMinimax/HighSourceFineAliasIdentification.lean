module

public import NearlyMinimax.HighSourceRawDecomposition
public import NearlyMinimax.OrdinaryFineAliasSpatialEnergy

@[expose] public section

/-! Exact identification of every genuine ordinary fine signed packet
with the spatial all-count alias action used by the energy bounds. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem higherBandFirstAction_fine_eq_aliasRawAction {d n : ℕ}
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    (hL : 0 < L) (hT : 1 ≤ T) (r M D q : ℕ) (hr : 2 ≤ r)
    (hD : 1 ≤ D) (hnD : n ≤ D) (C a V η : ℝ)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    higherBandFirstAction ad bd lam L T r M D q C true U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) =
      ordinaryFineAliasRawAction ad bd lam L T M r q C a V η U p g w c y := by
  rw [higherBandFirstAction_actual_count_expansion ad bd lam L T ha hab hlam hL hT
    r M D q hr hD hnD C true U hU p hp c]
  simp only [ordinaryFineAliasRawAction, higherBandActualMatrix, ite_true]

end NearlyMinimax
