module

public import PottsDiscontinuity.RCMProof.DominanceAssembly
public import PottsDiscontinuity.RCMProof.XiLower
public import PottsDiscontinuity.RCMProof.FinalAssembly
public import PottsDiscontinuity.Duality.DiagonalComparison

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsDiscontinuity.RCMProof

/-- The free correlation rate is the common value of the two spectral bounds. -/
theorem rcItem3ForEveryFreeLimit_proved (h319 : contract_h319)
    (q : ℝ) (hq : 4 < q) : rcItem3ForEveryFreeLimit q hq := by
  intro μ hμ lam hlam hcosh
  let Q : Set.Ici (1 : ℝ) := ⟨q, Set.mem_Ici.2 (by linarith)⟩
  let θ := FK.criticalParameters Q
  obtain ⟨ξ, _, hrot, hdiag⟩ := CorrLength.rotated_correlation_rate_exists_for_limit θ μ hμ
  have hEq :=
    tendsto_nhds_unique hrot (TorusRC.tendsto_inverseCorrelationLength Q)
  rw [hEq] at hdiag
  let L := Real.arcosh (Real.sqrt q / 2)
  obtain ⟨hL, hcoshL⟩ := arcosh_pos_of_gt4 q hq
  have hLam : lam = L := Real.cosh_injOn hlam.le hL.le (hcosh.trans hcoshL.symm)
  obtain ⟨S, _, hS, _, hpos, _⟩ := identity44 L hL
  have hlo := xi_inverse_ge_critical_rate Q hq (h319 Q) hS
  have hξ := hpos.trans_le hlo
  have hr : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (Duality.twoPoint μ (diagonalSite n)))
      atTop (𝓝 (TorusRC.inverseCorrelationLength Q)) := by
    simpa only [TorusExploration.corrLength_connectionEvent_eq, Duality.twoPoint,
      one_div, div_eq_mul_inv, neg_mul, mul_neg, one_mul, mul_one, mul_comm] using! hdiag
  have hno : μ (Duality.infiniteClusterAt (0,0)) = 0 := by
    have := hμ.1
    obtain ⟨C, c, _, hc, hd⟩ := Duality.free_exponential_decay_of_pos_diagonal_rate θ μ hμ _ hξ hr
    exact Duality.infiniteClusterAt_zero_of_exponential_decay μ C c hc hd
  have hhi := rc_xi_inverse_le_critical_rate Q hq μ hμ _ hdiag hξ hno hS hpos
  rw [le_antisymm hhi hlo] at hr
  rw [hLam]
  exact ⟨S, hS, hr⟩

end PottsDiscontinuity.RCMProof
