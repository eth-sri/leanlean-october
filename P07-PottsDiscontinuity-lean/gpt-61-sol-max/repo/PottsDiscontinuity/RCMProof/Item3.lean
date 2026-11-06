module
public import Mathlib

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.RCMProof.DominanceAssembly
public import PottsDiscontinuity.RCMProof.FinalAssembly
public import PottsDiscontinuity.RCMProof.Cor313Adapters
public import PottsDiscontinuity.RCMProof.TorusRCAdapters
public import PottsDiscontinuity.TorusExploration.Contract

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.RCMProof



/-- Theorem 1.2 item 3 for every free critical box limit, using the rotated
lattice rate bridge and the two matching bounds on the inverse correlation
length. -/
theorem rcItem3ForEveryFreeLimit_proved
    (hW21h319 : contract_h319)
    (q : ℝ) (hq : 4 < q) : rcItem3ForEveryFreeLimit q hq := by
  intro μ hμ lam hlam hcosh
  let qI : Set.Ici (1 : ℝ) := ⟨q, le_trans (by norm_num ) hq.le⟩
  
  
  
  
  
  obtain ⟨aInf, haInf, _hrot, hdiag⟩ :=
    CorrLength.rotated_correlation_rate_exists_for_limit
      (FK.criticalParameters qI) μ (by
                                      assumption)
  let ξinv  := aInf / 2
  
  
  
  
  obtain ⟨Slo, hSlo, hLower⟩ := xi_inverse_ge_critical_rate
     contract_cor313_i_proved   contract_cor313_ii_proved   contract_eq315_proved  qI (hW21h319 qI) hq μ (by
                                            assumption) ξinv  hdiag 
  obtain ⟨Shi, hShi, hUpper⟩ := rc_xi_inverse_le_critical_rate
     contract_cor313_i_proved   contract_cor313_ii_proved   contract_cor313_iii_proved   contract_eq315_proved   TorusExploration.contract_eq316 
    qI (hW21h319 qI) hq μ (by
                     assumption) ξinv  hdiag 
  have hSsame  := tendsto_nhds_unique hSlo hShi
  have hxi : ξinv = Real.arcosh (Real.sqrt q / 2) + 2 * Slo := by
    linarith
  obtain ⟨hlam0, hcosh0⟩ := arcosh_pos_of_gt4 q hq
  have hcoshArc : Real.cosh (Real.arcosh (Real.sqrt q / 2)) = Real.sqrt q / 2 := by
    assumption
  have hlamEq : lam = Real.arcosh (Real.sqrt q / 2) := by
    apply Real.cosh_injOn (Set.mem_Ici.mpr hlam.le) (Set.mem_Ici.mpr hlam0.le)
    rw [hcosh, hcoshArc]
  
  have hreach : Tendsto (fun n  => -Real.log
      (μ.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}) /
         n ) atTop (𝓝 ξinv) := by
    refine (hdiag).congr' ?_
    filter_upwards with n
    have hevent : CorrLength.connectionEvent (0, 0) (diagonalSite n) =
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} := by
                                                                             solve_by_elim [_root_.Set.ext, _root_.PottsDiscontinuity.CorrLength.connectionEvent_iff_rcInfiniteReachable]
    rw [hevent]
  have htarget : Tendsto (fun n : ℕ => -(1 / (n )) * Real.log
      (μ.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
      atTop (𝓝 ξinv) := by
    grind
  have hxiLam : ξinv = lam + 2 * Slo := by
    simp_all
  refine ⟨Slo,  by
                  aesop , ?_⟩
  simpa [hxiLam] using htarget

end PottsDiscontinuity.RCMProof
