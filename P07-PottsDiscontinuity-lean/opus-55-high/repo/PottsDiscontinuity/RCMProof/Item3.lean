module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.RCMProof.DominanceAssembly
public import PottsDiscontinuity.RCMProof.FinalAssembly
public import PottsDiscontinuity.RCMProof.Cor313Adapters
public import PottsDiscontinuity.RCMProof.TorusRCAdapters
public import PottsDiscontinuity.TorusExploration.Contract

public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity

/-- Theorem 1.2 item 3 for every free critical box limit, using the rotated
lattice rate bridge and the two matching bounds on the inverse correlation
length. -/
theorem rcItem3ForEveryFreeLimit_proved
    (hW21h319 : contract_h319)
    (q : ℝ) (hq : 4 < q) : rcItem3ForEveryFreeLimit q hq := by
  intro μ hμ lam hlam hcosh
  let qI : Set.Ici (1 : ℝ) := ⟨q, le_trans (by norm_num : (1 : ℝ) ≤ 4) hq.le⟩
  let hW21eq315 := contract_eq315_proved
  let hW21eq316 := TorusExploration.contract_eq316
  have hh319 := hW21h319 qI
  have hμFK : IsRCInfiniteVolumeLimit (FK.criticalParameters qI).toP
      (FK.criticalParameters qI).toQ 0 μ := by
    tauto
  obtain ⟨aInf, haInf, _hrot, hdiag⟩ :=
    CorrLength.rotated_correlation_rate_exists_for_limit
      (FK.criticalParameters qI) μ hμFK
  let ξinv := aInf / 2
  have hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv) := by
    omega
  let hW12i := contract_cor313_i_proved
  let hW12ii := contract_cor313_ii_proved
  let hW12iii := contract_cor313_iii_proved
  obtain ⟨Slo, hSlo, hLower⟩ := xi_inverse_ge_critical_rate
    hW12i hW12ii hW21eq315 qI hh319 hq μ hμFK ξinv hRate
  obtain ⟨Shi, hShi, hUpper⟩ := rc_xi_inverse_le_critical_rate
    hW12i hW12ii hW12iii hW21eq315 hW21eq316
    qI hh319 hq μ hμFK ξinv hRate
  have hSsame := tendsto_nhds_unique hSlo hShi
  have hxi : ξinv = Real.arcosh (Real.sqrt q / 2) + 2 * Slo := by
    linarith
  obtain ⟨hlam0, hcosh0⟩ := arcosh_pos_of_gt4 q hq
  have hlamEq : lam = Real.arcosh (Real.sqrt q / 2) := by
    apply Real.cosh_injOn (Set.mem_Ici.mpr hlam.le) (Set.mem_Ici.mpr hlam0.le)
    linarith
  have hsum : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      (-1 : ℝ) ^ k / (k : ℝ) * Real.tanh ((k : ℝ) * lam))
      atTop (𝓝 Slo) := by
    change Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
      (-1 : ℝ) ^ k / (k : ℝ) * Real.tanh
        ((k : ℝ) * Real.arcosh (Real.sqrt q / 2))) atTop (𝓝 Slo) at hSlo
    grind
  have hreach : Tendsto (fun n : ℕ => -Real.log
      (μ.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}) /
        (n : ℝ)) atTop (𝓝 ξinv) := by
    refine hRate.congr' ?_
    filter_upwards with n
    have hevent : CorrLength.connectionEvent (0, 0) (diagonalSite n) =
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} := by
      ext ω
      exact CorrLength.connectionEvent_iff_rcInfiniteReachable
        (0, 0) (diagonalSite n) ω
    simp_all
  have htarget : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
      (μ.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
      atTop (𝓝 ξinv) := by
    refine hreach.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    ring
  grind

end PottsDiscontinuity.RCMProof
