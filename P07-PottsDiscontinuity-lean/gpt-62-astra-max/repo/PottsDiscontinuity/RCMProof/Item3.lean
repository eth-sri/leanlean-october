module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.RCMProof.DominanceAssembly
public import PottsDiscontinuity.Analysis.Identity44
public import PottsDiscontinuity.TorusCrossing.Final
public import PottsDiscontinuity.RCMProof.Cor313Adapters
public import PottsDiscontinuity.RCMProof.TorusRCAdapters
public import PottsDiscontinuity.TorusExploration.Contract

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity

/-- Theorem 1.2 item 3 for every free critical box limit, using the rotated
lattice rate bridge and the two matching bounds on the inverse correlation
length. -/
theorem rc_critical_rate (q : ℝ) (hq : 4 < q)
    {μ : Measure (squareLattice.edgeSet → Bool)}
    (hμ : IsRCInfiniteVolumeLimit (rcCriticalParameter ⟨q, by change 1 ≤ q; linarith⟩)
      ⟨q, by change 0 < q; linarith⟩ 0 μ)
    (lam : ℝ) (hlam : 0 < lam) (hcosh : Real.cosh lam = Real.sqrt q / 2) :
    ∃ S, Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
        (μ.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
        atTop (𝓝 (lam + 2 * S)) ∧ 0 < lam + 2 * S := by
  let Q : Set.Ici (1:ℝ) := ⟨q, by change 1 ≤ q; linarith⟩
  have hfree : IsRCInfiniteVolumeLimit (FK.criticalParameters Q).toP (FK.criticalParameters Q).toQ 0 μ := hμ
  obtain ⟨a,_,_,hdiag⟩ := CorrLength.rotated_correlation_rate_exists_for_limit μ hfree
  have hcros := TorusCrossing.h319_proved Q
  obtain ⟨S,hs,hlo⟩ := xi_inverse_ge_critical_rate contract_cor313_i_proved contract_cor313_ii_proved
    contract_eq315_proved Q hcros hq μ hfree (a/2) hdiag
  have hlam' : Real.arcosh (Real.sqrt q/2) = lam := hcosh ▸ Real.arcosh_cosh hlam.le
  obtain rfl := hlam'
  obtain ⟨T,_,ht,_,hp,_⟩ := identity44 hlam
  have hpos := tendsto_nhds_unique hs ht ▸ hp
  have heq := le_antisymm (rc_xi_inverse_le_critical_rate contract_cor313_i_proved
    contract_cor313_iii_proved TorusExploration.contract_eq316 Q hcros hq μ hfree _ hdiag hs hpos hlo) hlo
  refine ⟨S,hs,heq ▸ hdiag.congr' ?_,hpos⟩
  filter_upwards with n
  have e : CorrLength.connectionEvent (0,0) (diagonalSite n) = {ω | (rcInfiniteOpenGraph ω).Reachable (0,0) (diagonalSite n)} :=
    Set.ext fun ω => CorrLength.connectionEvent_iff_rcInfiniteReachable _ _ ω
  rw [e]; ring

end PottsDiscontinuity.RCMProof
