module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.DiagonalComparison
public import PottsDiscontinuity.RCMProof.XiLower

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open FK Duality CorrLength

theorem routeB_free_nonpercolation_and_boundary_decay
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (hW21 : contract_eq315)
    (q : Set.Ici (1 : ℝ)) (hh319 : TorusRC.h319 q) (hq : 4 < q.val)
    (μ : Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Filter.Tendsto (fun n : ℕ =>
      -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) /
        (n : ℝ)) Filter.atTop (nhds ξinv)) :
    ∃ S : ℝ,
      Filter.Tendsto (altTanhPartial (Real.arcosh (Real.sqrt q.val / 2)))
        Filter.atTop (nhds S) ∧
      ξinv ≥ Real.arcosh (Real.sqrt q.val / 2) + 2 * S ∧
      μ (Duality.infiniteClusterAt (0, 0)) = 0 := by
  have := hμ.1
  obtain ⟨S, hS, hxi⟩ := xi_inverse_ge_critical_rate
    hW12i hW12ii hW21 q hh319 hq μ hμ ξinv hRate
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  have hlam : 0 < lam := Real.arcosh_pos
    (by nlinarith [Real.sq_sqrt (show 0 ≤ q.val by linarith), Real.sqrt_nonneg q.val])
  obtain ⟨S₀, _, hS₀, _, hpositive, _⟩ := PottsDiscontinuity.identity44 lam hlam
  have hS_eq : S = S₀ := tendsto_nhds_unique hS hS₀
  have hxiPositive : 0 < ξinv := lt_of_lt_of_le (hS_eq ▸ hpositive) (by simpa [lam] using hxi)
  have hRateDual : Filter.Tendsto (fun n : ℕ =>
      -(1 / (n : ℝ)) * Real.log (Duality.twoPoint μ (diagonalSite n)))
      Filter.atTop (nhds ξinv) := by
    refine hRate.congr' ?_
    filter_upwards with n
    have hevent : CorrLength.connectionEvent (0, 0) (diagonalSite n) =
        Duality.connectionEvent 0 (diagonalSite n) := by
      ext ω; exact CorrLength.connectionEvent_iff_rcInfiniteReachable (0, 0) (diagonalSite n) ω
    simp only [Duality.twoPoint, hevent]
    ring
  obtain ⟨C, c, _, hc, hdecay⟩ :=
    Duality.free_exponential_decay_of_pos_diagonal_rate
      (FK.criticalParameters q) μ hμ ξinv hxiPositive hRateDual
  have hclusterBound : ∀ x : ℤ × ℤ,
      μ (Duality.connectionEvent (0, 0) x) ≤ ENNReal.ofReal
        (C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) := fun x => by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal (hdecay x)
  exact ⟨S, hS, hxi,
    Duality.infiniteClusterAt_zero_of_exponential_decay μ C c hc hclusterBound⟩

end PottsDiscontinuity.RCMProof
