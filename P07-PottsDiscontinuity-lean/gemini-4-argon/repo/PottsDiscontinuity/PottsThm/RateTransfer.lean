module

public import PottsDiscontinuity.CorrLength.Positivity
public import PottsDiscontinuity.Frozen.Defs.DiagonalSite
public import PottsDiscontinuity.Potts.FreeSpinFormula

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.CorrLength

theorem free_spin_rate_of_rc_rate (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : Tendsto (fun n => boxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 φ))
    (hφrc : IsRCInfiniteVolumeLimit (fkParameters q hq β hβ).toP
      (fkParameters q hq β hβ).toQ 0 φ.toMeasure)
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β 0 μ.toMeasure)
    (L : ℝ)
    (hL : Tendsto
      (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
        (φ.toMeasure.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
      atTop (𝓝 L)) :
    Tendsto
      (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
        (μ.toMeasure.real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / (q : ℝ)))
      atTop (𝓝 L) := by
  let c : ℝ := 1 - 1 / (q : ℝ)
  have hc : 0 < c := sub_pos.mpr ((div_lt_one (by exact_mod_cast (show 0 < q by omega))).2
    (by exact_mod_cast (show 1 < q by omega)))
  have hconn (n : ℕ) : 0 < φ.toMeasure.real
      {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} := by
    rw [show {ω : LatticeConfiguration | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} =
        connectionEvent (0, 0) (diagonalSite n) by
      ext ω; exact (connectionEvent_iff_rcInfiniteReachable (0, 0) (diagonalSite n) ω).symm]
    exact isRCInfiniteVolumeLimit_connection_positive (fkParameters q hq β hβ)
      φ.toMeasure hφrc (0, 0) (diagonalSite n)
  have hlog (n : ℕ) :
      Real.log (μ.toMeasure.real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / (q : ℝ)) =
        Real.log c + Real.log (φ.toMeasure.real
          {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}) := by
    rw [show μ.toMeasure.real {σ | σ (0, 0) = σ (diagonalSite n)} - 1 / (q : ℝ) =
        c * φ.toMeasure.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} by
      rw [free_spin_correlation q hq β hβ φ hφ μ hμ (0, 0) (diagonalSite n)]; dsimp [c]; ring]
    exact Real.log_mul hc.ne' (hconn n).ne'
  have hsmall : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log c) atTop (𝓝 0) := by
    simpa [one_div, mul_comm, neg_mul] using
      (tendsto_const_nhds (x := -Real.log c)).mul
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  simp_rw [hlog, mul_add, add_comm (-(1 / (_ : ℝ)) * Real.log c)]
  simpa using hL.add hsmall

end PottsDiscontinuity.PottsThm
