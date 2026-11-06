module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.CorrLength.Positivity
public import PottsDiscontinuity.Frozen.Defs.DiagonalSite
public import PottsDiscontinuity.Potts.FreeSpinFormula
public import PottsDiscontinuity.PottsThm.CriticalParameters

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.Duality
open PottsDiscontinuity.CorrLength

theorem rc_diagonal_connection_tendsto_zero_of_pos_rate (q : ℕ) (hq : 4 < q)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 0 φ.toMeasure)
    (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
      (φ.toMeasure.real
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
      atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => φ.toMeasure.real
      {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}) atTop (𝓝 0) := by
  let p : ℕ → ℝ := fun n => φ.toMeasure.real
    {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}
  have hp (n : ℕ) : 0 < p n := by
    dsimp [p]
    rw [show {ω : LatticeConfiguration | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} =
        CorrLength.connectionEvent (0, 0) (diagonalSite n) by
      ext ω; exact (connectionEvent_iff_rcInfiniteReachable (0, 0) (diagonalSite n) ω).symm]
    exact isRCInfiniteVolumeLimit_connection_positive (criticalFKParameters q hq)
      φ.toMeasure hφ (0, 0) (diagonalSite n)
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * (L / 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp <|
      (tendsto_const_nhds.neg_mul_atTop (show -(L / 2) < 0 by linarith)
        tendsto_natCast_atTop_atTop).congr' (Eventually.of_forall fun n => by ring)
  have hbound : ∀ᶠ n : ℕ in atTop, p n ≤ Real.exp (-(n : ℝ) * (L / 2)) := by
    filter_upwards [hrate.eventually (Ioi_mem_nhds (show L / 2 < L by linarith)),
      eventually_gt_atTop 0] with n hr hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hmul := mul_lt_mul_of_pos_left hr hnR
    rw [show (n : ℝ) * (-(1 / (n : ℝ)) * Real.log (p n)) = -Real.log (p n) by field_simp] at hmul
    rw [← Real.exp_log (hp n)]
    exact (Real.exp_lt_exp.mpr (by nlinarith)).le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp
    (Eventually.of_forall fun _ => measureReal_nonneg) hbound

theorem free_spin_correlation_tendsto_uniform (q : ℕ) (hq : 4 < q)
    (φ : ProbabilityMeasure LatticeConfiguration)
    (hφ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP
      (criticalFKParameters q hq).toQ 0 φ.toMeasure)
    (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q (pottsCriticalBeta q) 0 μ.toMeasure)
    (hφweak : Tendsto
      (fun n => boxProbabilityMeasure (fkParameters q (by omega)
        (pottsCriticalBeta q) (pottsCriticalBeta_pos q hq)) (0, 0) n)
      atTop (𝓝 φ))
    (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
      (φ.toMeasure.real
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
      atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => μ.toMeasure.real
      {σ | σ (0, 0) = σ (diagonalSite n)}) atTop (𝓝 (1 / (q : ℝ))) := by
  simp_rw [fun n => free_spin_correlation q (by omega) (pottsCriticalBeta q)
    (pottsCriticalBeta_pos q hq) φ hφweak μ hμ (0, 0) (diagonalSite n)]
  simpa using (tendsto_const_nhds (x := (1 / (q : ℝ)))).add
    (tendsto_const_nhds.mul (rc_diagonal_connection_tendsto_zero_of_pos_rate q hq φ hφ L hL hrate))

end PottsDiscontinuity.PottsThm
