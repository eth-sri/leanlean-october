module

public import FixedPointTheorems.brouwer
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.CorrLength.Positivity
public import PottsDiscontinuity.Frozen.Defs.DiagonalSite
public import PottsDiscontinuity.Potts.FreeSpinFormula
public import PottsDiscontinuity.PottsThm.CriticalParameters

public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.PottsThm

open PottsDiscontinuity
open PottsDiscontinuity.FK
open PottsDiscontinuity.Potts
open PottsDiscontinuity.Duality
open PottsDiscontinuity.CorrLength

section
variable (q : ℕ) (hq : 4 < q) (φ : ProbabilityMeasure LatticeConfiguration) (hφ : IsRCInfiniteVolumeLimit (criticalFKParameters q hq).toP (criticalFKParameters q hq).toQ 0 φ.toMeasure)
include q hq φ hφ
/-- A positive logarithmic rate forces the free RC connection probabilities
along the specified diagonal to vanish. -/
theorem rc_diagonal_connection_tendsto_zero_of_pos_rate (L : ℝ) (hL : 0 < L)
    (hrate : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
      (φ.toMeasure.real
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}))
      atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => φ.toMeasure.real
      {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}) atTop (𝓝 0) := by
  let p := fun n => φ.toMeasure.real
    {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}
  have hp (n : ℕ) : 0 < p n := by
    have hevent : CorrLength.connectionEvent (0, 0) (diagonalSite n) =
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} := by
      ext ω
      exact connectionEvent_iff_rcInfiniteReachable (0, 0) (diagonalSite n) ω
    change 0 < φ.toMeasure.real
      {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)}
    rw [← hevent]
    exact isRCInfiniteVolumeLimit_connection_positive (criticalFKParameters q hq)
      φ.toMeasure hφ (0, 0) (diagonalSite n)
  have hratep : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (p n))
      atTop (𝓝 L) := by
    omega
  have hexpArg : Tendsto (fun n : ℕ => -(n : ℝ) * (L / 2)) atTop atBot := by
    have hc : -(L / 2) < 0 := by linarith
    have ht := tendsto_const_nhds.neg_mul_atTop hc tendsto_natCast_atTop_atTop
    grind
  have hrateLower : ∀ᶠ n : ℕ in atTop, L / 2 < -(1 / (n : ℝ)) * Real.log (p n) :=
    hratep.eventually (Ioi_mem_nhds (by linarith))
  have hbound : ∀ᶠ n : ℕ in atTop, p n ≤ Real.exp (-(n : ℝ) * (L / 2)) := by
    filter_upwards [hrateLower, eventually_gt_atTop 0] with n hr hn
    have hnR : 0 < (n : ℝ) := by positivity
    have hiden : (n : ℝ) * (-(1 / (n : ℝ)) * Real.log (p n)) =
        -Real.log (p n) := by
      field_simp
    have hlog : Real.log (p n) < -(n : ℝ) * (L / 2) := by nlinarith
    have hexp' := Real.exp_lt_exp.mpr hlog
    rw [Real.exp_log (hp n)] at hexp'
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    (Real.tendsto_exp_atBot.comp hexpArg) (Eventually.of_forall (fun n => measureReal_nonneg)) hbound

/-- The free Potts two point function tends to its independent-colour value
along the frozen diagonal whenever the supplied RC rate is positive. -/
theorem free_spin_correlation_tendsto_uniform (μ : ProbabilityMeasure (SpinSpace q))
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
  have hc : Tendsto (fun n : ℕ => (1 - 1 / (q : ℝ)) *
      φ.toMeasure.real
        {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)})
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (rc_diagonal_connection_tendsto_zero_of_pos_rate q hq φ hφ L hL hrate))
  have hsum := (tendsto_const_nhds (x := (1 / (q : ℝ)))).add hc
  have hseq : (fun n : ℕ => μ.toMeasure.real
      {σ | σ (0, 0) = σ (diagonalSite n)}) =
      fun n => 1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
        φ.toMeasure.real
          {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} := by
    funext n
    exact free_spin_correlation q (by omega) (pottsCriticalBeta q)
      (pottsCriticalBeta_pos q hq) φ hφweak μ hμ (0, 0) (diagonalSite n)
  simp_all
end

end PottsDiscontinuity.PottsThm
