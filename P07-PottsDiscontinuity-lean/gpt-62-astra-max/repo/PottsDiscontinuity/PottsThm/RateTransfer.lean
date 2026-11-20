module

public import PottsDiscontinuity.Frozen.Defs.DiagonalSite
public import PottsDiscontinuity.PottsThm.SamplerObservations

@[expose] public section
namespace PottsDiscontinuity.PottsThm
open Filter Topology MeasureTheory FK RCInfinite Potts

/-- A fixed positive Edwards–Sokal prefactor does not affect the logarithmic rate. -/
theorem rate_mul_const {p : ℕ → ℝ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (hr : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (p n)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (c * p n)) atTop (𝓝 L) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  apply (show Tendsto _ atTop (𝓝 L) from (by simpa using hr.add (ht.neg.mul_const (Real.log c)))).congr'
  filter_upwards [hr.eventually (lt_mem_nhds hL)] with n hn
  have hn' : p n ≠ 0 := fun h => by simp [h] at hn
  grind [Real.log_mul hc.ne' hn']

theorem free_colorLaw_rate {q : ℕ} (hq : 2 ≤ q)
    {φ : Measure LatticeConfiguration} [IsProbabilityMeasure φ]
    (pin : Set.Icc 1 q)
    (hfin : ∀ᵐ ω ∂φ, ∀ x, (cluster ω x).Finite) {L : ℝ} (hL : 0 < L)
    (hr : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
      (φ.real {ω | (rcInfiniteOpenGraph ω).Reachable (0,0) (diagonalSite n)})) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
      ((colorLaw φ pin).real {σ | σ (0,0) = σ (diagonalSite n)} - 1 / q)) atTop (𝓝 L) := by
  have hc : 0 < 1 - (q : ℝ)⁻¹ := by
    apply sub_pos.mpr ((inv_lt_one₀ (by norm_cast; omega : (0:ℝ) < q)).mpr ?_); norm_cast
  simpa only [colorLaw_agreement pin _ _ hfin, one_div, add_sub_cancel_left] using
    rate_mul_const hL hc hr

end PottsDiscontinuity.PottsThm
