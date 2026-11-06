module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonEnergyPointwise

/-! # Terminal continuity of signed source corrections

The proved pointwise time envelope gives the terminal trace of the zero extension.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter Set
open scoped Topology

variable {d : ℕ}

/-- The interior representative extended by zero to the ambient cylinder. -/
def sourceInteriorZeroExtension  (a T : ℝ) (Ω : PDE.VelocityRegion d)
    (w : HypoellipticAleksandrov.Parabolic.ScalarField d) : HypoellipticAleksandrov.Parabolic.ScalarField d := by
  classical
  exact (scalarParabolicOpenCylinder a T Ω).piecewise w (fun _ => 0)

/-- A time envelope gives a continuous zero terminal trace for the interior extension. -/
theorem continuousWithinAt_source_zeroExtension_terminal
    {Ω : PDE.VelocityRegion d} (a T M : ℝ) (hM : 0 ≤ M)
    (w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hb : ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |w z| ≤ M * (T - z.1))
    (p : TimeVelocity d) (hp : p.1 = T) :
    ContinuousWithinAt
      (sourceInteriorZeroExtension a T Ω w)
      (scalarParabolicClosedCylinder a T Ω) p := by
  classical
  let U := scalarParabolicOpenCylinder a T Ω
  let W := U.piecewise w (fun _ => 0)
  have hpU : p ∉ U := by
    intro h
    exact (lt_irrefl T) (hp ▸ h.1.2)
  have hpW : W p = 0 := piecewise_eq_of_notMem U w _ hpU
  have hbound (z : TimeVelocity d) : ‖W z‖ ≤ M * |T - z.1| := by
    by_cases hz : z ∈ U
    · rw [show W z = w z from piecewise_eq_of_mem U w _ hz,
        Real.norm_eq_abs]
      simpa only [abs_of_pos (sub_pos.mpr hz.1.2)] using hb z hz
    · rw [show W z = 0 from piecewise_eq_of_notMem U w _ hz, norm_zero]
      exact mul_nonneg hM (abs_nonneg _)
  have hz : Tendsto (fun z : TimeVelocity d => M * |T - z.1|) (𝓝 p) (𝓝 0) := by
    have hc : Continuous (fun z : TimeVelocity d => M * |T - z.1|) :=
      continuous_const.mul (continuous_const.sub continuous_fst).abs
    simpa only [hp, sub_self, abs_zero, mul_zero] using
      (hc.continuousAt (x := p)).tendsto
  have hW : Tendsto W (𝓝 p) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2
      (squeeze_zero (fun _ => norm_nonneg _) hbound hz)
  change Tendsto W (𝓝[scalarParabolicClosedCylinder a T Ω] p) (𝓝 (W p))
  rw [hpW]
  exact hW.mono_left nhdsWithin_le_nhds

end HypoellipticAleksandrov.Parabolic.LocalHolder
