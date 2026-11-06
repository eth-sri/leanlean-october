module

public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierConvergence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Almost-everywhere identification of a parabolic mollifier limit

This module identifies a supplied pointwise limit of the parabolic
mollifications of a global weak jet with its stored value representative on a
measurable carrier.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace ParabolicW12Function

/-- A supplied pointwise limit of the parabolic mollifications agrees almost
everywhere on a measurable carrier with the stored value representative. -/
theorem ae_eq_limit_toFun_on_of_pointwiseLimit
    {d : Nat} {K : Set (TimeVelocity d)}
    (hKmeas : MeasurableSet K)
    (g : ParabolicW12Function d Set.univ (parabolicExponent d))
    {q : TimeVelocity d -> Real}
    (hPointwise : ∀ z ∈ K,
      Tendsto (fun n : Nat =>
        parabolicConvolution g.toFun (parabolicMollifier d n) z)
        atTop (nhds (q z))) :
    q =ᵐ[timeVelocityVolumeOn K] g.toFun := by
  let p  := parabolicExponent d
  have hpOne : (1) ≤ p := by
    simpa only [p, Pi.sub_def] using (by simp [parabolicExponent])
  have hpTop : p ≠ ∞ := by
    simpa only [p, Pi.sub_def] using (by simp [parabolicExponent])
  have hpNeZero  :=
    (zero_lt_one.trans_le hpOne).ne.symm
  have hInMeasure : TendstoInMeasure _
      (fun n z => parabolicConvolution g.toFun _ z)
      atTop g.toFun :=
    tendstoInMeasure_of_tendsto_eLpNorm hpNeZero
      (by
        simpa only [p, Pi.sub_def] using
          g.tendsto_eLpNorm_convolution_toFun_sub hpOne hpTop)
  obtain ⟨ns, hns, hsubAe⟩ := hInMeasure.exists_seq_tendsto_ae
  filter_upwards [ae_restrict_of_ae hsubAe, ae_restrict_mem hKmeas] with z hzToFun hzK
  exact tendsto_nhds_unique ((hPointwise z hzK).comp hns.tendsto_atTop) hzToFun

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
