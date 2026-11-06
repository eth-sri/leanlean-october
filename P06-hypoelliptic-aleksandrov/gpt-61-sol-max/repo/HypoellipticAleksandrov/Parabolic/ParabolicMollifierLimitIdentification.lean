module

public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierConvergence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Almost-everywhere identification of a parabolic mollifier limit

This module identifies a supplied pointwise limit of the parabolic
mollifications of a global weak jet with its stored value representative on a
measurable carrier.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal

namespace ParabolicW12Function

/-- A supplied pointwise limit of the parabolic mollifications agrees almost
everywhere on a measurable carrier with the stored value representative. -/
theorem ae_eq_limit_toFun_on_of_pointwiseLimit
    {d : Nat} {K : HypoellipticAleksandrov.Parabolic.Region d}
    (hKmeas : MeasurableSet K)
    (g : ParabolicW12Function d Set.univ (parabolicExponent d))
    {q : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hPointwise : ∀ z ∈ K,
      Tendsto (fun n  =>
        parabolicConvolution g.toFun (parabolicMollifier d n) z)
        atTop (nhds (q z))) :
    q =ᵐ[timeVelocityVolumeOn K] g.toFun := by
  let p  := parabolicExponent d
  have hpOne : (1 : ENNReal) ≤ p := by
    simpa only using (by simp [p, parabolicExponent] : (1 : ENNReal) ≤ parabolicExponent d)



  have hInMeasure  :=
    tendstoInMeasure_of_tendsto_eLpNorm ((zero_lt_one.trans_le hpOne).ne.symm)
      ((id (tendsto_eLpNorm_convolution_toFun_sub g hpOne (by
          simpa only using (by simp [p, parabolicExponent] : parabolicExponent d ≠ ∞)))))
  obtain ⟨ns, hns, hsubAe⟩ := hInMeasure.exists_seq_tendsto_ae
  filter_upwards [ae_restrict_of_ae hsubAe, ae_restrict_mem hKmeas] with z hzToFun hzK
  exact tendsto_nhds_unique ((hPointwise z hzK).comp hns.tendsto_atTop) hzToFun

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
