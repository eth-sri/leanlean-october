module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyUniformCauchy
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierLimitIdentification
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Continuous uniform limits of parabolic mollifications

This module turns the compact-carrier uniform Cauchy control for value
mollifications into a continuous uniform limit, then identifies that limit
almost everywhere with the stored value representative.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open Filter Set
open scoped ENNReal

namespace ParabolicW12Function

/-- Compactly supported value mollifications have a continuous uniform limit
on every compact time--velocity carrier, equal almost everywhere there to the
stored value representative. -/
theorem exists_continuousOn_tendstoUniformlyOn_ae_eq_toFun_parabolicConvolution
    {d : Nat} (hd : 1 <= d)
    (g : ParabolicW12Function d Set.univ (parabolicExponent d))
    (hg : HasCompactSupport g.toFun)
    (K : HypoellipticAleksandrov.Parabolic.Region d) (hK : IsCompact K) :
    ∃ q : HypoellipticAleksandrov.Parabolic.ScalarField d,
      ContinuousOn q K ∧
      TendstoUniformlyOn
        (fun n  => fun z : TimeVelocity d =>
          parabolicConvolution g.toFun (parabolicMollifier d n) z)
        q atTop K ∧
      q =ᵐ[timeVelocityVolumeOn K] g.toFun := by
  classical
  let F  := fun n z =>
    parabolicConvolution g.toFun (parabolicMollifier d n) z
  have hSup : UniformCauchySeqOn F atTop K := by
    exact g.uniformCauchySeqOn_parabolicConvolution hd hg K hK
  let q  := fun z =>
    if hz : z ∈ K then
      Classical.choose (cauchySeq_tendsto_of_complete (hSup.cauchySeq hz))
    else 0
  have hPointwise : ∀ z ∈ K, Tendsto (fun n  => F n z) atTop (nhds (q z)) := by
    intro z hz
    rw [show q z = Classical.choose (cauchySeq_tendsto_of_complete (hSup.cauchySeq hz)) by
      simp only [q, dif_pos hz]]
    exact Classical.choose_spec (cauchySeq_tendsto_of_complete (hSup.cauchySeq hz))
  have hUniform  :=
    hSup.tendstoUniformlyOn_of_tendsto hPointwise
  have hContinuous : ContinuousOn q K := by
    apply hUniform.continuousOn
    have hEventually : ∀ᶠ n : Nat in atTop, ContinuousOn (F n) K := by
      exact Filter.Eventually.of_forall fun n => by
        change ContinuousOn (parabolicConvolution g.toFun (parabolicMollifier d n)) K
        have hSmooth : ContDiff Real PDE.smoothOrder
            (parabolicConvolution g.toFun (parabolicMollifier d n)) :=
          g.contDiff_convolution (by simp [parabolicExponent]) (parabolicMollifier d n)
            (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)
        exact hSmooth.continuous.continuousOn
    exact hEventually.frequently
  refine ⟨q, hContinuous, ?_, ?_⟩
  · exact hUniform
  · exact g.ae_eq_limit_toFun_on_of_pointwiseLimit hK.measurableSet hPointwise

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
