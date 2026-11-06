module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyUniformCauchy
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierLimitIdentification
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Continuous uniform limits of parabolic mollifications

This module turns the compact-carrier uniform Cauchy control for value
mollifications into a continuous uniform limit, then identifies that limit
almost everywhere with the stored value representative.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace ParabolicW12Function

/-- Compactly supported value mollifications have a continuous uniform limit
on every compact time--velocity carrier, equal almost everywhere there to the
stored value representative. -/
theorem exists_continuousOn_tendstoUniformlyOn_ae_eq_toFun_parabolicConvolution
    {d : Nat} (hd : 1 <= d)
    (g : ParabolicW12Function d Set.univ (parabolicExponent d))
    (hg : HasCompactSupport g.toFun)
    (K : Set (TimeVelocity d)) (hK : IsCompact K) :
    ∃ q : TimeVelocity d → Real,
      ContinuousOn q K ∧
      TendstoUniformlyOn
        (fun n : Nat => fun z : TimeVelocity d =>
          parabolicConvolution g.toFun (parabolicMollifier d n) z)
        q atTop K ∧
      q =ᵐ[timeVelocityVolumeOn K] g.toFun := by
  classical
  let F  := fun n z =>
    parabolicConvolution g.toFun (parabolicMollifier d n) z
  have hSup : UniformCauchySeqOn F atTop K := by
    simpa using g.uniformCauchySeqOn_parabolicConvolution hd hg K hK
  let q  := fun z =>
    if hz : z ∈ K then
      Classical.choose (cauchySeq_tendsto_of_complete (hSup.cauchySeq hz))
    else 0
  have hPointwise : ∀ z ∈ K, Tendsto (fun n : Nat => F n z) atTop (nhds (q z)) := by
    grind
  have hUniform  :=
    hSup.tendstoUniformlyOn_of_tendsto hPointwise
  have hContinuous : ContinuousOn q K := by
    apply hUniform.continuousOn
    have hEventually : ∀ᶠ n : Nat in atTop, ContinuousOn (F n) K := Filter.Eventually.of_forall fun n => by
        have hSmooth : ContDiff Real _
            _ :=
          g.contDiff_convolution (by simp [parabolicExponent]) _
            (contDiff_parabolicMollifier d n) (hasCompactSupport_parabolicMollifier d n)
        exact hSmooth.continuous.continuousOn
    exact hEventually.frequently
  refine ⟨q, hContinuous, ?_, ?_⟩
  · omega
  · exact g.ae_eq_limit_toFun_on_of_pointwiseLimit hK.measurableSet hPointwise

end ParabolicW12Function

end HypoellipticAleksandrov.Parabolic
