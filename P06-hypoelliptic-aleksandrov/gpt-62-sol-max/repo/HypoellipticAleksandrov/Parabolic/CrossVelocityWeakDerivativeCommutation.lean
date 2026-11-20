module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique

/-!
# Crossed weak velocity derivatives

This module proves that two crossed second weak velocity derivatives of one
raw function agree almost everywhere.  The proof uses distributional
uniqueness and commutation of classical mixed derivatives of test functions.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

theorem cross_velocityGradient_tsupport_subset {d : ℕ}
    {f : TimeVelocity d → ℝ} {i : Fin d} :
    tsupport (fun z => velocityGradient f z i) ⊆ tsupport f := by
  unfold velocityGradient
  change closure (Function.support
    (fun z => fderiv ℝ f z (0, Pi.single i 1))) ⊆ tsupport f
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  rw [Function.mem_support] at hz ⊢
  intro hzero
  apply hz
  simp [hzero]

namespace HasWeakVelocityPartialDerivOn

/-- Two crossed second weak velocity derivatives of the same raw function
agree almost everywhere on an open domain. -/
theorem cross_ae_eq_of_memLp
    {d : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U)
    (i j : Fin d)
    (u ui uj dij dji : TimeVelocity d → ℝ)
    (hdij : ParabolicMemLpOn U 2 dij)
    (hdji : ParabolicMemLpOn U 2 dji)
    (hui : HasWeakVelocityPartialDerivOn U i u ui)
    (huj : HasWeakVelocityPartialDerivOn U j u uj)
    (hij : HasWeakVelocityPartialDerivOn U j ui dij)
    (hji : HasWeakVelocityPartialDerivOn U i uj dji) :
    dij =ᵐ[timeVelocityVolumeOn U] dji := by
  apply ae_eq_of_pairing_eq hU
    (hdij.locallyIntegrableOn (by norm_num))
    (hdji.locallyIntegrableOn (by norm_num))
  intro φ hφSmooth hφCompact hφSub
  have htestSmooth (k : Fin d) :
      ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient φ z k) :=
    _root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_contDiff_infty hφSmooth
  have htestCompact (k : Fin d) :
      HasCompactSupport (fun z => velocityGradient φ z k) :=
    _root_.HypoellipticAleksandrov.Parabolic.velocityGradient_compact hφCompact
  have htestSub (k : Fin d) :
      tsupport (fun z => velocityGradient φ z k) ⊆ U :=
    cross_velocityGradient_tsupport_subset.trans hφSub
  have hijSecond := hij φ hφSmooth hφCompact hφSub
  have hiFirst := hui (fun z => velocityGradient φ z j) (htestSmooth j)
    (htestCompact j) (htestSub j)
  have hjiSecond := hji φ hφSmooth hφCompact hφSub
  have hjFirst := huj (fun z => velocityGradient φ z i) (htestSmooth i)
    (htestCompact i) (htestSub i)
  calc
    (∫ z in U, dij z * φ z ∂volume) =
        ∫ z in U, u z *
          velocityGradient (fun y => velocityGradient φ y j) z i ∂volume := by
      linarith only [hijSecond, hiFirst]
    _ = ∫ z in U, u z *
          velocityGradient (fun y => velocityGradient φ y i) z j ∂volume := by
      apply setIntegral_congr_fun hU.measurableSet
      intro z hz
      simp only
      rw [_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_velocityGradient_commute hφSmooth]
    _ = ∫ z in U, dji z * φ z ∂volume := by
      linarith only [hjiSecond, hjFirst]

end HasWeakVelocityPartialDerivOn
end HypoellipticAleksandrov.Parabolic
