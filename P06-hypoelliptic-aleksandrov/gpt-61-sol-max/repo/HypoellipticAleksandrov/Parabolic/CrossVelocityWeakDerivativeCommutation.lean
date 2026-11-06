module

public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import PDEFoundation.Calculus.RegularityOrder


open private HypoellipticAleksandrov.Parabolic.ae_eq_of_pairing_eq from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_velocityGradient_commute from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_contDiff_infty from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique


/-!
# Crossed weak velocity derivatives

This module proves that two crossed second weak velocity derivatives of one
raw function agree almost everywhere.  The proof uses distributional
uniqueness and commutation of classical mixed derivatives of test functions.
-/

 public section

open MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic
















namespace HasWeakVelocityPartialDerivOn

/-- Two crossed second weak velocity derivatives of the same raw function
agree almost everywhere on an open domain. -/
theorem cross_ae_eq_of_memLp
    {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}
    (hU : IsOpen U)
    (i j : Fin d)
    (u ui uj dij dji : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hdij : ParabolicMemLpOn U 2 dij)
    (hdji : ParabolicMemLpOn U 2 dji)
    (hui : HasWeakVelocityPartialDerivOn U i u ui)
    (huj : HasWeakVelocityPartialDerivOn U j u uj)
    (hij : HasWeakVelocityPartialDerivOn U j ui dij)
    (hji : HasWeakVelocityPartialDerivOn U i uj dji) :
    dij =ᵐ[timeVelocityVolumeOn U] dji := by
  apply _root_.HypoellipticAleksandrov.Parabolic.ae_eq_of_pairing_eq hU
    (hdij.locallyIntegrableOn (by norm_num))
    (hdji.locallyIntegrableOn (by norm_num))
  intro φ hφSmooth hφCompact hφSub
  have htestSmooth (k : Fin d) :
      ContDiff ℝ PDE.smoothOrder (fun z => velocityGradient φ z k) :=
    _root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_contDiff_infty hφSmooth
  have htestCompact (k : Fin d) :
      HasCompactSupport (fun z => velocityGradient φ z k) :=
    _root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_hasCompactSupport hφCompact
  have htestSub (k : Fin d) :
      tsupport (fun z => velocityGradient φ z k) ⊆ U :=
    _root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset.trans hφSub

  have hiFirst := hui (fun z => velocityGradient φ z j) (htestSmooth j)
    (htestCompact j) (htestSub j)

  have hjFirst := huj (fun z => velocityGradient φ z i) (htestSmooth i)
    (htestCompact i) (htestSub i)
  calc
    (∫ z in U, dij z * φ z) =
        ∫ z in U, u z *
          velocityGradient (fun y => velocityGradient φ y j) z i := by
      linarith only [(hij φ hφSmooth hφCompact hφSub), hiFirst]
    _ = ∫ z in U, u z *
          velocityGradient (fun y => velocityGradient φ y i) z j := by
      apply setIntegral_congr_fun hU.measurableSet
      intro z hz
      simp only
      rw [_root_.HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_velocityGradient_commute hφSmooth]
    _ = ∫ z in U, dji z * φ z := by
      linarith only [(hji φ hφSmooth hφCompact hφSub), hjFirst]

end HasWeakVelocityPartialDerivOn
end HypoellipticAleksandrov.Parabolic
