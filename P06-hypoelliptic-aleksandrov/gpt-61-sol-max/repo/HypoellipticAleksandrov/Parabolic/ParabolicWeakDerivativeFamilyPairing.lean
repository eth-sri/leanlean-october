module

public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexSplitSuccessor
import Batteries.Tactic.Alias
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSmoothResidual
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder





/-!
# Compact-test pairing for weak derivative families

This file identifies every selected representative in a bounded parabolic weak
derivative family by repeated distributional integration by parts.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory


variable {d : ℕ}

variable (gamma : TimeVelocityMultiIndex d) (f : HypoellipticAleksandrov.Parabolic.ScalarField d)

private alias coordinateIteratedFDeriv_contDiff := _root_.HypoellipticAleksandrov.Parabolic.LocalHolder.contDiff_coordinateIteratedFDeriv_infty


private theorem coordinateIteratedFDeriv_tsupport_subset
      :
    tsupport (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  apply support_iteratedFDeriv_subset (f := f) (𝕜 := ℝ) gamma.coordinateList.length
  intro hzero
  exact hz (by
    simp_all [TimeVelocityMultiIndex.coordinateIteratedFDeriv])

private theorem coordinateIteratedFDeriv_hasCompactSupport
      (hf : HasCompactSupport f) :
    HasCompactSupport
      (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma f) :=
  hf.of_isClosed_subset isClosed_closure
    (coordinateIteratedFDeriv_tsupport_subset gamma f)

section
variable (hf : ContDiff ℝ PDE.smoothOrder f)

include hf
private theorem timeDerivative_coordinateIteratedFDeriv
       (z : TimeVelocity d) :
    timeDerivative (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma f) z =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (gamma + Pi.single (timeCoord d) 1) f z := by
  rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single]
  · rfl
  · exact contDiff_infty.mp hf _

private theorem velocityGradient_coordinateIteratedFDeriv

    (i : Fin d) (z : TimeVelocity d) :
    velocityGradient (TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma f) z i =
      TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (gamma + Pi.single (velocityCoord i) 1) f z := by
  rw [TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single]
  · rfl
  · exact contDiff_infty.mp hf _
end


private theorem integral_mul_congr_ae
     {U : HypoellipticAleksandrov.Parabolic.Region d}
    {f g ψ : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hfg : f =ᵐ[timeVelocityVolumeOn U] g) :
    (∫ z in U, f z * ψ z ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ∫ z in U, g z * ψ z ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  apply integral_congr_ae
  filter_upwards [hfg] with z hz
  rw [hz]

/-- Distributional compact-test characterization of every selected bounded
time--velocity weak derivative. -/
theorem ParabolicWeakDerivativeFamily.integral_representative_mul_test
    {d L : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (D : ParabolicWeakDerivativeFamily d L U u)
    (alpha : ParabolicDerivativeIndex d L)
    (φ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hφSmooth : ContDiff ℝ PDE.smoothOrder φ)
    (hφCompact : HasCompactSupport φ)
    (hφSupport : tsupport φ ⊆ U) :
    (∫ z in U, D.representative alpha z * φ z
      ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
      ((-1 : ℝ) ^ alpha.1.order) *
        ∫ z in U, u z *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv alpha.1 φ z
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  let P := fun beta  =>
    ∀ (gamma : TimeVelocityMultiIndex d) (ψ : HypoellipticAleksandrov.Parabolic.ScalarField d),
      ContDiff ℝ PDE.smoothOrder ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ z in U, D.representative beta z *
          TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma ψ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
        ((-1 : ℝ) ^ beta.1.order) *
          ∫ z in U, u z *
            TimeVelocityMultiIndex.coordinateIteratedFDeriv (beta.1 + gamma) ψ z
            ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
  have hmain := ParabolicDerivativeIndex.inductionOn alpha (P := P) ?_ ?_ ?_
  simpa using hmain (0 ) φ
    hφSmooth hφCompact hφSupport
  · intro gamma ψ _ _ _
    rw [integral_mul_congr_ae D.zero_ae]
    simp [ParabolicDerivativeIndex.coe_zero, TimeVelocityMultiIndex.order,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
      VelocityMultiIndex.order]
  · intro beta h ih gamma ψ hψSmooth hψCompact hψSupport
    let θ := TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma ψ




    have hind := ih (gamma + Pi.single (timeCoord d) 1) ψ
      hψSmooth hψCompact hψSupport
    rw [ParabolicDerivativeIndex.coe_timeSucc_eq_add_single]
    rw [show (∫ z in U, D.representative
        (ParabolicDerivativeIndex.timeSucc beta h) z * θ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
        -∫ z in U, D.representative beta z * timeDerivative θ z
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) by linarith only [(D.hasWeakTimeSucc beta h θ (coordinateIteratedFDeriv_contDiff gamma ψ hψSmooth) (coordinateIteratedFDeriv_hasCompactSupport gamma ψ hψCompact) ((coordinateIteratedFDeriv_tsupport_subset gamma ψ).trans hψSupport))]]
    dsimp only [θ]
    simp_rw [timeDerivative_coordinateIteratedFDeriv gamma ψ hψSmooth]
    rw [hind]
    simp only [TimeVelocityMultiIndex.order_add,
      TimeVelocityMultiIndex.order_single, pow_add, pow_one]
    ring_nf
  · intro beta i h ih gamma ψ hψSmooth hψCompact hψSupport
    let θ := TimeVelocityMultiIndex.coordinateIteratedFDeriv gamma ψ




    have hind := ih (gamma + Pi.single (velocityCoord i) 1) ψ
      hψSmooth hψCompact hψSupport
    rw [ParabolicDerivativeIndex.coe_velocitySucc_eq_add_single]
    rw [show (∫ z in U, D.representative
        (ParabolicDerivativeIndex.velocitySucc beta i h) z * θ z
        ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
        -∫ z in U, D.representative beta z * velocityGradient θ z i
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) by linarith only [(D.hasWeakVelocitySucc beta i h θ (_root_.HypoellipticAleksandrov.Parabolic.LocalHolder.contDiff_coordinateIteratedFDeriv_infty gamma ψ hψSmooth) (coordinateIteratedFDeriv_hasCompactSupport gamma ψ hψCompact) ((coordinateIteratedFDeriv_tsupport_subset gamma ψ).trans hψSupport))]]
    dsimp only [θ]
    simp_rw [velocityGradient_coordinateIteratedFDeriv gamma ψ hψSmooth i]
    rw [hind]
    simp only [TimeVelocityMultiIndex.order_add,
      TimeVelocityMultiIndex.order_single, pow_add, pow_one]
    ring_nf

end HypoellipticAleksandrov.Parabolic
