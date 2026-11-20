module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationAllTimeKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartMixtures

/-! # Integrating the literal position-start identity against actual starting measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/-- Finite active starting measures satisfy the exact position-resolved slab identity. -/
theorem positionStartQuadratic_integrated_slab_identity
    
    {lam Lam : ℝ} 
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (Y a b : ℝ)
    (hc : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ c.active) (hab : a ≤ b) :
    let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
    (∫ p in {q : Point | a < q.time ∧ q.time ≤ b}, f p ∂mu) =
      (∫ q, f q ∂(positionStartTerminalKernel A c J b ∘ₘ mu)) -
      (∫ q, f q ∂(positionStartTerminalKernel A c J a ∘ₘ mu)) -
      ∫ q in {q : Point | a < q.time ∧ q.time ≤ b}, forwardScalarOperator A.a f q
        ∂(enlargedActiveGreenKernel A c ∘ₘ mu) := by
  dsimp only
  let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
    visitQuadratic c (q.velocity 0)
  let g := fun q : Point => forwardScalarOperator A.a f q
  let S := {q : Point | a < q.time ∧ q.time ≤ b}
  let B := positionStartTerminalKernel A c J b
  let D := positionStartTerminalKernel A c J a
  let G := enlargedActiveGreenKernel A c
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isClosed_le continuous_time continuous_const).measurableSet
  have hB : Integrable f (B ∘ₘ mu) :=
    positionStartQuadratic_integrable c Y _
      (positionStartTerminalMixture_ae_closedActive A c J b mu)
  have hD : Integrable f (D ∘ₘ mu) :=
    positionStartQuadratic_integrable c Y _
      (positionStartTerminalMixture_ae_closedActive A c J a mu)
  have hG : Integrable g (G ∘ₘ mu) :=
    positionStartQuadratic_operator_integrable A c Y hc _
      (positionStartAllTimeMixture_ae_active A c mu)
  have hGs : Integrable (S.indicator g) (G ∘ₘ mu) := hG.indicator hS
  have hp : S.indicator f =ᵐ[mu] fun p =>
      (∫ q, f q ∂B p) - (∫ q, f q ∂D p) - ∫ q, S.indicator g q ∂G p := by
    filter_upwards [hmu] with p hv
    have hi := positionStartQuadratic_slab_identity
      A c J Y a b hc hJ p hv hab
    dsimp only at hi
    rw [integral_indicator hS, show G p = _ from enlargedActiveGreenKernel_apply A c p hv]
    exact hi
  change (∫ p in S, f p ∂mu) =
    (∫ q, f q ∂B ∘ₘ mu) - (∫ q, f q ∂D ∘ₘ mu) - ∫ q in S, g q ∂G ∘ₘ mu
  rw [← integral_indicator hS, integral_congr_ae hp]
  have hiB := integrable_integral_measure_comp hB
  have hiD := integrable_integral_measure_comp hD
  have hiBD : Integrable (fun p => (∫ q, f q ∂B p) - ∫ q, f q ∂D p) mu := hiB.sub hiD
  rw [integral_sub hiBD (integrable_integral_measure_comp hGs), integral_sub hiB hiD,
    ← integral_measure_comp hB, ← integral_measure_comp hD,
    ← integral_measure_comp hGs, integral_indicator hS]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
