module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationAllTimeKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonOrder

/-! # Genuine core domination by the all-time Green measure of the actual entrance count -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)

/-- Extending by zero preserves a pointwise comparison to a physical kernel. -/
theorem visitExtendKernel_le_of_subtype {D : Set Point} {hD : MeasurableSet D}
    {F : D → Measure Point} {hF : Measurable F} (G : Kernel Point Point)
    (hle : ∀ p : D, F p ≤ G p) (p : Point) : visitExtendKernel D hD F hF p ≤ G p := by
  by_cases hp : p ∈ D
  · rw [visitExtendKernel_apply_mem hp]
    exact hle ⟨p, hp⟩
  · rw [visitExtendKernel_apply_notMem hp]
    exact bot_le

/-- The finite active-union Green measure is dominated by the all-time active strip. -/
theorem finiteUnionGreen_le_enlargedActiveGreenKernel
    (T : ℝ) (e : FiniteUnionPole (visitActiveUnion c J) (T : WithTop ℝ)) :
    finiteUnionGreen A (visitActiveUnion c J) T e ≤ enlargedActiveGreenKernel A c e.val := by
  let H := visitActiveUnion c J
  let i := finiteUnionPoleIndex H T e
  have hsub : (H.component i).carrier ⊆ c.active := fun _ hv =>
    ((visitActiveUnion_carrier c J).le (H.component_subset i hv)).1
  rw [enlargedActiveGreenKernel_apply A c e.val ((visitActiveUnion_carrier c J).le e.property.2).1]
  exact stripGreen_mono A (H.component i) c.activeInterval hsub T ⊤ le_top
    (finiteUnionComponentPole H T e)

/-- A pointwise kernel order passes to the associated mixtures. -/
theorem visitKernel_compMeasure_le {K L : Kernel Point Point} (mu : Measure Point)
    (hle : ∀ p, K p ≤ L p) : K ∘ₘ mu ≤ L ∘ₘ mu := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.bind_apply hB (Kernel.aemeasurable _), Measure.bind_apply hB (Kernel.aemeasurable _)]
  exact lintegral_mono fun p => hle p B

/-- Each actual clipped active Green kernel is bounded by the full all-time active-strip kernel. -/
theorem visitActiveGreenKernel_le_allTime (p : Point) :
    visitUnionGreenKernel A (visitActiveUnion c J) s T p ≤
      enlargedActiveGreenKernel A c p := by
  apply visitExtendKernel_le_of_subtype
  exact fun e => finiteUnionGreen_le_enlargedActiveGreenKernel A c J T (visitPoleInclusion _ s T e)

/-- The genuine active Green mixture is bounded by its all-time active-strip extension. -/
theorem visitActiveGreenMixture_le_allTime (mu : Measure Point) :
    visitUnionGreenKernel A (visitActiveUnion c J) s T ∘ₘ mu ≤
      enlargedActiveGreen A c mu := visitKernel_compMeasure_le mu (visitActiveGreenKernel_le_allTime A c J s T)

/-- Core occupation is dominated by the actual all-time Green measure of the full visit count. -/
theorem visitOuterGreen_core_domination (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
    (visitUnionGreenKernel A J.toFiniteUnion s T P).restrict
      {q | q.velocity 0 ∈ c.core} ≤
    (enlargedActiveGreen A c
      (Measure.sum (visitEntrancePiece A c J s T P))).restrict
        {q | q.velocity 0 ∈ c.core} := by
  let C : Set Point := {q | q.velocity 0 ∈ c.core}
  have hC : MeasurableSet C :=
    isClosed_Icc.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  rw [visitOuterGreen_core_identity A c J s T hT P hP]
  unfold enlargedActiveGreen
  rw [Measure.bind_sum _ _ (Kernel.aemeasurable _), Measure.restrict_sum _ hC]
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.sum_apply _ hB, Measure.sum_apply _ hB]
  apply ENNReal.tsum_le_tsum
  intro n
  exact Measure.restrict_mono_measure
    (visitActiveGreenMixture_le_allTime A c J s T
      (visitEntrancePiece A c J s T P n)) C B

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
