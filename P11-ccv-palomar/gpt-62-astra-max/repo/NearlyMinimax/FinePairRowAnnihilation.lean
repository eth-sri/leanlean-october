module

public import NearlyMinimax.FinePairRows


@[expose] public section

/-! Every bounded Borel density observable is killed by the genuine
uncentered response packet, under its actual absolute reference law. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Generic
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

variable {σ : Measure Z} [IsFiniteMeasure σ] {a b : ℝ} {m r D M q : ℕ} {C : ℝ} {A : Z → ι → ι → ℝ}
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
include hA hcost

theorem highPacketAbsoluteLaw_density_observable_zero
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    {F : Z × HighDensityMarkIndex m r D → ℝ} (hF : Measurable F)
    {L : ℝ} (hbound : ∀ e, ‖F e‖ ≤ L) :
    (∫ e, highPacketActivation σ a b m r D q C A e * F (e.1,e.2.1)
      ∂highPacketAbsoluteLaw σ a b m r D q C A) = 0 :=
  tensorActivation_density_zero (densityPacketWeight a b m r D) q C hA hcost hpos hF hbound

theorem finePairPacketAbsoluteLaw_density_observable_zero
    (hpos : 0 < finePairPacketMarkMass σ a b M q C A)
    {F : Z × FinePairDensityIndex M → ℝ} (hF : Measurable F)
    {L : ℝ} (hbound : ∀ e, ‖F e‖ ≤ L) :
    (∫ e, finePairPacketActivation σ a b M q C A e * F (e.1,e.2.1)
      ∂finePairPacketAbsoluteLaw σ a b M q C A) = 0 :=
  tensorActivation_density_zero (finePairDensityWeight a b M) q C hA hcost hpos hF hbound

end Generic
end NearlyMinimax
