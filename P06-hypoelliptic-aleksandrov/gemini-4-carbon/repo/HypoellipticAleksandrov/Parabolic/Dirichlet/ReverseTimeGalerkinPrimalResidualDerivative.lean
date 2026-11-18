module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperator
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeDualPairingRight
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGelfandPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourcePairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBochner
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTimeDerivative

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet
section
open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

local instance reverseTimeL2VStarModule
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  Lp.instModule

local instance reverseTimeSpatialFormOperatorNormedAddCommGroup
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) :
    NormedAddCommGroup (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ) := by
  letI : NormedAddCommGroup (H10HilbertGraph hΩ) := by infer_instance
  letI : NormedSpace ℝ (H10HilbertGraph hΩ) := by infer_instance
  letI : NormedAddCommGroup (H10HilbertGraphDual hΩ) := by infer_instance
  letI : NormedSpace ℝ (H10HilbertGraphDual hΩ) := by infer_instance
  infer_instance

private theorem AEStronglyMeasurable.clm_apply
    {α E F : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure α}
    (K : α → E →L[ℝ] F) (u : α → E)
    (hK : AEStronglyMeasurable K μ) (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x => K x (u x)) μ := by
  exact ((ContinuousLinearMap.apply ℝ F).flip).aestronglyMeasurable_comp₂ hK hu

/-- Pointwise representative of the Bochner spatial-form action. -/
noncomputable def reverseTimeSpatialFormBochnerRaw
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) : ℝ → H10HilbertGraphDual hΩ := fun τ =>
  reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth τ (u τ)


private theorem norm_reverseTimeSpatialFormBochnerRaw_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) (τ : ℝ) :
    ‖reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u τ‖ ≤ C * ‖u τ‖ := by
  change ‖reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth τ (u τ)‖ ≤ C * ‖u τ‖
  simpa only [reverseTimeSpatialFormOperatorClamp] using
    hC (Set.projIcc 0 (r₁ - r₀) (sub_nonneg.mpr h₀₁.le) τ) (u τ)

/-- The pointwise spatial-form action belongs to reverse-time L². -/
theorem memLp_reverseTimeSpatialFormBochnerRaw
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    MemLp (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u) (2 : ℝ≥0∞) (reverseTimeVolume (r₁ - r₀))  := by
  have aestronglyMeasurable_reverseTimeSpatialFormBochnerRaw {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ) (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
      AEStronglyMeasurable
      (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth u)
    (reverseTimeVolume (r₁ - r₀)) := by
    letI : SecondCountableTopologyEither ℝ
        (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ) :=
      { out := Or.inl (by infer_instance) }
    change AEStronglyMeasurable
      (fun τ => reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ (u τ))
      (reverseTimeVolume (r₁ - r₀))
    exact AEStronglyMeasurable.clm_apply
      (reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth)
      u
      (continuous_reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth).aestronglyMeasurable
      (Lp.memLp u).aestronglyMeasurable
  refine (Lp.memLp u).of_le_mul (c := C)
    (aestronglyMeasurable_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u) ?_
  exact Eventually.of_forall
    (norm_reverseTimeSpatialFormBochnerRaw_le r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC u)

/-- The spatial form acting on a reverse-time Bochner curve. -/
noncomputable def reverseTimeSpatialFormBochnerRawAction
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) : ReverseTimeL2VStar hΩ (r₁ - r₀) :=
  (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC u).toLp
    (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth u)

/-- The Bochner spatial-form action preserves addition. -/
theorem reverseTimeSpatialFormBochnerRawAction_map_add
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖)
    (u w : ReverseTimeL2V hΩ (r₁ - r₀)) :
    reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC (u + w) =
      reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC u +
      reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC w := by
    apply Lp.ext
    filter_upwards [
      (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC (u + w)).coeFn_toLp,
      (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC u).coeFn_toLp,
      (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC w).coeFn_toLp,
      Lp.coeFn_add u w,
      Lp.coeFn_add
        (reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u)
        (reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC w)] with τ hsum hu hw huv hout
    calc
      reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC (u + w) τ =
          reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth (u + w) τ := hsum
      _ = reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth u τ +
          reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth w τ := by
        simp only [reverseTimeSpatialFormBochnerRaw, huv, Pi.add_apply]
        exact (reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth τ).map_add _ _
      _ = reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u τ +
          reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth C hC w τ := by
        change _ =
          (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth C hC u).toLp
              (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
                haSmooth hbSmooth hcSmooth u) τ +
            (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth C hC w).toLp
              (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
                haSmooth hbSmooth hcSmooth w) τ
        rw [← hu, ← hw]
      _ = (reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u +
          reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth C hC w) τ := hout.symm

/-- The Bochner spatial-form action preserves scalar multiplication. -/
theorem reverseTimeSpatialFormBochnerRawAction_map_smul
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖)
    (q : ℝ) (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC (q • u) =
      q • reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC u := by
    apply Lp.ext
    filter_upwards [
      (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC (q • u)).coeFn_toLp,
      (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC u).coeFn_toLp,
      Lp.coeFn_smul q u,
      Lp.coeFn_smul q
        (reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u)] with τ hqu hu hquv hout
    change (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC (q • u)).toLp
        (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth (q • u)) τ = _
    rw [hqu]
    calc
      reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth (q • u) τ =
          q • reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth u τ := by
        simp only [reverseTimeSpatialFormBochnerRaw, hquv, Pi.smul_apply]
        exact (reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth τ).map_smul q _
      _ = q • reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u τ := by
        change _ = q • (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u).toLp
            (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth u) τ
        rw [← hu]
      _ = (q • reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth C hC u) τ := hout.symm

/-- The reverse-time Bochner spatial form as a linear map. -/
noncomputable def reverseTimeSpatialFormBochnerRawLinearMap
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖) :
    ReverseTimeL2V hΩ (r₁ - r₀) →ₗ[ℝ] ReverseTimeL2VStar hΩ (r₁ - r₀) where
  toFun := reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC
  map_add' := reverseTimeSpatialFormBochnerRawAction_map_add r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC
  map_smul' := reverseTimeSpatialFormBochnerRawAction_map_smul r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC

private theorem norm_reverseTimeSpatialFormBochnerRawAction_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (C : ℝ)
    (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ,
      ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    ‖reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC u).coeFn_toLp] with τ hτ
  change ‖(memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC u).toLp
      (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth u) τ‖ ≤ C * ‖u τ‖
  rw [hτ]
  exact norm_reverseTimeSpatialFormBochnerRaw_le r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC u τ

/-- The bounded linear Bochner action of the clamped reverse-time spatial form. -/
noncomputable def reverseTimeSpatialFormBochnerAction
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ReverseTimeL2VStar hΩ (r₁ - r₀) := by
  let C := Classical.choose (exists_reverseTimeSpatialFormOperator_bound r₀ r₁ h₀₁ hΩ
    hΩbounded a b c haSmooth hbSmooth hcSmooth)
  let hBound := (Classical.choose_spec (exists_reverseTimeSpatialFormOperator_bound r₀ r₁ h₀₁
    hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth)).2
  exact LinearMap.mkContinuous
    (reverseTimeSpatialFormBochnerRawLinearMap r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hBound)
    C
    (by
      intro u
      exact norm_reverseTimeSpatialFormBochnerRawAction_le r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hBound u)

/-- One event represents the action simultaneously for all spatial tests. -/
theorem ae_reverseTimeSpatialFormBochnerAction_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ v : H10HilbertGraph hΩ,
      reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth u τ v = reverseTimeSpatialForm hΩ r₁ τ a b c (u τ) v := by
  obtain ⟨C, hC, hBound⟩ := exists_reverseTimeSpatialFormOperator_bound r₀ r₁ h₀₁ hΩ hΩbounded
    a b c haSmooth hbSmooth hcSmooth
  unfold reverseTimeSpatialFormBochnerAction
  filter_upwards [
    (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hBound u).coeFn_toLp,
    ae_reverseTimeSpatialFormOperatorClamp_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth] with τ hRaw hClamp
  intro v
  change reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hBound u τ v = _
  change ((memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hBound u).toLp
      (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth u) τ) v = _
  rw [hRaw]
  exact hClamp (u τ) v

end
section
open Filter Function Set MeasureTheory Topology
open scoped Topology ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

/-- A norm-bounded sequence in a separable real Hilbert space has a strictly monotone
subsequence converging against every continuous linear functional. -/
theorem exists_strictMono_tendsto_clm_of_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (R : ℝ) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ell : H →L[ℝ] ℝ,
        Tendsto (fun n => ell (u (φ n))) atTop (𝓝 (ell v))  := by
  have exists_strictMono_tendsto_inner_of_norm_le :
      ∃ (v : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ z : H,
        Tendsto (fun n => inner ℝ (u (φ n)) z) atTop
          (𝓝 (inner ℝ v z)) := by
    let f : ℕ → WeakDual ℝ H := fun n =>
      StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u n))
    have hf : ∀ n, f n ∈ WeakDual.toStrongDual ⁻¹'
        Metric.closedBall (0 : StrongDual ℝ H) R := by
      intro n
      rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
      change ‖InnerProductSpace.toDual ℝ H (u n) - 0‖ ≤ R
      simpa using hu n
    obtain ⟨ℓ, hℓ, φ, hφ, hlim⟩ :=
      (WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) R) hf
    let v : H :=
      (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual ℓ)
    refine ⟨v, φ, hφ, fun z => ?_⟩
    simpa [f, v, Function.comp_def] using
      ((WeakDual.eval_continuous z).tendsto ℓ).comp hlim
  obtain ⟨v, φ, hφ, hinner⟩ := exists_strictMono_tendsto_inner_of_norm_le
  refine ⟨v, φ, hφ, fun ell => ?_⟩
  let z := (InnerProductSpace.toDual ℝ H).symm ell
  simp_rw [← InnerProductSpace.toDual_symm_apply]
  simpa only [z, real_inner_comm] using hinner z

section
open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace


private theorem raw_integral_transport
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (mass source form : ℝ) (s f : α → ℝ)
    (hs : Integrable s μ) (hsf : Integrable (fun x => s x - f x) μ)
    (hmass : mass = -(∫ x, (s x - f x) ∂μ))
    (hsource : source = ∫ x, s x ∂μ) (hform : form = ∫ x, f x ∂μ) :
    mass = -source + form := by
  have hf : Integrable f μ := by
    refine (hs.sub hsf).congr (Eventually.of_forall fun x => ?_)
    change s x - (s x - f x) = f x
    ring
  calc
    mass = -(∫ x, (s x - f x) ∂μ) := hmass
    _ = -((∫ x, s x ∂μ) - ∫ x, f x ∂μ) := by rw [integral_sub hs hf]
    _ = -(∫ x, s x ∂μ) + ∫ x, f x ∂μ := by ring
    _ = -source + form := by rw [← hsource, ← hform]


private theorem integral_eq_of_ae_of_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f =ᵐ[μ] g) :
    (∫ x, f x ∂μ) = ∫ x, g x ∂μ := by
  have hL1 :=
    (Integrable.toL1_eq_toL1_iff f g hf hg).2 hfg
  calc
    (∫ x, f x ∂μ) = ∫ x, (hf.toL1 f) x ∂μ := (L1.integral_of_fun_eq_integral hf).symm
    _ = ∫ x, (hg.toL1 g) x ∂μ := congrArg (fun w : α →₁[μ] ℝ => ∫ x, w x ∂μ) hL1
    _ = ∫ x, g x ∂μ := L1.integral_of_fun_eq_integral hg

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
  (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
  (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat
    d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

/-- The literal finite Galerkin mass/source/form pairing identity. -/
def reverseTimeGalerkinPrimal_pairing_identity_prop {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam) (hΩ : IsOpen Ω) (hΩbounded :
      Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat
      d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (v : galerkinSpace hΩ N) (eta :
      ReverseTimeScalarTest (r₁-r₀)) : Prop :=
  reverseTimeDualPairingRightCLM hΩ (r₁-r₀) (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv
    (eta.memLp_deriv ∞) (v : H10HilbertGraph hΩ))
      (reverseTimeGelfandCLM hΩ (r₁-r₀) (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
        a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)) =
    -reverseTimeDualPairingRightCLM hΩ (r₁-r₀) (reverseTimeSeparatedVTest hΩ eta (v :
      H10HilbertGraph hΩ)) (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) +
    reverseTimeDualPairingRightCLM hΩ (r₁-r₀) (reverseTimeSeparatedVTest hΩ eta (v :
      H10HilbertGraph hΩ))
      (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth
          hcSmooth hFSmooth hLower hcNonpos N initial))

private theorem reverseTimeGalerkinPrimal_pairing_identity_prop_intro
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (v : galerkinSpace hΩ N)
    (eta : ReverseTimeScalarTest (r₁ - r₀)) (U : ReverseTimeL2V hΩ (r₁ - r₀))
    (hU : U = reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (h : reverseTimeDualPairingRightCLM hΩ (r₁-r₀)
        (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv (eta.memLp_deriv ∞)
          (v : H10HilbertGraph hΩ))
        (reverseTimeGelfandCLM hΩ (r₁-r₀) U) =
      -reverseTimeDualPairingRightCLM hΩ (r₁-r₀)
          (reverseTimeSeparatedVTest hΩ eta (v : H10HilbertGraph hΩ))
          (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) +
        reverseTimeDualPairingRightCLM hΩ (r₁-r₀)
          (reverseTimeSeparatedVTest hΩ eta (v : H10HilbertGraph hΩ))
          (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth U)) :
    reverseTimeGalerkinPrimal_pairing_identity_prop r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial v eta := by
  subst U
  simpa only [reverseTimeGalerkinPrimal_pairing_identity_prop] using h

/-- The finite Galerkin pairing identity for canonical quotient representatives. -/
theorem reverseTimeGalerkinPrimal_pairing_identity
    (N : ℕ) (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (v : galerkinSpace hΩ N)
    (eta : ReverseTimeScalarTest (r₁ - r₀)) :
    reverseTimeGalerkinPrimal_pairing_identity_prop r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial v eta   := by
  have integrable_reverseTimeNegativeSourceRaw_mul_test {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (F : ℝ → PDE.Vec d → ℝ) (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (eta : ReverseTimeScalarTest (r₁ - r₀)) (v : H10HilbertGraph hΩ) :
      Integrable (fun τ => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ v * eta τ)
      (reverseTimeVolume (r₁ - r₀)) := by
    let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
    let z := reverseTimeSeparatedVTest hΩ eta v
    have hPair :=
      integrable_reverseTimeDualPairing hΩ (r₁ - r₀) z S
    refine hPair.congr ?_
    filter_upwards [(memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).coeFn_toLp,
      ae_reverseTimeSeparatedVTest hΩ eta v] with τ hS hz
    dsimp only [S, z]
    calc
      reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
          (reverseTimeSeparatedVTest hΩ eta v τ) =
          reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (eta τ • v) :=
        congrArg (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ) hz
      _ = eta τ * reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ v := by
        rw [ContinuousLinearMap.map_smul]
        rfl
      _ = eta τ * reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ v :=
        congrArg (fun g => eta τ * g v) hS
      _ = reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ v * eta τ := mul_comm _ _
  have reverseTimeSpatialForm_pairing_eq_integral {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ) (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (u : ReverseTimeL2V hΩ (r₁ - r₀)) (eta : ReverseTimeScalarTest (r₁ - r₀)) (v : H10HilbertGraph hΩ) :
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTest hΩ eta v)
        (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth u) =
      ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau
        ∂reverseTimeVolume (r₁ - r₀) := by
    let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u
    let z := reverseTimeSeparatedVTest hΩ eta v
    change reverseTimeDualPairingRightCLM hΩ (r₁ - r₀) z A = _
    have hAeval : ∀ᵐ tau ∂reverseTimeVolume (r₁ - r₀),
        ∀ w : H10HilbertGraph hΩ,
          A tau w = reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) w := by
      simpa only [A] using
        (ae_reverseTimeSpatialFormBochnerAction_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth u)
    calc
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀) z A =
          reverseTimeDualPairingCLM hΩ (r₁ - r₀) A z :=
        reverseTimeDualPairingRightCLM_apply hΩ (r₁ - r₀) z A
      _ = ∫ tau, A tau (z tau) ∂reverseTimeVolume (r₁ - r₀) :=
        reverseTimeDualPairingCLM_apply hΩ (r₁ - r₀) A z
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hAeval, ae_reverseTimeSeparatedVTest hΩ eta v] with tau hA hz
        calc
          A tau (z tau) = A tau (eta tau • v) := congrArg (A tau) hz
          _ = eta tau * A tau v := by
            rw [ContinuousLinearMap.map_smul]
            rfl
          _ = eta tau * reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v :=
            congrArg (eta tau * ·) (hA v)
          _ = reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau := mul_comm _ _
  let U := reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth
    hcSmooth hFSmooth hLower hcNonpos N initial
  let raw := reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth
    hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  have hUraw : U =ᵐ[reverseTimeVolume (r₁ - r₀)] raw := by
    simpa only [U, raw] using ae_reverseTimeGalerkinPrimal_eq_raw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  obtain ⟨hMassRaw, hResidualRaw, hRawIdentity⟩ :=
    reverseTimeGalerkinPrimal_compactTime r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth
      hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial v eta
  have hMassRaw' : Integrable (fun τ => inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
      (valueCLM hΩ (raw τ)) * eta.deriv τ) (reverseTimeVolume (r₁-r₀)) := by
    simpa only [raw] using hMassRaw
  have hMassCanonical : Integrable (fun τ => inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ))
      (valueCLM hΩ (U τ)) * eta.deriv τ) (reverseTimeVolume (r₁-r₀)) := by
    refine hMassRaw'.congr ?_
    filter_upwards [hUraw] with τ hτ
    rw [hτ]
  let massRaw : ℝ := ∫ τ, inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ)) (valueCLM hΩ (raw τ)) *
    eta.deriv τ ∂reverseTimeVolume (r₁ - r₀)
  have hMassPair : reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv (eta.memLp_deriv ∞) (v : H10HilbertGraph hΩ))
      (reverseTimeGelfandCLM hΩ (r₁ - r₀) U) = massRaw := by
    calc
      _ = ∫ τ, inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ)) (valueCLM hΩ (U τ)) * eta.deriv τ
        ∂reverseTimeVolume (r₁ - r₀) :=
        reverseTimeGelfand_pairing_multiplier_eq_integral hΩ U eta.deriv (eta.memLp_deriv ∞) (v :
          H10HilbertGraph hΩ)
      _ = massRaw := by
        dsimp only [massRaw]
        apply integral_eq_of_ae_of_integrable (reverseTimeVolume (r₁-r₀))
          (fun τ => inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ)) (valueCLM hΩ (U τ)) * eta.deriv
            τ)
          (fun τ => inner ℝ (valueCLM hΩ (v : H10HilbertGraph hΩ)) (valueCLM hΩ (raw τ)) *
            eta.deriv τ)
          hMassCanonical hMassRaw'
        filter_upwards [hUraw] with τ hτ
        rw [hτ]
  have hSourceRaw := integrable_reverseTimeNegativeSourceRaw_mul_test r₀ r₁ h₀₁ hΩ hΩbounded F
    hFSmooth eta (v : H10HilbertGraph hΩ)
  have hSourcePair := reverseTimeNegativeSource_pairing_eq_integral_raw r₀ r₁ h₀₁ hΩ hΩbounded F
    hFSmooth eta (v : H10HilbertGraph hΩ)
  have hFormPair := reverseTimeSpatialForm_pairing_eq_integral r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth U eta (v : H10HilbertGraph hΩ)
  have hFormPairRaw : reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTest hΩ eta (v : H10HilbertGraph hΩ))
      (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
        U) =
      ∫ τ, reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ) * eta τ
        ∂reverseTimeVolume (r₁ - r₀) := by
    calc
      _ = ∫ τ, reverseTimeSpatialForm hΩ r₁ τ a b c (U τ) (v : H10HilbertGraph hΩ) * eta τ
        ∂reverseTimeVolume (r₁ - r₀) := hFormPair
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hUraw] with τ hτ
        rw [hτ]
  have hResidualRaw' : Integrable (fun τ =>
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph hΩ) -
        reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ)) * eta τ)
          (reverseTimeVolume (r₁-r₀)) := by
    simpa only [raw] using hResidualRaw
  have hDiffRaw : Integrable (fun τ =>
      reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph hΩ) *
        eta τ -
      reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ) * eta τ)
        (reverseTimeVolume (r₁-r₀)) := by
    refine hResidualRaw'.congr (Eventually.of_forall fun τ => ?_)
    change (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph
      hΩ) -
      reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ)) * eta τ =
      reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph hΩ) *
        eta τ -
      reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ) * eta τ
    exact sub_mul _ _ _
  have hRawIdentity' : massRaw = -∫ τ,
      (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph hΩ) *
        eta τ -
      reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ) * eta τ)
        ∂reverseTimeVolume (r₁-r₀) := by
    have hRawIdentity0 : massRaw = -∫ τ,
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph hΩ) -
        reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ)) * eta τ
          ∂reverseTimeVolume (r₁-r₀) := by
      simpa only [massRaw, raw] using hRawIdentity
    rw [hRawIdentity0]
    congr 1
    apply integral_eq_of_ae_of_integrable (reverseTimeVolume (r₁-r₀)) _ _ hResidualRaw' hDiffRaw
    filter_upwards with τ
    change (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph
      hΩ) -
      reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ)) * eta τ =
      reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v : H10HilbertGraph hΩ) *
        eta τ -
      reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ) * eta τ
    exact sub_mul _ _ _
  have hConcrete := raw_integral_transport (reverseTimeVolume (r₁-r₀)) _ _ _
    (fun τ => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (v :
      H10HilbertGraph hΩ) * eta τ)
    (fun τ => reverseTimeSpatialForm hΩ r₁ τ a b c (raw τ) (v : H10HilbertGraph hΩ) * eta τ)
    hSourceRaw hDiffRaw (hMassPair.trans hRawIdentity') hSourcePair hFormPairRaw
  have hU : U = reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial := rfl
  exact reverseTimeGalerkinPrimal_pairing_identity_prop_intro r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b
    c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial v eta U hU hConcrete

end
section

open Filter MeasureTheory Set
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
  (a : CoefficientField d)
  (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
  (haSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => a z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hbSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => b z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hcSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => c z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hFSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => F z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hLower : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

/-- The canonical reverse-time Galerkin primal curves possess a strictly monotone
subsequence converging under every continuous real linear functional. -/
theorem exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V hΩ (r₁ - r₀)) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ell : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ,
        Tendsto
          (fun n => ell
            (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (φ n) initial))
          atTop
          (𝓝 (ell U)) := by
  letI : TopologicalSpace.SeparableSpace (H10HilbertGraph hΩ) :=
    instSeparableSpaceH10HilbertGraph hΩ
  letI : MeasureTheory.SFinite (reverseTimeVolume (r₁ - r₀)) := by
    dsimp only [reverseTimeVolume]
    infer_instance
  letI : MeasurableSpace.CountablyGenerated ℝ := by infer_instance
  letI : MeasureTheory.IsSeparable (reverseTimeVolume (r₁ - r₀)) := by infer_instance
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : SecondCountableTopology (ReverseTimeL2V hΩ (r₁ - r₀)) :=
    MeasureTheory.Lp.SecondCountableTopology
  letI : TopologicalSpace.SeparableSpace (ReverseTimeL2V hΩ (r₁ - r₀)) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  exact exists_strictMono_tendsto_clm_of_norm_le
    (fun N => reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
    (reverseTimeGalerkinPrimalRadius r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial)
    (fun N => norm_reverseTimeGalerkinPrimal_le_radius
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial N)

end

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
  (a : CoefficientField d)
  (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
  (haSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => a z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hbSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => b z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hcSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => c z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hFSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => F z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hLower : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

/-- The quotient-level reverse-time identity against a fixed actual Galerkin test. -/
def reverseTimeGalerkinPrimal_fixed_test_identity_prop
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (U : ReverseTimeL2V hΩ (r₁ - r₀))
    (k : ℕ) (eta : ReverseTimeScalarTest (r₁ - r₀)) : Prop :=
  reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv
        (eta.memLp_deriv ∞) (galerkinVector hΩ k))
      (reverseTimeGelfandCLM hΩ (r₁ - r₀) U) =
    -reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTest hΩ eta (galerkinVector hΩ k))
        (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) +
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTest hΩ eta (galerkinVector hΩ k))
        (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded
          a b c haSmooth hbSmooth hcSmooth U)

/-- One common weakly convergent Galerkin subsequence satisfies the identity for every
fixed actual Galerkin vector and scalar time test. -/
theorem exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_fixedTests
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V hΩ (r₁ - r₀)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ ell : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ,
        Tendsto
          (fun n => ell
            (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
              a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
              (φ n) initial))
          atTop (𝓝 (ell U))) ∧
      ∀ (k : ℕ) (eta : ReverseTimeScalarTest (r₁ - r₀)),
        reverseTimeGalerkinPrimal_fixed_test_identity_prop
          r₀ r₁ h₀₁ hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth U k eta := by
  obtain ⟨U, φ, hφ, hclm⟩ :=
    exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial
  refine ⟨U, φ, hφ, hclm, ?_⟩
  intro k eta
  let hEtaDeriv :=
    eta.memLp_deriv ∞
  let massEll :=
    (reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv hEtaDeriv
        (galerkinVector hΩ k))).comp (reverseTimeGelfandCLM hΩ (r₁ - r₀))
  let formEll :=
    (reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTest hΩ eta (galerkinVector hΩ k))).comp
      (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded
        a b c haSmooth hbSmooth hcSmooth)
  let source : ℝ := reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
    (reverseTimeSeparatedVTest hΩ eta (galerkinVector hΩ k))
    (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)
  have hMass := hclm massEll
  have hForm := hclm formEll
  have hIndex : ∀ᶠ n in atTop, k + 1 ≤ φ n := by
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    exact hn.trans (hφ.id_le n)
  have hFinite :
      (fun n => massEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
          a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
          (φ n) initial)) =ᶠ[atTop]
      fun n => -source + formEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
          a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
          (φ n) initial) := by
    filter_upwards [hIndex] with n hn
    let v : galerkinSpace hΩ (φ n) := ⟨galerkinVector hΩ k,
      galerkinSpace_mono hΩ hn (by
        change galerkinVector hΩ k ∈ Submodule.span ℝ
          (Set.range fun i : Fin (k + 1) => galerkinVector hΩ i)
        apply Submodule.subset_span
        exact ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩)⟩
    have h := reverseTimeGalerkinPrimal_pairing_identity
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (φ n) initial v eta
    simpa only [reverseTimeGalerkinPrimal_pairing_identity_prop, massEll, formEll,
      source, ContinuousLinearMap.comp_apply, v, hEtaDeriv] using h
  have hMass' := hMass
  have hForm' := hForm
  have hRight : Tendsto
      (fun n => -source + formEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
          a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
          (φ n) initial)) atTop (𝓝 (-source + formEll U)) :=
    (tendsto_const_nhds.neg).add hForm'
  have hLimit : massEll U = -source + formEll U :=
    tendsto_nhds_unique_of_eventuallyEq hMass' hRight hFinite
  simpa only [reverseTimeGalerkinPrimal_fixed_test_identity_prop, massEll, formEll,
    source, ContinuousLinearMap.comp_apply, hEtaDeriv] using hLimit

end
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder Matrix

/-- The reverse-time residual candidate in the Bochner dual carrier. -/
noncomputable def reverseTimeFormResidual
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    ReverseTimeL2VStar hΩ (r₁ - r₀) :=
  reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth -
    reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u

/-- On one event, the residual plus the literal spatial form is the
negative reverse-time source functional, simultaneously for all spatial tests. -/
theorem ae_reverseTimeFormResidual_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      ∀ hτ : τ ∈ Set.Ioo 0 (r₁ - r₀),
        ∀ v : H10HilbertGraph hΩ,
          reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth F hFSmooth u τ v +
            reverseTimeSpatialForm hΩ r₁ τ a b c (u τ) v =
          reverseTimeSourceFunctional hΩ
            (reverseTimeSourceSlice r₁ τ F
              (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
                r₀ r₁ hΩ hΩbounded F hFSmooth τ
                ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩)) v := by
  filter_upwards [
    ae_reverseTimeNegativeSource_apply r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth,
    ae_reverseTimeSpatialFormBochnerAction_apply r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u,
    Lp.coeFn_sub
      (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)
      (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth u)] with τ hSource hAction hSub
  intro hτ v
  rw [reverseTimeFormResidual, hSub, Pi.sub_apply, ContinuousLinearMap.sub_apply,
    hSource hτ, hAction v]
  abel

section
open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
  (a : CoefficientField d)
  (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
  (haSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => a z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hbSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => b z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hcSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => c z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hFSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => F z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hLower : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

/-- The quotient-level reverse-time identity against an arbitrary spatial test. -/
def reverseTimeGalerkinPrimal_arbitrary_test_identity_prop
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (U : ReverseTimeL2V hΩ (r₁ - r₀))
    (v : H10HilbertGraph hΩ)
    (eta : ReverseTimeScalarTest (r₁ - r₀)) : Prop :=
  reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv
        (eta.memLp_deriv ∞) v)
      (reverseTimeGelfandCLM hΩ (r₁ - r₀) U) =
    -reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTest hΩ eta v)
        (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) +
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTest hΩ eta v)
        (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded
          a b c haSmooth hbSmooth hcSmooth U)

/-- One common weakly convergent Galerkin subsequence satisfies the identity
for every spatial test and every scalar time test. -/
theorem exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_arbitraryTests
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V hΩ (r₁ - r₀)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ ell : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ,
        Tendsto
          (fun n => ell
            (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
              a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
              (φ n) initial))
          atTop (𝓝 (ell U))) ∧
      ∀ (v : H10HilbertGraph hΩ)
        (eta : ReverseTimeScalarTest (r₁ - r₀)),
        reverseTimeGalerkinPrimal_arbitrary_test_identity_prop
          r₀ r₁ h₀₁ hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth U v eta := by
  obtain ⟨U, φ, hφ, hclm, hfixed⟩ :=
    exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_fixedTests
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial
  refine ⟨U, φ, hφ, hclm, ?_⟩
  intro v eta
  have hvClosure : v ∈ closure (Set.range (galerkinVector hΩ)) := by
    rw [(denseRange_galerkinVector hΩ).closure_range]
    exact Set.mem_univ v
  obtain ⟨vN, hvN, hv⟩ := mem_closure_iff_seq_limit.mp hvClosure
  choose k hk using hvN
  let G := reverseTimeGelfandCLM hΩ (r₁ - r₀) U
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth U
  let mass : H10HilbertGraph hΩ → ℝ := fun w =>
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv (eta.memLp_deriv ∞) w) G
  let source : H10HilbertGraph hΩ → ℝ := fun w =>
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTest hΩ eta w) S
  let form : H10HilbertGraph hΩ → ℝ := fun w =>
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTest hΩ eta w) A
  have hMass : Tendsto (fun n => mass (vN n)) atTop (𝓝 (mass v)) := by
    change Tendsto
      (fun n => reverseTimeDualPairingCLM hΩ (r₁ - r₀) G
        (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv (eta.memLp_deriv ∞) (vN n)))
      atTop
      (𝓝 (reverseTimeDualPairingCLM hΩ (r₁ - r₀) G
        (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv (eta.memLp_deriv ∞) v)))
    exact (reverseTimeDualPairingCLM hΩ (r₁ - r₀) G).continuous.tendsto _ |>.comp
      (tendsto_reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv
        (eta.memLp_deriv ∞) hv)
  have hSource : Tendsto (fun n => source (vN n)) atTop (𝓝 (source v)) := by
    change Tendsto
      (fun n => reverseTimeDualPairingCLM hΩ (r₁ - r₀) S
        (reverseTimeSeparatedVTest hΩ eta (vN n)))
      atTop
      (𝓝 (reverseTimeDualPairingCLM hΩ (r₁ - r₀) S
        (reverseTimeSeparatedVTest hΩ eta v)))
    exact (reverseTimeDualPairingCLM hΩ (r₁ - r₀) S).continuous.tendsto _ |>.comp
      (tendsto_reverseTimeSeparatedVTest hΩ eta hv)
  have hForm : Tendsto (fun n => form (vN n)) atTop (𝓝 (form v)) := by
    change Tendsto
      (fun n => reverseTimeDualPairingCLM hΩ (r₁ - r₀) A
        (reverseTimeSeparatedVTest hΩ eta (vN n)))
      atTop
      (𝓝 (reverseTimeDualPairingCLM hΩ (r₁ - r₀) A
        (reverseTimeSeparatedVTest hΩ eta v)))
    exact (reverseTimeDualPairingCLM hΩ (r₁ - r₀) A).continuous.tendsto _ |>.comp
      (tendsto_reverseTimeSeparatedVTest hΩ eta hv)
  have hFixed : ∀ n, mass (vN n) = -source (vN n) + form (vN n) := by
    intro n
    simpa only [reverseTimeGalerkinPrimal_fixed_test_identity_prop, mass, source, form, G, S,
      A, hk n] using hfixed (k n) eta
  have hRight : Tendsto (fun n => -source (vN n) + form (vN n)) atTop
      (𝓝 (-source v + form v)) :=
    hSource.neg.add hForm
  have hLimit : mass v = -source v + form v :=
    tendsto_nhds_unique_of_eventuallyEq hMass hRight (Eventually.of_forall hFixed)
  simpa only [reverseTimeGalerkinPrimal_arbitrary_test_identity_prop, mass, source, form, G,
    S, A] using hLimit

end

local instance instResidualDerivativeReverseTimeL2VStarModule
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  MeasureTheory.Lp.instModule


private theorem reverseTimeDualPairingRightCLM_reverseTimeFormResidual
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (z : ReverseTimeL2V hΩ (r₁ - r₀)) :
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀) z
        (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth F hFSmooth u) =
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀) z
        (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) -
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀) z
        (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth u)  := by
  have reverseTimeDualPairingRightCLM_sub {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (z : ReverseTimeL2V hΩ T) (g₁ g₂ : ReverseTimeL2VStar hΩ T) : reverseTimeDualPairingRightCLM hΩ T z (g₁ - g₂) =
      reverseTimeDualPairingRightCLM hΩ T z g₁ -
        reverseTimeDualPairingRightCLM hΩ T z g₂ :=
    (reverseTimeDualPairingRightCLM hΩ T z).map_sub g₁ g₂
  rw [reverseTimeFormResidual]
  exact reverseTimeDualPairingRightCLM_sub hΩ (r₁ - r₀) z _ _

private theorem residual_pairing_algebra {m s a q : ℝ}
    (hm : m = -s + a) (hq : q = s - a) : m = -q := by
  linarith

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
  (a : CoefficientField d)
  (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
  (haSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => a z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hbSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => b z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hcSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => c z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hFSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => F z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hLower : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

/-- A common weak Galerkin subsequence converges to a curve whose Gelfand weak
time derivative is the concrete reverse-time form residual. -/
theorem exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_residual_derivative
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V hΩ (r₁ - r₀)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ ell : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ,
        Tendsto
          (fun n => ell
            (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
              a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
              (φ n) initial))
          atTop (𝓝 (ell U))) ∧
      HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
        (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth F hFSmooth U) := by
  obtain ⟨U, φ, hφ, hclm, hidentity⟩ :=
    exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_arbitraryTests
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial
  let T := r₁ - r₀
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth U
  refine ⟨U, φ, hφ, hclm, ?_⟩
  intro v eta
  let g := reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth F hFSmooth U
  let z := reverseTimeSeparatedVTest hΩ eta v
  let G := reverseTimeGelfandCLM hΩ T U
  have hEtaDeriv : MemLp eta.deriv (∞ : ℝ≥0∞) (reverseTimeVolume T) :=
    eta.memLp_deriv ∞
  refine ⟨integrable_reverseTimeWeakDerivative_left hΩ T U v eta,
    integrable_reverseTimeWeakDerivative_right hΩ T g v eta, ?_⟩
  have hmass := reverseTimeGelfand_pairing_multiplier_eq_integral
    hΩ U eta.deriv hEtaDeriv v
  have hleft :
      (∫ tau, inner ℝ (valueCLM hΩ v)
        (reverseTimeValueCLM hΩ T U tau) * eta.deriv tau
        ∂reverseTimeVolume T) =
      (∫ tau, inner ℝ (valueCLM hΩ v) (valueCLM hΩ (U tau)) * eta.deriv tau
        ∂reverseTimeVolume T) := by
    apply integral_congr_ae
    filter_upwards [coeFn_reverseTimeValueCLM hΩ T U] with tau hU
    rw [hU]
  have hright :
      reverseTimeDualPairingRightCLM hΩ T z g =
        ∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T := by
    rw [reverseTimeDualPairingRightCLM_apply,
      reverseTimeDualPairingCLM_apply]
    apply integral_congr_ae
    filter_upwards [ae_reverseTimeSeparatedVTest hΩ eta v] with tau hz
    rw [hz, ContinuousLinearMap.map_smul]
    exact mul_comm _ _
  let m : ℝ := reverseTimeDualPairingRightCLM hΩ T
    (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv hEtaDeriv v) G
  let s : ℝ := reverseTimeDualPairingRightCLM hΩ T z S
  let f : ℝ := reverseTimeDualPairingRightCLM hΩ T z A
  let q : ℝ := reverseTimeDualPairingRightCLM hΩ T z g
  have hid : m = -s + f := by
    simpa only [m, s, f, T, S, A, z, G,
      reverseTimeGalerkinPrimal_arbitrary_test_identity_prop] using hidentity v eta
  have hres := reverseTimeDualPairingRightCLM_reverseTimeFormResidual
    r₀ r₁ h₀₁ hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth U z
  have hq : q = s - f := by
    dsimp only [q, s, f, g]
    exact hres
  have hpairScalar : m = -q := residual_pairing_algebra hid hq
  have hpair :
      reverseTimeDualPairingRightCLM hΩ T
          (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv hEtaDeriv v) G =
        -reverseTimeDualPairingRightCLM hΩ T z g := by
    change m = -q
    exact hpairScalar
  calc
    (∫ tau, inner ℝ (valueCLM hΩ v)
        (reverseTimeValueCLM hΩ T U tau) * eta.deriv tau
        ∂reverseTimeVolume T) =
        ∫ tau, inner ℝ (valueCLM hΩ v) (valueCLM hΩ (U tau)) * eta.deriv tau
          ∂reverseTimeVolume T := hleft
    _ = reverseTimeDualPairingRightCLM hΩ T
          (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv hEtaDeriv v) G := hmass.symm
    _ = -reverseTimeDualPairingRightCLM hΩ T z g := hpair
    _ = -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) := congrArg Neg.neg hright

end HypoellipticAleksandrov.Parabolic.Dirichlet

