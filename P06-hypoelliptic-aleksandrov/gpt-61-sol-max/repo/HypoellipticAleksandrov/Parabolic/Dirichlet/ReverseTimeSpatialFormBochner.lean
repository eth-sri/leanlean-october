module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperator
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Tactic.Bound



/-!
# Bochner action of the reverse-time spatial form

This module packages the continuous clamped local reverse-time spatial-form
operator as a bounded action on quotient-valued Bochner `L²` spaces.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

local instance reverseTimeL2VStarModule
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  Lp.instModule

local instance reverseTimeSpatialFormOperatorNormedAddCommGroup
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) :
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
    AEStronglyMeasurable (fun x => K x (u x)) μ := ((ContinuousLinearMap.apply ℝ F).flip).aestronglyMeasurable_comp₂ hK hu

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d) (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d) (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω))

variable (u : ReverseTimeL2V hΩ (r₁ - r₀))

/-- Pointwise representative of the Bochner spatial-form action. -/
def reverseTimeSpatialFormBochnerRaw

     : ℝ → H10HilbertGraphDual hΩ := fun τ =>
  reverseTimeSpatialFormOperatorClamp r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth τ (u τ)

private theorem aestronglyMeasurable_reverseTimeSpatialFormBochnerRaw

     :
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

variable (C : ℝ) (hC : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ u : H10HilbertGraph hΩ, ‖reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ u‖ ≤ C * ‖u‖)

variable (u : ReverseTimeL2V hΩ (r₁ - r₀))

include hC in
private theorem norm_reverseTimeSpatialFormBochnerRaw_le


     (τ : ℝ) :
    ‖reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u τ‖ ≤ C * ‖u τ‖ := by
  bound

include hC in
/-- The pointwise spatial-form action belongs to reverse-time L². -/
theorem memLp_reverseTimeSpatialFormBochnerRaw


     :
    MemLp (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u) (2 ) (reverseTimeVolume (r₁ - r₀)) := by
  refine (Lp.memLp u).of_le_mul (c := C)
    (aestronglyMeasurable_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth u) ?_
  exact Eventually.of_forall
    (norm_reverseTimeSpatialFormBochnerRaw_le r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC u)

/-- The spatial form acting on a reverse-time Bochner curve. -/
def reverseTimeSpatialFormBochnerRawAction


     : ReverseTimeL2VStar hΩ (r₁ - r₀) :=
  (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC u).toLp
    (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth u)

/-- The Bochner spatial-form action preserves addition. -/
theorem reverseTimeSpatialFormBochnerRawAction_map_add


    (u w : ReverseTimeL2V hΩ (r₁ - r₀)) :
    reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC (u + w) =
      reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC u +
      reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC w := by
    let sharedTerm_9de751d15f := ((memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth C hC w))
    let sharedTerm_f02caad464 := ((memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth C hC u))
    let sharedTerm_4d9f29b0a3 := (reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth C hC w)
    let sharedTerm_32e05755e8 := ((reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth C hC u))
    apply Lp.ext
    filter_upwards [
      (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC (u + w)).coeFn_toLp,
      sharedTerm_f02caad464.coeFn_toLp,
      sharedTerm_9de751d15f.coeFn_toLp,
      Lp.coeFn_add u w,
      Lp.coeFn_add
        sharedTerm_32e05755e8
        sharedTerm_4d9f29b0a3] with τ hsum hu hw huv hout
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
          sharedTerm_f02caad464.toLp
              (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
                haSmooth hbSmooth hcSmooth u) τ +
            sharedTerm_9de751d15f.toLp
              (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
                haSmooth hbSmooth hcSmooth w) τ
        rw [← hu, ← hw]
      _ = (sharedTerm_32e05755e8 +
          sharedTerm_4d9f29b0a3) τ := hout.symm

/-- The Bochner spatial-form action preserves scalar multiplication. -/
theorem reverseTimeSpatialFormBochnerRawAction_map_smul


    (q : ℝ) (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC (q • u) =
      q • reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC u := by
    let sharedTerm_2e14f21ba1 := ((memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth C hC u))
    let sharedTerm_e1cf45fa70 := ((reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth C hC u))
    apply Lp.ext
    filter_upwards [
      (memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth C hC (q • u)).coeFn_toLp,
      sharedTerm_2e14f21ba1.coeFn_toLp,
      Lp.coeFn_smul q u,
      Lp.coeFn_smul q
        sharedTerm_e1cf45fa70] with τ hqu hu hquv hout
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
        change _ = q • sharedTerm_2e14f21ba1.toLp
            (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
              haSmooth hbSmooth hcSmooth u) τ
        rw [← hu]
      _ = (q • sharedTerm_e1cf45fa70) τ := hout.symm

/-- The reverse-time Bochner spatial form as a linear map. -/
def reverseTimeSpatialFormBochnerRawLinearMap

     :
    ReverseTimeL2V hΩ (r₁ - r₀) →ₗ[ℝ] ReverseTimeL2VStar hΩ (r₁ - r₀) where
  toFun := reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC
  map_add' := reverseTimeSpatialFormBochnerRawAction_map_add r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC
  map_smul' := reverseTimeSpatialFormBochnerRawAction_map_smul r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC

private theorem norm_reverseTimeSpatialFormBochnerRawAction_le


    (u : ReverseTimeL2V hΩ (r₁ - r₀)) :
    ‖reverseTimeSpatialFormBochnerRawAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hC u‖ ≤ C * ‖u‖ := by
  let sharedTerm_b0d1d208ed := ((memLp_reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth C hC u))
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    sharedTerm_b0d1d208ed.coeFn_toLp] with τ hτ
  change ‖sharedTerm_b0d1d208ed.toLp
      (reverseTimeSpatialFormBochnerRaw r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth u) τ‖ ≤ C * ‖u τ‖
  rw [hτ]
  exact norm_reverseTimeSpatialFormBochnerRaw_le r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth C hC u τ

/-- The bounded linear Bochner action of the clamped reverse-time spatial form. -/
def reverseTimeSpatialFormBochnerAction
     :
    ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ReverseTimeL2VStar hΩ (r₁ - r₀) := by
  let sharedTerm_84c11ffc7e := ((exists_reverseTimeSpatialFormOperator_bound r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth))
  let C := Classical.choose sharedTerm_84c11ffc7e
  let hBound := (Classical.choose_spec sharedTerm_84c11ffc7e).2
  exact LinearMap.mkContinuous
    (reverseTimeSpatialFormBochnerRawLinearMap r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth C hBound)
    C
    (by
      solve_by_elim (maxDepth := 4) [norm_reverseTimeSpatialFormBochnerRawAction_le])

/-- One event represents the action simultaneously for all spatial tests. -/
theorem ae_reverseTimeSpatialFormBochnerAction_apply

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

end HypoellipticAleksandrov.Parabolic.Dirichlet
