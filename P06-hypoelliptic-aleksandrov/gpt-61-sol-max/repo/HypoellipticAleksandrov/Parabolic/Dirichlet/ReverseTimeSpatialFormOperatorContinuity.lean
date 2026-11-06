module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2MultiplierDifference
public import Mathlib.Topology.UniformSpace.HeineCantor
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
public import PDEFoundation.Calculus.RegularityOrder


open private HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le from HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds


/-!
# Continuity of the reverse-time spatial form operator

This module proves operator-norm continuity for the local operator constructed
in ReverseTimeSpatialFormOperatorBase, using private fresh multiplier evidence
for the finite continuous term curve.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : PDE.VelocityRegion d}

variable (r₀ r₁ : ℝ)

variable (a : CoefficientField d)

private theorem continuousOn_reverseTimeCoefficientEntry_joint

      (i j : Fin d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ContinuousOn (fun z : TimeVelocity d => a z.1 z.2 i j)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
  rcases ha with ⟨V, hVopen, hKV, hV⟩

  exact ((contDiffOn_apply ℝ ℝ j Set.univ).comp ((contDiffOn_apply ℝ (Fin d → ℝ) i Set.univ).comp hV (by
        intro z hz
        exact Set.mem_univ _)) (by
    intro z hz
    simp)).continuousOn.mono hKV

private theorem continuousOn_reverseTimeDivergenceDriftEntry_joint

      (b : PDE.TimeVectorField d)
    (j : Fin d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ContinuousOn (fun z : TimeVelocity d =>
      scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
  have hdiv := continuousOn_scalarSpatialCoefficientDivergence_of_smoothOnNeighborhood
    r₀ r₁ a ha
  have heval : ContinuousOn (fun x : PDE.Vec d => x j) Set.univ :=
    (continuous_apply j).continuousOn
  rcases hb with ⟨V, hVopen, hKV, hV⟩

  exact heval.comp hdiv (by intro z hz; simp) |>.sub ((show ContDiffOn ℝ PDE.smoothOrder (fun z : TimeVelocity d => b z.1 z.2 j) V by
      exact (contDiffOn_apply ℝ ℝ j Set.univ).comp hV (by
        intro z hz
        exact Set.mem_univ _)).continuousOn.mono hKV)

private theorem continuousOn_reverseTimeScalarCoefficient_joint

     (c : PDE.TimeScalarField d)
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ContinuousOn (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) := by
  rcases hc with ⟨V, hVopen, hKV, hV⟩
  exact hV.continuousOn.mono hKV

variable (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)

include hΩ hΩbounded in
private theorem exists_delta_ae_norm_reverseTime_sub_le


    (q : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hq : ContinuousOn q (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (τ : Set.Icc 0 (r₁ - r₀)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ : Set.Icc 0 (r₁ - r₀),
      dist σ τ < δ →
        ∀ᵐ y ∂PDE.volumeOn Ω,
          ‖q (r₁ - σ.1, y) - q (r₁ - τ.1, y)‖ ≤ ε := by
  have hUC  :=
    IsCompact.uniformContinuousOn_of_continuous
      (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded) hq
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδ, hδUC⟩ := hUC ε hε
  refine ⟨δ, hδ, ?_⟩
  intro σ hστ
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy



  exact (hδUC _ (⟨by constructor <;> linarith [σ.2.1, σ.2.2], subset_closure hy⟩) _ (⟨by constructor <;> linarith [τ.2.1, τ.2.2], subset_closure hy⟩) (by
      rw [dist_prod_same_right, Real.dist_eq]
      change |σ.1 - τ.1| < δ at hστ
      rw [show r₁ - σ.1 - (r₁ - τ.1) = τ.1 - σ.1 by ring, abs_sub_comm]
      exact hστ)).le

section
variable (a : CoefficientField d)

include hΩ hΩbounded
private theorem continuousAt_reverseTimeCoefficientEntry_multiplier



    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω))
    (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j)
    (i j : Fin d) (τ : Set.Icc 0 (r₁ - r₀)) :
    ContinuousAt (fun σ : Set.Icc 0 (r₁ - r₀) =>
      scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
        (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j)) τ := by
  let sharedTerm_30c1392a94 := ((fun y => a (r₁ - τ.1) y i j))
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hsub⟩ := exists_delta_ae_norm_reverseTime_sub_le r₀ r₁ hΩ hΩbounded
    (fun z : TimeVelocity d => a z.1 z.2 i j)
    (continuousOn_reverseTimeCoefficientEntry_joint r₀ r₁ a i j ha) τ (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro σ hστ
  rw [dist_eq_norm]
  calc
    ‖scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
        (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j) -
        scalarL2Multiplier sharedTerm_30c1392a94
          (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)‖ ≤ ε / 2 :=
      norm_scalarL2Multiplier_sub_le_of_ae_norm_sub_le
        (fun y => a (r₁ - σ.1) y i j) sharedTerm_30c1392a94
        (hAMeas σ i j) (hAMeas τ i j) (Ca i j) (hCa i j) (hABound σ i j)
        (Ca i j) (hCa i j) (hABound τ i j) (ε / 2) (le_of_lt (half_pos hε))
        (hsub σ hστ)
    _ < ε := half_lt_self hε

private theorem continuousAt_reverseTimeDivergenceDriftEntry_multiplier


     (b : PDE.TimeVectorField d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      AEStronglyMeasurable
        (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω))
    (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j)
    (j : Fin d) (τ : Set.Icc 0 (r₁ - r₀)) :
    ContinuousAt (fun σ : Set.Icc 0 (r₁ - r₀) =>
      scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
        (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j)) τ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hsub⟩ := exists_delta_ae_norm_reverseTime_sub_le r₀ r₁ hΩ hΩbounded
    (fun z : TimeVelocity d => scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j)
    (continuousOn_reverseTimeDivergenceDriftEntry_joint r₀ r₁ a b j ha hb) τ (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro σ hστ
  rw [dist_eq_norm]
  calc
    ‖scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
        (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j) -
        scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
          (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)‖ ≤ ε / 2 :=
      norm_scalarL2Multiplier_sub_le_of_ae_norm_sub_le
        (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
        (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
        (hDriftMeas σ j) (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound σ j)
        (Cd j) (hCd j) (hDriftBound τ j) (ε / 2) (le_of_lt (half_pos hε))
        ((id (hsub σ hστ)))
    _ < ε := half_lt_self hε
end


include hΩ hΩbounded in
private theorem continuousAt_reverseTimeScalarCoefficient_multiplier


    (c : PDE.TimeScalarField d)
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀),
      AEStronglyMeasurable
        (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω))
    (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)
    (τ : Set.Icc 0 (r₁ - r₀)) :
    ContinuousAt (fun σ : Set.Icc 0 (r₁ - r₀) =>
      scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
        (hScalarMeas σ) Cc hCc (hScalarBound σ)) τ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hsub⟩ := exists_delta_ae_norm_reverseTime_sub_le r₀ r₁ hΩ hΩbounded
    (fun z : TimeVelocity d => c z.1 z.2)
    (continuousOn_reverseTimeScalarCoefficient_joint r₀ r₁ c hc) τ (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro σ hστ
  rw [dist_eq_norm]
  calc
    ‖scalarL2Multiplier ((reverseTimeScalarCoefficient r₁ c σ.1))
        (hScalarMeas σ) Cc hCc (hScalarBound σ) -
        scalarL2Multiplier ((reverseTimeScalarCoefficient r₁ c τ.1))
          (hScalarMeas τ) Cc hCc (hScalarBound τ)‖ ≤ ε / 2 :=
      norm_scalarL2Multiplier_sub_le_of_ae_norm_sub_le
        ((reverseTimeScalarCoefficient r₁ c σ.1))
        ((reverseTimeScalarCoefficient r₁ c τ.1))
        (hScalarMeas σ) (hScalarMeas τ) Cc hCc (hScalarBound σ)
        Cc hCc (hScalarBound τ) (ε / 2) (le_of_lt (half_pos hε))
        (hsub σ hστ)
    _ < ε := half_lt_self hε




variable (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d) (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j) (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j, AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω)) (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j, ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j) (i j : Fin d)

variable (τ : Set.Icc 0 (r₁ - r₀))

private def reverseTimeSpatialFormPrincipalTerm

      :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun u v =>
        inner ℝ
          (scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
            (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)
            (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
          (PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ v)))
      (by
        intro u w v
        simp only [map_add, inner_add_left])
      (by
        intro q u v
        simp only [map_smul, inner_smul_left, starRingEnd_apply, star_trivial, smul_eq_mul])
      (by
        intro u v w
        simp only [map_add, inner_add_right])
      (by
        intro q u v
        simp only [map_smul, inner_smul_right, smul_eq_mul]))
    (Ca i j * ‖gradientCLM hΩ‖ ^ 2)
    (fun u v => by
      rw [Real.norm_eq_abs]
      have hju :
          ‖PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)‖ ≤
            ‖gradientCLM hΩ‖ * ‖u‖ :=
        (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le j _).trans
          (ContinuousLinearMap.le_opNorm _ _)
      have hiv :
          ‖PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ v)‖ ≤
            ‖gradientCLM hΩ‖ * ‖v‖ :=
        (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le i _).trans
          (ContinuousLinearMap.le_opNorm _ _)
      calc
        |inner ℝ
            (scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
              (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)
              (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
            (PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ v))| ≤
            ‖scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
              (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)
              (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))‖ *
              ‖PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ v)‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ (Ca i j *
              ‖PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)‖) *
              ‖PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ v)‖ := mul_le_mul_of_nonneg_right
            (norm_scalarL2Multiplier_apply_le _ _ _ _ _ _) (norm_nonneg _)
        _ ≤ (Ca i j * (‖gradientCLM hΩ‖ * ‖u‖)) *
              (‖gradientCLM hΩ‖ * ‖v‖) := mul_le_mul
            (mul_le_mul_of_nonneg_left hju (hCa i j))
            hiv
            (norm_nonneg _)
            (mul_nonneg (hCa i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        _ = (Ca i j * ‖gradientCLM hΩ‖ ^ 2) * ‖u‖ * ‖v‖ := by ring)

private theorem reverseTimeSpatialFormPrincipalTerm_apply

      (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ u v =
      inner ℝ
        (scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
          (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
        (PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ v)) := rfl

variable (σ τ : Set.Icc 0 (r₁ - r₀))

private theorem reverseTimeSpatialFormPrincipalTerm_sub_apply

      (u v : H10HilbertGraph hΩ) :
    (reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j σ -
      reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ) u v =
      inner ℝ
        ((scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
            (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j) -
          scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
            (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j))
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
        (PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ v)) := by
  let sharedTerm_270f979483 := (inner ℝ
    (scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j) (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j)
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
    (PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ v)))
  let sharedTerm_bdf78be646 := (inner ℝ
    (scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j) (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)
      (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
    (PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ v)))
  rw [ContinuousLinearMap.sub_apply]
  rw [ContinuousLinearMap.sub_apply]
  rw [reverseTimeSpatialFormPrincipalTerm_apply
    hΩ r₀ r₁ a Ca hCa hAMeas hABound i j σ u v]

  calc
    _ = (sharedTerm_270f979483) -
          sharedTerm_bdf78be646 :=
      congrArg (fun z : ℝ =>
        sharedTerm_270f979483 - z) (reverseTimeSpatialFormPrincipalTerm_apply
              hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ u v)
    _ = _ := (inner_sub_left _ _ _).symm.trans
        (congrArg (fun z => inner ℝ z _)
          (ContinuousLinearMap.sub_apply _ _ _).symm)

private theorem norm_reverseTimeSpatialFormPrincipalTerm_sub_le

      :
    ‖reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j σ -
      reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ‖ ≤
      ‖gradientCLM hΩ‖ ^ 2 *
        ‖scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
            (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j) -
          scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j)
            (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j)‖ := by
  let sharedTerm_bb9e79561b := (scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j) (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j))
  let sharedTerm_bbdd983dc0 := (scalarL2Multiplier (fun y => a (r₁ - τ.1) y i j) (hAMeas τ i j) (Ca i j) (hCa i j) (hABound τ i j))
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) ?_
  intro u v
  rw [reverseTimeSpatialFormPrincipalTerm_sub_apply
    hΩ r₀ r₁ a Ca hCa hAMeas hABound i j σ τ u v]
  have hju :
      ‖PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)‖ ≤
        ‖gradientCLM hΩ‖ * ‖u‖ :=
    (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le j _).trans
      (ContinuousLinearMap.le_opNorm _ _)
  have hiv :
      ‖PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ v)‖ ≤
        ‖gradientCLM hΩ‖ * ‖v‖ :=
    (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le i _).trans
      (ContinuousLinearMap.le_opNorm _ _)
  calc
    ‖inner ℝ
        ((sharedTerm_bb9e79561b -
          sharedTerm_bbdd983dc0)
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
        (PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ v))‖ ≤
        ‖(sharedTerm_bb9e79561b -
          sharedTerm_bbdd983dc0)
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))‖ *
          ‖PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ v)‖ :=
      norm_inner_le_norm _ _
    _ ≤ (‖sharedTerm_bb9e79561b -
          sharedTerm_bbdd983dc0‖ *
          ‖PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)‖) *
          ‖PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ v)‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖sharedTerm_bb9e79561b -
          sharedTerm_bbdd983dc0‖ *
          (‖gradientCLM hΩ‖ * ‖u‖)) *
          (‖gradientCLM hΩ‖ * ‖v‖) := by
      gcongr
    _ = (‖gradientCLM hΩ‖ ^ 2 *
          ‖sharedTerm_bb9e79561b -
            sharedTerm_bbdd983dc0‖) * ‖u‖ * ‖v‖ := by
      ring

end HypoellipticAleksandrov.Parabolic.Dirichlet

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d) (b : PDE.TimeVectorField d) (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j) (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j, AEStronglyMeasurable (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω)) (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j, ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j) (j : Fin d)

variable (τ : Set.Icc 0 (r₁ - r₀))

private def reverseTimeSpatialFormDriftTerm
      :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun u v =>
        inner ℝ
          (scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
            (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)
            (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
          (valueCLM hΩ v))
      (by
        intro u w v
        simp only [map_add, inner_add_left])
      (by
        intro q u v
        simp only [map_smul, inner_smul_left, starRingEnd_apply, star_trivial, smul_eq_mul])
      (by
        intro u v w
        simp only [map_add, inner_add_right])
      (by
        intro q u v
        simp only [map_smul, inner_smul_right, smul_eq_mul]))
    (Cd j * ‖gradientCLM hΩ‖ * ‖valueCLM hΩ‖)
    (fun u v => by
      rw [Real.norm_eq_abs]
      have hju :
          ‖PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)‖ ≤
            ‖gradientCLM hΩ‖ * ‖u‖ :=
        (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le j _).trans
          (ContinuousLinearMap.le_opNorm _ _)
      have hv : ‖valueCLM hΩ v‖ ≤ ‖valueCLM hΩ‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      calc
        |inner ℝ
            (scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
              (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)
              (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
            (valueCLM hΩ v)| ≤
            ‖scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
              (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)
              (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))‖ *
              ‖valueCLM hΩ v‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ (Cd j *
              ‖PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)‖) *
              ‖valueCLM hΩ v‖ := mul_le_mul_of_nonneg_right
            (norm_scalarL2Multiplier_apply_le _ _ _ _ _ _) (norm_nonneg _)
        _ ≤ (Cd j * (‖gradientCLM hΩ‖ * ‖u‖)) *
              (‖valueCLM hΩ‖ * ‖v‖) := mul_le_mul
            (mul_le_mul_of_nonneg_left hju (hCd j))
            hv
            (norm_nonneg _)
            (mul_nonneg (hCd j) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        _ = (Cd j * ‖gradientCLM hΩ‖ * ‖valueCLM hΩ‖) * ‖u‖ * ‖v‖ := by ring)

private theorem reverseTimeSpatialFormDriftTerm_apply
      (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ u v =
      inner ℝ
        (scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
          (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
        (valueCLM hΩ v) := rfl

variable (σ τ : Set.Icc 0 (r₁ - r₀))

private theorem reverseTimeSpatialFormDriftTerm_sub_apply
      (u v : H10HilbertGraph hΩ) :
    (reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j σ -
      reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ) u v =
      inner ℝ
        ((scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
            (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j) -
          scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
            (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j))
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
        (valueCLM hΩ v) := by
  let sharedTerm_2262579536 := (inner ℝ
    (scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j) (hDriftMeas σ j) (Cd j) (hCd j)
      (hDriftBound σ j) (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
    (valueCLM hΩ v))
  let sharedTerm_9b6bd73f54 := (inner ℝ
    (scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (hDriftMeas τ j) (Cd j) (hCd j)
      (hDriftBound τ j) (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
    (valueCLM hΩ v))
  rw [ContinuousLinearMap.sub_apply]
  rw [ContinuousLinearMap.sub_apply]
  rw [reverseTimeSpatialFormDriftTerm_apply
    hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j σ u v]

  calc
    _ = (sharedTerm_2262579536) -
          sharedTerm_9b6bd73f54 :=
      congrArg (fun z : ℝ =>
        sharedTerm_2262579536 - z) (reverseTimeSpatialFormDriftTerm_apply
              hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ u v)
    _ = _ := (inner_sub_left _ _ _).symm.trans
        (congrArg (fun z => inner ℝ z _)
          (ContinuousLinearMap.sub_apply _ _ _).symm)

private theorem norm_reverseTimeSpatialFormDriftTerm_sub_le
      :
    ‖reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j σ -
      reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ‖ ≤
      (‖gradientCLM hΩ‖ * ‖valueCLM hΩ‖) *
        ‖scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
            (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j) -
          scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j)
            (hDriftMeas τ j) (Cd j) (hCd j) (hDriftBound τ j)‖ := by
  let sharedTerm_90c8531180 := ((scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j) (hDriftMeas σ j) (Cd j) (hCd j)
      (hDriftBound σ j) -
    scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (hDriftMeas τ j) (Cd j) (hCd j)
      (hDriftBound τ j)))
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) ?_
  intro u v
  rw [reverseTimeSpatialFormDriftTerm_sub_apply
    hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j σ τ u v]
  have hju :
      ‖PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)‖ ≤
        ‖gradientCLM hΩ‖ * ‖u‖ :=
    (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.norm_hilbertVectorLpCoord_le j _).trans
      (ContinuousLinearMap.le_opNorm _ _)

  calc
    ‖inner ℝ
        (sharedTerm_90c8531180
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)))
        (valueCLM hΩ v)‖ ≤
        ‖sharedTerm_90c8531180
          (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u))‖ *
          ‖valueCLM hΩ v‖ :=
      norm_inner_le_norm _ _
    _ ≤ (‖sharedTerm_90c8531180‖ *
          ‖PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u)‖) *
          ‖valueCLM hΩ v‖ := mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ (‖sharedTerm_90c8531180‖ *
          (‖gradientCLM hΩ‖ * ‖u‖)) *
          (‖valueCLM hΩ‖ * ‖v‖) := mul_le_mul
        (mul_le_mul_of_nonneg_left hju (norm_nonneg _))
        (ContinuousLinearMap.le_opNorm _ _)
        (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = (‖gradientCLM hΩ‖ * ‖valueCLM hΩ‖) *
        ‖sharedTerm_90c8531180‖ * ‖u‖ * ‖v‖ := by
      ring

end HypoellipticAleksandrov.Parabolic.Dirichlet

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (c : PDE.TimeScalarField d) (Cc : ℝ) (hCc : 0 ≤ Cc) (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), AEStronglyMeasurable (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω)) (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)

variable (τ : Set.Icc 0 (r₁ - r₀))

private def reverseTimeSpatialFormScalarTerm

     :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun u v =>
        inner ℝ
          (scalarL2Multiplier ((reverseTimeScalarCoefficient r₁ c τ.1))
            (hScalarMeas τ) Cc hCc (hScalarBound τ) (valueCLM hΩ u))
          (valueCLM hΩ v))
      (by
        intro u w v
        simp only [map_add, inner_add_left])
      (by
        intro q u v
        simp only [map_smul, inner_smul_left, starRingEnd_apply, star_trivial, smul_eq_mul])
      (by
        intro u v w
        simp only [map_add, inner_add_right])
      (by
        intro q u v
        simp only [map_smul, inner_smul_right, smul_eq_mul]))
    (Cc * ‖valueCLM hΩ‖ ^ 2)
    (fun u v => by
      rw [Real.norm_eq_abs]
      have hu : ‖valueCLM hΩ u‖ ≤ ‖valueCLM hΩ‖ * ‖u‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have hv : ‖valueCLM hΩ v‖ ≤ ‖valueCLM hΩ‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      calc
        |inner ℝ
            (scalarL2Multiplier ((reverseTimeScalarCoefficient r₁ c τ.1))
              (hScalarMeas τ) Cc hCc (hScalarBound τ) (valueCLM hΩ u))
            (valueCLM hΩ v)| ≤
            ‖scalarL2Multiplier ((reverseTimeScalarCoefficient r₁ c τ.1))
              (hScalarMeas τ) Cc hCc (hScalarBound τ) (valueCLM hΩ u)‖ *
              ‖valueCLM hΩ v‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ (Cc * ‖valueCLM hΩ u‖) * ‖valueCLM hΩ v‖ := mul_le_mul_of_nonneg_right
            (norm_scalarL2Multiplier_apply_le _ _ _ _ _ _) (norm_nonneg _)
        _ ≤ (Cc * (‖valueCLM hΩ‖ * ‖u‖)) *
              (‖valueCLM hΩ‖ * ‖v‖) := mul_le_mul
            (mul_le_mul_of_nonneg_left hu hCc)
            hv
            (norm_nonneg _)
            (mul_nonneg hCc (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        _ = (Cc * ‖valueCLM hΩ‖ ^ 2) * ‖u‖ * ‖v‖ := by ring)

private theorem reverseTimeSpatialFormScalarTerm_apply

     (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound τ u v =
      inner ℝ
        (scalarL2Multiplier ((reverseTimeScalarCoefficient r₁ c τ.1))
          (hScalarMeas τ) Cc hCc (hScalarBound τ) (valueCLM hΩ u))
        (valueCLM hΩ v) := rfl

variable (σ τ : Set.Icc 0 (r₁ - r₀))

private theorem reverseTimeSpatialFormScalarTerm_sub_apply

     (u v : H10HilbertGraph hΩ) :
    (reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound σ -
      reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound τ) u v =
      inner ℝ
        ((scalarL2Multiplier ((reverseTimeScalarCoefficient r₁ c σ.1))
            (hScalarMeas σ) Cc hCc (hScalarBound σ) -
          scalarL2Multiplier ((reverseTimeScalarCoefficient r₁ c τ.1))
            (hScalarMeas τ) Cc hCc (hScalarBound τ))
          (valueCLM hΩ u))
        (valueCLM hΩ v) := by
  let sharedTerm_327a244f84 := (inner ℝ
    (scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (hScalarMeas τ) Cc hCc (hScalarBound τ)
      (valueCLM hΩ u))
    (valueCLM hΩ v))
  let sharedTerm_641325d6ab := (inner ℝ
    (scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y) (hScalarMeas σ) Cc hCc (hScalarBound σ)
      (valueCLM hΩ u))
    (valueCLM hΩ v))
  rw [ContinuousLinearMap.sub_apply]
  rw [ContinuousLinearMap.sub_apply]
  rw [reverseTimeSpatialFormScalarTerm_apply
    hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound σ u v]

  calc
    _ = (sharedTerm_641325d6ab) -
          sharedTerm_327a244f84 :=
      congrArg (fun z : ℝ =>
        sharedTerm_641325d6ab - z) (reverseTimeSpatialFormScalarTerm_apply
              hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound τ u v)
    _ = _ := (inner_sub_left _ _ _).symm.trans
        (congrArg (fun z => inner ℝ z _)
          (ContinuousLinearMap.sub_apply _ _ _).symm)

private theorem norm_reverseTimeSpatialFormScalarTerm_sub_le

     :
    ‖reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound σ -
      reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound τ‖ ≤
      ‖valueCLM hΩ‖ ^ 2 *
        ‖scalarL2Multiplier ((reverseTimeScalarCoefficient r₁ c σ.1))
            (hScalarMeas σ) Cc hCc (hScalarBound σ) -
          scalarL2Multiplier ((reverseTimeScalarCoefficient r₁ c τ.1))
            (hScalarMeas τ) Cc hCc (hScalarBound τ)‖ := by
  let sharedTerm_723bc00df7 := ((scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y) (hScalarMeas σ) Cc hCc (hScalarBound σ) -
    scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (hScalarMeas τ) Cc hCc (hScalarBound τ)))
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) ?_
  intro u v
  rw [reverseTimeSpatialFormScalarTerm_sub_apply
    hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound σ τ u v]


  calc
    ‖inner ℝ
        (sharedTerm_723bc00df7
          (valueCLM hΩ u))
        (valueCLM hΩ v)‖ ≤
        ‖sharedTerm_723bc00df7
          (valueCLM hΩ u)‖ * ‖valueCLM hΩ v‖ :=
      norm_inner_le_norm _ _
    _ ≤ (‖sharedTerm_723bc00df7‖ * ‖valueCLM hΩ u‖) *
          ‖valueCLM hΩ v‖ := mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ (‖sharedTerm_723bc00df7‖ *
          (‖valueCLM hΩ‖ * ‖u‖)) * (‖valueCLM hΩ‖ * ‖v‖) := mul_le_mul
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
        (ContinuousLinearMap.le_opNorm _ _)
        (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = (‖valueCLM hΩ‖ ^ 2 *
        ‖sharedTerm_723bc00df7‖) * ‖u‖ * ‖v‖ := by
      ring

end HypoellipticAleksandrov.Parabolic.Dirichlet

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem continuousAt_of_norm_sub_le_mul
    {X Y Z : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    {f : X → Y} {g : X → Z} {x : X} (K : ℝ) (hK : 0 ≤ K)
    (hsub : ∀ y, ‖g y - g x‖ ≤ K * ‖f y - f x‖)
    (hf : ContinuousAt f x) : ContinuousAt g x := by
  rw [Metric.continuousAt_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := hf (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  rw [dist_eq_norm]

  calc
    ‖g y - g x‖ ≤ K * ‖f y - f x‖ := hsub y
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left (show ‖f y - f x‖ < ε / (K + 1) by
        simpa only [dist_eq_norm] using hδf hy).le hK
    _ < ε := by
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ (by linarith)).2 (by nlinarith)

section

variable {d : ℕ} {Ω : PDE.VelocityRegion d}
variable (hΩ : IsOpen Ω) (r₀ r₁ : ℝ) (a : CoefficientField d)
variable (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)
variable (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
variable (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
  AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω))
variable (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
  ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j)
variable (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
variable (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
  AEStronglyMeasurable
    (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω))
variable (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
  ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j)
variable (Cc : ℝ) (hCc : 0 ≤ Cc)
variable (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀),
  AEStronglyMeasurable
    (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω))
variable (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀),
  ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)

variable (hΩbounded : Bornology.IsBounded Ω)

section
variable (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω))

include hΩbounded haSmooth
private theorem continuousAt_reverseTimeSpatialFormPrincipalTerm


    (i j : Fin d) (τ : Set.Icc 0 (r₁ - r₀)) :
    ContinuousAt
      (reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j) τ := continuousAt_of_norm_sub_le_mul
    (f := fun σ => scalarL2Multiplier (fun y => a (r₁ - σ.1) y i j)
      (hAMeas σ i j) (Ca i j) (hCa i j) (hABound σ i j))
    (g := reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j)
    (‖gradientCLM hΩ‖ ^ 2) (sq_nonneg _)
    (fun σ => norm_reverseTimeSpatialFormPrincipalTerm_sub_le hΩ r₀ r₁ a Ca hCa hAMeas
      hABound i j σ τ)
    (continuousAt_reverseTimeCoefficientEntry_multiplier r₀ r₁ hΩ hΩbounded a haSmooth Ca
      hCa hAMeas hABound i j τ)

private theorem continuousAt_reverseTimeSpatialFormDriftTerm


    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (j : Fin d) (τ : Set.Icc 0 (r₁ - r₀)) :
    ContinuousAt
      (reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j) τ := by
  let f : Set.Icc 0 (r₁ - r₀) →
      PDE.ScalarLp Ω (2 ) →L[ℝ] PDE.ScalarLp Ω (2 ) := fun σ =>
    scalarL2Multiplier (fun y => reverseTimeDivergenceDrift r₁ a b σ.1 y j)
      (hDriftMeas σ j) (Cd j) (hCd j) (hDriftBound σ j)
  refine continuousAt_of_norm_sub_le_mul (f := f)
    (g := reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j)
    (‖gradientCLM hΩ‖ * ‖valueCLM hΩ‖)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_ ?_
  · intro σ
    simpa only [f] using norm_reverseTimeSpatialFormDriftTerm_sub_le hΩ r₀ r₁ a b Cd hCd
      hDriftMeas hDriftBound j σ τ
  · simpa only [f] using
      (continuousAt_reverseTimeDivergenceDriftEntry_multiplier r₀ r₁ hΩ hΩbounded a b haSmooth
        hbSmooth Cd hCd hDriftMeas hDriftBound j τ)
end


include hΩbounded in
private theorem continuousAt_reverseTimeSpatialFormScalarTerm

    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (τ : Set.Icc 0 (r₁ - r₀)) :
    ContinuousAt
      (reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound) τ := continuousAt_of_norm_sub_le_mul
    (f := fun σ => scalarL2Multiplier (fun y => reverseTimeScalarCoefficient r₁ c σ.1 y)
      (hScalarMeas σ) Cc hCc (hScalarBound σ))
    (g := reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound)
    (‖valueCLM hΩ‖ ^ 2) (sq_nonneg _)
    (fun σ => norm_reverseTimeSpatialFormScalarTerm_sub_le hΩ r₀ r₁ c Cc hCc hScalarMeas
      hScalarBound σ τ)
    (continuousAt_reverseTimeScalarCoefficient_multiplier r₀ r₁ hΩ hΩbounded c hcSmooth Cc
      hCc hScalarMeas hScalarBound τ)

section
variable (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω))

include hΩbounded haSmooth
private theorem continuous_reverseTimeSpatialFormPrincipalTerm


    (i j : Fin d) :
    Continuous
      (reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j) := continuous_iff_continuousAt.2 (continuousAt_reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound hΩbounded haSmooth i j)

private theorem continuous_reverseTimeSpatialFormDriftTerm


    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (j : Fin d) :
    Continuous
      (reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j) := continuous_iff_continuousAt.2 (continuousAt_reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound hΩbounded haSmooth hbSmooth j)
end


include hΩbounded in
private theorem continuous_reverseTimeSpatialFormScalarTerm

    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    Continuous
      (reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound) := continuous_iff_continuousAt.2 (continuousAt_reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound hΩbounded hcSmooth)

private def reverseTimeSpatialFormTermCurve  :=
  fun τ =>
    (∑ i : Fin d, ∑ j : Fin d,
      reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ) +
    (∑ j : Fin d,
      reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ) -
    reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound τ

private theorem continuousAdd_reverseTimeSpatialFormOperator
    {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) :
    ContinuousAdd (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ) := by
  let htop : IsTopologicalAddGroup
      (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ) := inferInstance
  exact htop.toContinuousAdd

private theorem continuous_add_sub_explicit
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [AddCommGroup E]
    (hadd : ContinuousAdd E) (hneg : ContinuousNeg E)
    (p q s : X → E)
    (hp : Continuous p) (hq : Continuous q) (hs : Continuous s) :
    Continuous (fun x => p x + q x - s x) := by
  letI : ContinuousAdd E := hadd
  letI : ContinuousNeg E := hneg
  letI : ContinuousSub E := ⟨by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      hadd.continuous_add.comp
        (continuous_fst.prodMk (hneg.continuous_neg.comp continuous_snd))⟩
  exact (hp.add hq).sub hs

variable (hΩbounded : Bornology.IsBounded Ω) (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω))

include hΩbounded haSmooth in
private theorem continuous_reverseTimeSpatialFormPrincipalSum
     :
    Continuous (fun τ =>
      ∑ i : Fin d, ∑ j : Fin d,
        reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ) := @continuous_finset_sum (Fin d)
    (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ)
    (Set.Icc 0 (r₁ - r₀)) _ _ ContinuousLinearMap.addCommMonoid
    (continuousAdd_reverseTimeSpatialFormOperator hΩ)
    (fun i τ => ∑ j : Fin d,
      reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ)
    Finset.univ
    (fun i _ => @continuous_finset_sum (Fin d)
      (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ)
      (Set.Icc 0 (r₁ - r₀)) _ _ ContinuousLinearMap.addCommMonoid
      (continuousAdd_reverseTimeSpatialFormOperator hΩ)
      ((reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i))
      Finset.univ
      (fun j _ => continuous_reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas
        hABound hΩbounded haSmooth i j))

variable (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω))

include hΩbounded haSmooth hbSmooth
private theorem continuous_reverseTimeSpatialFormDriftSum

     :
    Continuous (fun τ =>
      ∑ j : Fin d,
        reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ) := @continuous_finset_sum (Fin d)
    (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ)
    (Set.Icc 0 (r₁ - r₀)) _ _ ContinuousLinearMap.addCommMonoid
    (continuousAdd_reverseTimeSpatialFormOperator hΩ)
    ((reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound))
    Finset.univ
    (fun j _ => continuous_reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas
      hDriftBound
      hΩbounded haSmooth hbSmooth j)

private theorem continuous_reverseTimeSpatialFormTermCurve


    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    Continuous (reverseTimeSpatialFormTermCurve hΩ r₀ r₁ a b c Ca hCa hAMeas hABound Cd hCd
      hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound) := by
  unfold reverseTimeSpatialFormTermCurve
  let htop : IsTopologicalAddGroup
      (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ) := inferInstance
  exact continuous_add_sub_explicit htop.toContinuousAdd htop.toContinuousNeg
    (fun τ => ∑ i : Fin d, ∑ j : Fin d,
      reverseTimeSpatialFormPrincipalTerm hΩ r₀ r₁ a Ca hCa hAMeas hABound i j τ)
    (fun τ => ∑ j : Fin d,
      reverseTimeSpatialFormDriftTerm hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound j τ)
    ((reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound))
    (continuous_reverseTimeSpatialFormPrincipalSum hΩ r₀ r₁ a Ca hCa hAMeas hABound
      hΩbounded haSmooth)
    (continuous_reverseTimeSpatialFormDriftSum hΩ r₀ r₁ a b Cd hCd hDriftMeas hDriftBound
      hΩbounded haSmooth hbSmooth)
    (continuous_reverseTimeSpatialFormScalarTerm hΩ r₀ r₁ c Cc hCc hScalarMeas hScalarBound
      hΩbounded hcSmooth)

end

section

variable {d : ℕ} {Ω : PDE.VelocityRegion d}
variable (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
variable (a : CoefficientField d) (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)
variable (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))
variable (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))
variable (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
  (scalarParabolicClosedCylinder r₀ r₁ Ω))

section

variable (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
variable (hAMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
  AEStronglyMeasurable (fun y => a (r₁ - τ.1) y i j) (PDE.volumeOn Ω))
variable (hABound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ i j,
  ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ.1) y i j‖ ≤ Ca i j)
variable (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
variable (hDriftMeas : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
  AEStronglyMeasurable (fun y => reverseTimeDivergenceDrift r₁ a b τ.1 y j) (PDE.volumeOn Ω))
variable (hDriftBound : ∀ τ : Set.Icc 0 (r₁ - r₀), ∀ j,
  ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeDivergenceDrift r₁ a b τ.1 y j‖ ≤ Cd j)
variable (Cc : ℝ) (hCc : 0 ≤ Cc)
variable (hScalarMeas : ∀ τ : Set.Icc 0 (r₁ - r₀),
  AEStronglyMeasurable (fun y => reverseTimeScalarCoefficient r₁ c τ.1 y) (PDE.volumeOn Ω))
variable (hScalarBound : ∀ τ : Set.Icc 0 (r₁ - r₀),
  ∀ᵐ y ∂PDE.volumeOn Ω, ‖reverseTimeScalarCoefficient r₁ c τ.1 y‖ ≤ Cc)

private theorem reverseTimeSpatialFormOperator_eq_termCurve (τ : Set.Icc 0 (r₁ - r₀)) :
    reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ =
      reverseTimeSpatialFormTermCurve hΩ r₀ r₁ a b c Ca hCa hAMeas hABound Cd hCd
        hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound τ := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rw [reverseTimeSpatialFormOperator_apply]
  simp only [reverseTimeSpatialFormTermCurve, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    reverseTimeSpatialFormPrincipalTerm_apply, reverseTimeSpatialFormDriftTerm_apply,
    reverseTimeSpatialFormScalarTerm_apply]
  exact reverseTimeSpatialForm_eq_multiplierInner_of_sliceEvidence hΩ r₁ τ.1 a b c u v
    Ca hCa (hAMeas τ) (hABound τ) Cd hCd (hDriftMeas τ) (hDriftBound τ) Cc hCc
      (hScalarMeas τ) (hScalarBound τ)

end

end

/-- The local reverse-time spatial operator is continuous in operator norm. -/
theorem continuous_reverseTimeSpatialFormOperator
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    Continuous (reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth) := by
  obtain ⟨Ca, Cd, Cc, hCa, hCd, hCc, hAMeas, hABound, hDriftMeas, hDriftBound,
    hScalarMeas, hScalarBound⟩ := exists_sliceMultiplierBounds_of_smoothOnNeighborhood r₀ r₁
      hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
  rw [show reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth = reverseTimeSpatialFormTermCurve hΩ r₀ r₁ a b c
        Ca hCa hAMeas hABound Cd hCd hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound by
    funext τ
    exact reverseTimeSpatialFormOperator_eq_termCurve r₀ r₁ h₀₁ hΩ hΩbounded a b c
      haSmooth hbSmooth hcSmooth Ca hCa hAMeas hABound Cd hCd hDriftMeas hDriftBound Cc hCc
      hScalarMeas hScalarBound τ]
  exact continuous_reverseTimeSpatialFormTermCurve hΩ r₀ r₁ a b c Ca hCa hAMeas hABound Cd hCd
    hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound hΩbounded haSmooth hbSmooth hcSmooth

end HypoellipticAleksandrov.Parabolic.Dirichlet
