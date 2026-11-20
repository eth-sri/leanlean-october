module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialL2MultiplierDifference
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Multiplier realization of the reverse-time spatial form -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

section Multipliers

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}

theorem reverseTime_mem_closedCylinder {τ : ℝ} (hτ : τ ∈ Icc 0 (r₁ - r₀))
    {y : PDE.Vec d} (hy : y ∈ Ω) : (r₁ - τ, y) ∈ scalarParabolicClosedCylinder r₀ r₁ Ω :=
  ⟨⟨by linarith [hτ.2], by linarith [hτ.1]⟩, subset_closure hy⟩

/-- Time-uniform essential bounds for a scalar coefficient on the spatial slices. -/
structure ReverseTimeMultiplierData (r₀ r₁ : ℝ) (Ω : Set (PDE.Vec d))
    (q : TimeVelocity d → ℝ) where
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  measurable : ∀ τ : Icc 0 (r₁ - r₀), AEStronglyMeasurable (fun y => q (r₁ - τ.1, y)) (PDE.volumeOn Ω)
  ae_le : ∀ τ : Icc 0 (r₁ - r₀), ∀ᵐ y ∂PDE.volumeOn Ω, ‖q (r₁ - τ.1, y)‖ ≤ bound

variable {q : TimeVelocity d → ℝ}

/-- A continuous coefficient has one uniform multiplier bound on a bounded cylinder. -/
def ReverseTimeMultiplierData.ofContinuousOn (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hq : ContinuousOn q (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    ReverseTimeMultiplierData r₀ r₁ Ω q := by
  let h := (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩb).exists_bound_of_continuousOn hq
  refine ⟨max h.choose 0, le_max_right _ _, ?_, ?_⟩
  · intro τ
    exact (hq.comp (Continuous.prodMk_right _).continuousOn
      (fun _ hy => reverseTime_mem_closedCylinder τ.2 hy)).aestronglyMeasurable hΩ.measurableSet
  · intro τ
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    exact (h.choose_spec _ (reverseTime_mem_closedCylinder τ.2 hy)).trans (le_max_left _ _)

section
variable (e : ReverseTimeMultiplierData r₀ r₁ Ω q) (τ : Icc 0 (r₁ - r₀))
include e τ

/-- Multiplication by one spatial slice, as an operator on `L²`. -/
def ReverseTimeMultiplierData.operator : PDE.ScalarLp Ω 2 →L[ℝ] PDE.ScalarLp Ω 2 :=
  scalarL2Multiplier _ (e.measurable τ) e.bound e.bound_nonneg (e.ae_le τ)

theorem ReverseTimeMultiplierData.norm_operator_le : ‖e.operator τ‖ ≤ e.bound :=
  ContinuousLinearMap.opNorm_le_bound _ e.bound_nonneg
    (norm_scalarL2Multiplier_apply_le _ _ _ _ _)

end

private theorem exists_delta_ae_norm_reverseTime_sub_le
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (q : TimeVelocity d → ℝ)
    (hq : ContinuousOn q (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (τ : Set.Icc 0 (r₁ - r₀)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ : Set.Icc 0 (r₁ - r₀),
      dist σ τ < δ →
        ∀ᵐ y ∂PDE.volumeOn Ω,
          ‖q (r₁ - σ.1, y) - q (r₁ - τ.1, y)‖ ≤ ε := by
  have hUC :=
    IsCompact.uniformContinuousOn_of_continuous
      (isCompact_scalarParabolicClosedCylinder r₀ r₁ hΩbounded) hq
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδ, hδUC⟩ := hUC ε hε
  refine ⟨δ, hδ, ?_⟩
  intro σ hστ
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
  have hσK := reverseTime_mem_closedCylinder σ.2 hy
  have hτK := reverseTime_mem_closedCylinder τ.2 hy
  have hdist : dist (r₁ - σ.1, y) (r₁ - τ.1, y) < δ := by
    rw [dist_prod_same_right, Real.dist_eq]
    change |σ.1 - τ.1| < δ at hστ
    rw [show r₁ - σ.1 - (r₁ - τ.1) = τ.1 - σ.1 by ring, abs_sub_comm]
    exact hστ
  exact (hδUC _ hσK _ hτK hdist).le

/-- Slice multiplication is continuous in operator norm for jointly continuous coefficients. -/
theorem ReverseTimeMultiplierData.continuous_operator (e : ReverseTimeMultiplierData r₀ r₁ Ω q)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hq : ContinuousOn q (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    Continuous e.operator := by
  rw [continuous_iff_continuousAt]
  intro τ
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hsub⟩ := exists_delta_ae_norm_reverseTime_sub_le r₀ r₁ hΩ hΩb q hq τ (half_pos hε)
  refine ⟨δ, hδ, fun σ hστ => ?_⟩
  rw [dist_eq_norm]
  exact (norm_scalarL2Multiplier_sub_le_of_ae_norm_sub_le _ _ _ _ _ _ _ _ _ _ _
    (half_pos hε).le (hsub σ hστ)).trans_lt (half_lt_self hε)

end Multipliers

section Form

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
variable {a : CoefficientField d} {b : ℝ → PDE.Vec d → PDE.Vec d} {c : ℝ → PDE.Vec d → ℝ}

/-- Uniform multiplier data for each of the three coefficient families in the spatial form. -/
structure ReverseTimeSpatialFormEvidence (r₀ r₁ : ℝ) (Ω : Set (PDE.Vec d))
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ) where
  principal (i j : Fin d) : ReverseTimeMultiplierData r₀ r₁ Ω (fun z => a z.1 z.2 i j)
  drift (j : Fin d) : ReverseTimeMultiplierData r₀ r₁ Ω
    (fun z => scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j)
  scalar : ReverseTimeMultiplierData r₀ r₁ Ω (Function.uncurry c)

theorem continuousOn_of_smoothOnNeighborhood {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {K : Set E}
    (h : IsSmoothOnNeighborhood f K) : ContinuousOn f K := by
  obtain ⟨V, _, hKV, hV⟩ := h
  exact hV.continuousOn.mono hKV

theorem principal_continuousOn
    (ha : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (i j : Fin d) : ContinuousOn (fun z : TimeVelocity d => a z.1 z.2 i j)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) :=
  (continuous_apply j).comp_continuousOn
    ((continuous_apply i).comp_continuousOn (continuousOn_of_smoothOnNeighborhood ha))

theorem drift_continuousOn
    (ha : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hb : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (j : Fin d) : ContinuousOn (fun z : TimeVelocity d => scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) :=
  ((continuous_apply j).comp_continuousOn
    (continuousOn_scalarSpatialCoefficientDivergence_of_smoothOnNeighborhood r₀ r₁ a ha)).sub
    ((continuous_apply j).comp_continuousOn (continuousOn_of_smoothOnNeighborhood hb))

/-- Smooth coefficient fields supply simultaneous evidence for all terms of the form. -/
def ReverseTimeSpatialFormEvidence.ofSmooth (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (ha : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hb : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hc : IsSmoothOnClosedCylinder r₀ r₁ Ω c) :
    ReverseTimeSpatialFormEvidence r₀ r₁ Ω a b c :=
  ⟨fun i j => .ofContinuousOn hΩ hΩb (principal_continuousOn ha i j),
    fun j => .ofContinuousOn hΩ hΩb (drift_continuousOn ha hb j),
    .ofContinuousOn hΩ hΩb (continuousOn_of_smoothOnNeighborhood hc)⟩

variable (hΩ : IsOpen Ω)

/-- One spatial gradient coordinate, as a continuous linear map. -/
def spatialGradientCoord (i : Fin d) : H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω 2 :=
  (PDE.hilbertVectorLpCoord Ω 2 i).comp (gradientCLM hΩ)

section
variable (L R : H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω 2)
include R

section
variable (M : PDE.ScalarLp Ω 2 →L[ℝ] PDE.ScalarLp Ω 2)
include M

/-- Pulling back a multiplier pairing along two spatial `L²` components. -/
def multiplierPairing : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ :=
  R.toSesqForm.comp (M.comp L)

private theorem multiplierPairing_apply (u v : H10HilbertGraph hΩ) :
    multiplierPairing hΩ L R M u v = inner ℝ (M (L u)) (R v) := rfl

end

private theorem multiplierPairing_continuous
    {M : Icc 0 (r₁ - r₀) → PDE.ScalarLp Ω 2 →L[ℝ] PDE.ScalarLp Ω 2} (hM : Continuous M) :
    Continuous (fun τ => multiplierPairing hΩ L R (M τ)) :=
  (hM.clm_comp_const L).const_clm_comp R.toSesqForm

end

variable (e : ReverseTimeSpatialFormEvidence r₀ r₁ Ω a b c)

def ReverseTimeSpatialFormEvidence.principalTerm (i j : Fin d) (τ : Icc 0 (r₁ - r₀)) :=
  multiplierPairing hΩ (spatialGradientCoord hΩ j) (spatialGradientCoord hΩ i) ((e.principal i j).operator τ)

def ReverseTimeSpatialFormEvidence.driftTerm (j : Fin d) (τ : Icc 0 (r₁ - r₀)) :=
  multiplierPairing hΩ (spatialGradientCoord hΩ j) (valueCLM hΩ) ((e.drift j).operator τ)

section
variable (τ : Icc 0 (r₁ - r₀))
include τ

def ReverseTimeSpatialFormEvidence.scalarTerm :=
  multiplierPairing hΩ (valueCLM hΩ) (valueCLM hΩ) (e.scalar.operator τ)

/-- The operator associated with the raw form, using bounded measurable slice data. -/
def ReverseTimeSpatialFormEvidence.operator :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ :=
  (∑ i, ∑ j, e.principalTerm hΩ i j τ) + (∑ j, e.driftTerm hΩ j τ) - e.scalarTerm hΩ τ

end

theorem ReverseTimeSpatialFormEvidence.operator_apply (e : ReverseTimeSpatialFormEvidence r₀ r₁ Ω a b c)
    (τ : Icc 0 (r₁ - r₀)) (u v : H10HilbertGraph hΩ) :
    e.operator hΩ τ u v = reverseTimeSpatialForm hΩ r₁ τ.1 a b c u v := by
  simp only [operator, principalTerm, driftTerm, scalarTerm, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, multiplierPairing_apply, spatialGradientCoord,
    ContinuousLinearMap.comp_apply, ReverseTimeMultiplierData.operator]
  symm
  exact reverseTimeSpatialForm_eq_multiplierInner_of_sliceEvidence hΩ r₁ τ.1 a b c u v
    (fun i j => (e.principal i j).bound) (fun i j => (e.principal i j).bound_nonneg)
    (fun i j => (e.principal i j).measurable τ) (fun i j => (e.principal i j).ae_le τ)
    (fun j => (e.drift j).bound) (fun j => (e.drift j).bound_nonneg)
    (fun j => (e.drift j).measurable τ) (fun j => (e.drift j).ae_le τ)
    e.scalar.bound e.scalar.bound_nonneg (e.scalar.measurable τ) (e.scalar.ae_le τ)

private theorem norm_multiplierPairing_le (L R : H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω 2)
    (M : PDE.ScalarLp Ω 2 →L[ℝ] PDE.ScalarLp Ω 2) (C : ℝ) (hC : ‖M‖ ≤ C) :
    ‖multiplierPairing hΩ L R M‖ ≤ ‖R‖ * C * ‖L‖ := by
  have hn := (norm_nonneg _).trans hC
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg (norm_nonneg _) hn) (norm_nonneg _))
  intro u
  change ‖R.toSesqForm (M (L u))‖ ≤ _
  calc
    _ ≤ ‖R‖ * ‖M (L u)‖ := ContinuousLinearMap.toSesqForm_apply_norm_le
    _ ≤ ‖R‖ * (C * (‖L‖ * ‖u‖)) := by
      gcongr
      exact (M.le_opNorm _).trans (by gcongr; exact L.le_opNorm _)
    _ = _ := by ring

private theorem norm_form_sum_le {E ι : Type*} [SeminormedAddCommGroup E] [Fintype ι]
    {P : ι → ι → E} {D : ι → E} {S : E}
    {p : ι → ι → ℝ} {d : ι → ℝ} {s : ℝ}
    (hp : ∀ i j, ‖P i j‖ ≤ p i j) (hd : ∀ j, ‖D j‖ ≤ d j) (hs : ‖S‖ ≤ s) :
    ‖(∑ i, ∑ j, P i j) + (∑ j, D j) - S‖ ≤ (∑ i, ∑ j, p i j) + (∑ j, d j) + s := by
  calc
    _ ≤ ‖(∑ i, ∑ j, P i j) + (∑ j, D j)‖ + ‖S‖ := norm_sub_le _ _
    _ ≤ (‖∑ i, ∑ j, P i j‖ + ‖∑ j, D j‖) + s :=
      add_le_add (norm_add_le _ _) hs
    _ ≤ _ := add_le_add_left (add_le_add
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hp i j)))
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hd j))) _

private theorem continuous_form_sum {X E ι : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [AddCommGroup E] [IsTopologicalAddGroup E] [Fintype ι]
    {P : ι → ι → X → E} {D : ι → X → E} {S : X → E}
    (hp : ∀ i j, Continuous (P i j)) (hd : ∀ j, Continuous (D j)) (hs : Continuous S) :
    Continuous (fun x => (∑ i, ∑ j, P i j x) + (∑ j, D j x) - S x) := by
  simp only [sub_eq_add_neg]
  exact ((continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => hp i j).add
    (continuous_finsetSum _ fun j _ => hd j)).add hs.neg

section
variable (e : ReverseTimeSpatialFormEvidence r₀ r₁ Ω a b c)

/-- One operator bound works on the entire time interval. -/
theorem ReverseTimeSpatialFormEvidence.exists_operator_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ, ‖e.operator hΩ τ‖ ≤ C := by
  let G := spatialGradientCoord hΩ
  let V := valueCLM hΩ
  let P : Fin d → Fin d → ℝ := fun i j => ‖G i‖ * (e.principal i j).bound * ‖G j‖
  let D : Fin d → ℝ := fun j => ‖V‖ * (e.drift j).bound * ‖G j‖
  let S := ‖V‖ * e.scalar.bound * ‖V‖
  have hp i j : 0 ≤ P i j := mul_nonneg (mul_nonneg (norm_nonneg _) (e.principal i j).bound_nonneg) (norm_nonneg _)
  have hd j : 0 ≤ D j := mul_nonneg (mul_nonneg (norm_nonneg _) (e.drift j).bound_nonneg) (norm_nonneg _)
  have hs : 0 ≤ S := mul_nonneg (mul_nonneg (norm_nonneg _) e.scalar.bound_nonneg) (norm_nonneg _)
  refine ⟨(∑ i, ∑ j, P i j) + (∑ j, D j) + S, ?_, ?_⟩
  · exact add_nonneg (add_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hp i j)
      (Finset.sum_nonneg fun j _ => hd j)) hs
  · intro τ
    unfold operator
    exact norm_form_sum_le (P := fun i j => e.principalTerm hΩ i j τ)
      (D := fun j => e.driftTerm hΩ j τ) (S := e.scalarTerm hΩ τ) (p := P) (d := D) (s := S)
      (fun i j => norm_multiplierPairing_le hΩ _ _ _ _ ((e.principal i j).norm_operator_le τ))
      (fun j => norm_multiplierPairing_le hΩ _ _ _ _ ((e.drift j).norm_operator_le τ))
      (norm_multiplierPairing_le hΩ _ _ _ _ (e.scalar.norm_operator_le τ))

/-- Smooth coefficients give a continuous curve of spatial form operators. -/
theorem ReverseTimeSpatialFormEvidence.continuous_operator (hΩb : Bornology.IsBounded Ω)
    (ha : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hb : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hc : IsSmoothOnClosedCylinder r₀ r₁ Ω c) :
    Continuous (e.operator hΩ) := by
  letI : IsTopologicalAddGroup (H10HilbertGraph hΩ →L[ℝ] H10HilbertGraphDual hΩ) := inferInstance
  unfold operator
  exact continuous_form_sum (P := e.principalTerm hΩ) (D := e.driftTerm hΩ) (S := e.scalarTerm hΩ)
    (fun i j => multiplierPairing_continuous hΩ _ _ ((e.principal i j).continuous_operator hΩ hΩb
      (principal_continuousOn ha i j)))
    (fun j => multiplierPairing_continuous hΩ _ _ ((e.drift j).continuous_operator hΩ hΩb
      (drift_continuousOn ha hb j)))
    (multiplierPairing_continuous hΩ _ _
      (e.scalar.continuous_operator hΩ hΩb (continuousOn_of_smoothOnNeighborhood hc)))

end

end Form

end HypoellipticAleksandrov.Parabolic.Dirichlet
