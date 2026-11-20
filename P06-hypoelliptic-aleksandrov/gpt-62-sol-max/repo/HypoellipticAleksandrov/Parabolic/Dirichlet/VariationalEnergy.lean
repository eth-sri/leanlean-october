module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertIntegrationByParts
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTimeDerivativeUnique
public import HypoellipticAleksandrov.Parabolic.Dirichlet.IntegralGronwall
import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertRepresentativeAlgebra

/-!
# Reverse-time variational energy uniqueness

This file proves the literal difference-energy estimate and uniqueness for
reverse-time variational solutions of the homogeneous-lateral Dirichlet problem.
It does not construct solutions.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

local instance instReverseTimeL2VStarModuleEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  MeasureTheory.Lp.instModule

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- A literal common-event weak variational solution of the reversed,
homogeneous-lateral Dirichlet energy problem. -/
def IsReverseTimeVariationalEnergySolution
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g) : Prop :=
  reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu = initial ∧
  ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
    ∀ hτ : τ ∈ Set.Ioo 0 (r₁ - r₀),
    ∀ v : H10HilbertGraph hΩ,
      (g τ) v + reverseTimeSpatialForm hΩ r₁ τ a b c (u τ) v =
        reverseTimeSourceFunctional hΩ
          (reverseTimeSourceSlice r₁ τ F
            (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
              r₀ r₁ hΩ hΩbounded F hFSmooth τ
              ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩)) v

/-- The literal closed-time Gårding difference-energy inequality. -/
def HasReverseTimeDifferenceEnergyBound
    (r₀ r₁ lam K : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (v : ReverseTimeL2V hΩ (r₁ - r₀))
    (k : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdv : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) v k) : Prop :=
  ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc 0 (r₁ - r₀),
    ∀ ht : t ∈ Set.Icc 0 (r₁ - r₀), s ≤ t →
      ‖reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          u g hdu ⟨t, ht⟩ -
          reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          v k hdv ⟨t, ht⟩‖ ^ 2 -
        ‖reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          u g hdu ⟨s, hs⟩ -
          reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          v k hdv ⟨s, hs⟩‖ ^ 2 +
        lam * (∫ τ in Set.Ioc s t,
          ‖gradientCLM hΩ (u τ - v τ)‖ ^ 2
            ∂reverseTimeVolume (r₁ - r₀)) ≤
      2 * K * (∫ τ in Set.Ioc s t,
        ‖valueCLM hΩ (u τ - v τ)‖ ^ 2
          ∂reverseTimeVolume (r₁ - r₀))

private theorem reverseTimeSpatialForm_sub_left_of_smoothOnNeighborhood
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (u₁ u₂ v : H10HilbertGraph hΩ) :
    reverseTimeSpatialForm hΩ r₁ τ a b c (u₁ - u₂) v =
      reverseTimeSpatialForm hΩ r₁ τ a b c u₁ v -
        reverseTimeSpatialForm hΩ r₁ τ a b c u₂ v := by
  let e := ReverseTimeSpatialFormEvidence.ofSmooth hΩ hΩbounded haSmooth hbSmooth hcSmooth
  have he (u v) := e.operator_apply hΩ ⟨τ,hτ⟩ u v
  rw [← he, ← he, ← he, map_sub, ContinuousLinearMap.sub_apply]

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private theorem reverseTimeSpatialForm_sub_left_diagonal_of_smoothOnNeighborhood
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (u v : H10HilbertGraph hΩ) :
    reverseTimeSpatialForm hΩ r₁ τ a b c u (u - v) -
      reverseTimeSpatialForm hΩ r₁ τ a b c v (u - v) =
        reverseTimeSpatialForm hΩ r₁ τ a b c (u - v) (u - v) := by
  simpa using
    (reverseTimeSpatialForm_sub_left_of_smoothOnNeighborhood
      r₀ r₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ hτ u v (u - v)).symm

private theorem hasGelfandWeakTimeDerivative_sub {hΩ : IsOpen Ω} {T : ℝ} {hT : 0 < T}
    {u v : ReverseTimeL2V hΩ T} {g k : ReverseTimeL2VStar hΩ T}
    (hu : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (hv : HasGelfandWeakTimeDerivative hΩ T hT v k) :
    HasGelfandWeakTimeDerivative hΩ T hT (u - v) (g - k) := by
  simpa [sub_eq_add_neg] using hu.add (hv.smul (-1 : ℝ))

private theorem ae_reverseTimeVariationalEnergy_difference_equation
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu)
    (v : ReverseTimeL2V hΩ (r₁ - r₀))
    (k : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdv : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k)
    (hv : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial v k hdv) :
    ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      ∀ _hτ : τ ∈ Set.Ioo 0 (r₁ - r₀),
        ((g - k) τ) ((u - v) τ) + reverseTimeSpatialForm hΩ r₁ τ a b c
          ((u - v) τ) ((u - v) τ) = 0 := by
  rcases hu with ⟨_, huEq⟩
  rcases hv with ⟨_, hvEq⟩
  filter_upwards [huEq, hvEq, Lp.coeFn_sub u v, Lp.coeFn_sub g k] with τ huτ hvτ huv hgk
  intro hτ
  have hτcc : τ ∈ Set.Icc 0 (r₁ - r₀) := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  have huTest := huτ hτ (u τ - v τ)
  have hvTest := hvτ hτ (u τ - v τ)
  have hform := reverseTimeSpatialForm_sub_left_diagonal_of_smoothOnNeighborhood
    r₀ r₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ hτcc (u τ) (v τ)
  rw [huv, hgk]
  change ((g τ - k τ) (u τ - v τ)) +
    reverseTimeSpatialForm hΩ r₁ τ a b c (u τ - v τ) (u τ - v τ) = 0
  rw [ContinuousLinearMap.sub_apply]
  linarith

end

private theorem setIntegral_garding_of_ae
    {μ : Measure ℝ} (p G V : ℝ → ℝ) (lam K s t : ℝ)
    (hp : Integrable p μ) (hG : Integrable G μ) (hV : Integrable V μ)
    (hae : ∀ᵐ r ∂μ, 2 * p r + lam * G r ≤ 2 * K * V r) :
    2 * (∫ r in Set.Ioc s t, p r ∂μ) + lam * (∫ r in Set.Ioc s t, G r ∂μ) ≤
      2 * K * (∫ r in Set.Ioc s t, V r ∂μ) := by
  have hl : Integrable (fun r => 2 * p r + lam * G r) μ :=
    (hp.const_mul 2).add (hG.const_mul lam)
  have hr : Integrable (fun r => 2 * K * V r) μ := by
    simpa only [mul_assoc] using hV.const_mul (2 * K)
  have h := setIntegral_mono_ae_restrict hl.integrableOn hr.integrableOn
    (ae_restrict_of_ae hae : ∀ᵐ r ∂μ.restrict (Set.Ioc s t),
      2 * p r + lam * G r ≤ 2 * K * V r)
  rw [integral_add (hp.const_mul 2).restrict (hG.const_mul lam).restrict,
    integral_const_mul, integral_const_mul, integral_const_mul] at h
  exact h

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private theorem hasReverseTimeDifferenceEnergyBound_of_pointwise
    (r₀ r₁ lam K : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (v : ReverseTimeL2V hΩ (r₁ - r₀)) (k : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdv : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k)
    (hdiff : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) (u - v) (g - k))
    (hpoint : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      2 * ((g - k) τ) ((u - v) τ) + lam * ‖gradientCLM hΩ ((u - v) τ)‖ ^ 2 ≤
        2 * K * ‖valueCLM hΩ ((u - v) τ)‖ ^ 2) :
    HasReverseTimeDifferenceEnergyBound r₀ r₁ lam K h₀₁ hΩ u g hdu v k hdv := by
  intro s t hs ht hst
  have hrep := reverseTimeHilbertRepresentative_sub_eq hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
    u g hdu v k hdv hdiff
  have henergy := (reverseTimeHilbertRepresentative_spec hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
    (u - v) (g - k) hdiff).2 s t hs ht hst
  have hpair : Integrable (fun τ => ((g - k) τ) ((u - v) τ))
      (reverseTimeVolume (r₁ - r₀)) :=
    integrable_reverseTimeDualPairing hΩ (r₁ - r₀) (u - v) (g - k)
  have hgradMem : MemLp (fun τ => gradientCLM hΩ ((u - v) τ)) (2 : ℝ≥0∞)
      (reverseTimeVolume (r₁ - r₀)) :=
    (Lp.memLp (u - v)).continuousLinearMap_comp (gradientCLM hΩ)
  have hvalueMem : MemLp (fun τ => valueCLM hΩ ((u - v) τ)) (2 : ℝ≥0∞)
      (reverseTimeVolume (r₁ - r₀)) :=
    (Lp.memLp (u - v)).continuousLinearMap_comp (valueCLM hΩ)
  have hgrad : Integrable (fun τ => ‖gradientCLM hΩ ((u - v) τ)‖ ^ 2)
      (reverseTimeVolume (r₁ - r₀)) :=
    (memLp_two_iff_integrable_sq_norm hgradMem.aestronglyMeasurable).mp hgradMem
  have hvalue : Integrable (fun τ => ‖valueCLM hΩ ((u - v) τ)‖ ^ 2)
      (reverseTimeVolume (r₁ - r₀)) :=
    (memLp_two_iff_integrable_sq_norm hvalueMem.aestronglyMeasurable).mp hvalueMem
  have hint := setIntegral_garding_of_ae
    (fun τ => ((g - k) τ) ((u - v) τ))
    (fun τ => ‖gradientCLM hΩ ((u - v) τ)‖ ^ 2)
    (fun τ => ‖valueCLM hΩ ((u - v) τ)‖ ^ 2)
    lam K s t hpair hgrad hvalue hpoint
  have hgradIoc :
      (∫ τ in Set.Ioc s t, ‖gradientCLM hΩ ((u - v) τ)‖ ^ 2
        ∂reverseTimeVolume (r₁ - r₀)) =
      ∫ τ in Set.Ioc s t, ‖gradientCLM hΩ (u τ - v τ)‖ ^ 2
        ∂reverseTimeVolume (r₁ - r₀) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub u v)] with τ hτ
    rw [hτ]
    simp only [Pi.sub_apply]
  have hvalueIoc :
      (∫ τ in Set.Ioc s t, ‖valueCLM hΩ ((u - v) τ)‖ ^ 2
        ∂reverseTimeVolume (r₁ - r₀)) =
      ∫ τ in Set.Ioc s t, ‖valueCLM hΩ (u τ - v τ)‖ ^ 2
        ∂reverseTimeVolume (r₁ - r₀) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub u v)] with τ hτ
    rw [hτ]
    simp only [Pi.sub_apply]
  rw [hrep] at henergy
  change
    ‖reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu ⟨t, ht⟩ -
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k hdv ⟨t, ht⟩‖ ^ 2 -
      ‖reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu ⟨s, hs⟩ -
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k hdv ⟨s, hs⟩‖ ^ 2 =
      2 * (∫ r in Set.Ioc s t, ((g - k) r) ((u - v) r)
        ∂reverseTimeVolume (r₁ - r₀)) at henergy
  rw [hgradIoc, hvalueIoc] at hint
  rw [henergy]
  exact hint

/-- Smooth coefficient data supply a difference-energy constant before the
forcing, initial datum, solution curves, and time endpoints are chosen. -/
theorem exists_reverseTimeVariationalEnergy_difference_constant
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ F : ℝ → PDE.Vec d → ℝ,
      ∀ hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F,
      ∀ initial : PDE.ScalarLp Ω (2 : ℝ≥0∞),
      ∀ u : ReverseTimeL2V hΩ (r₁ - r₀),
      ∀ g : ReverseTimeL2VStar hΩ (r₁ - r₀),
      ∀ hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
        (sub_pos.mpr h₀₁) u g,
      ∀ _hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
        a b c F hFSmooth initial u g hdu,
      ∀ v : ReverseTimeL2V hΩ (r₁ - r₀),
      ∀ k : ReverseTimeL2VStar hΩ (r₁ - r₀),
      ∀ hdv : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
        (sub_pos.mpr h₀₁) v k,
      ∀ _hv : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
        a b c F hFSmooth initial v k hdv,
      HasReverseTimeDifferenceEnergyBound r₀ r₁ lam K h₀₁ hΩ
        u g hdu v k hdv := by
  obtain ⟨K, hK, hGarding⟩ :=
    reverseTimeSpatialForm_garding_of_smoothOnNeighborhood r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c haSmooth hbSmooth hcSmooth hLower hcNonpos
  refine ⟨K, hK, ?_⟩
  intro F hFSmooth initial u g hdu hu v k hdv hv
  let hdiff := hasGelfandWeakTimeDerivative_sub hdu hdv
  have hpde := ae_reverseTimeVariationalEnergy_difference_equation r₀ r₁ h₀₁ hΩ hΩbounded
    a b c F haSmooth hbSmooth hcSmooth hFSmooth initial u g hdu hu v k hdv hv
  have hpoint : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      2 * ((g - k) τ) ((u - v) τ) + lam * ‖gradientCLM hΩ ((u - v) τ)‖ ^ 2 ≤
        2 * K * ‖valueCLM hΩ ((u - v) τ)‖ ^ 2 := by
    filter_upwards [hpde, ae_restrict_mem measurableSet_Ioo] with τ hpdeτ hτ
    have hτcc : τ ∈ Set.Icc 0 (r₁ - r₀) := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
    have hgarding := hGarding τ hτcc ((u - v) τ)
    have heq := hpdeτ hτ
    linarith
  exact hasReverseTimeDifferenceEnergyBound_of_pointwise r₀ r₁ lam K h₀₁ hΩ
    u g hdu v k hdv hdiff hpoint

end

private theorem setIntegral_Ioc_reverseTimeVolume_eq_volume
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {T t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (∫ r in Set.Ioc 0 t, f r ∂reverseTimeVolume T) = ∫ r in Set.Ioc 0 t, f r := by
  rw [reverseTimeVolume, reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc,
    Measure.restrict_restrict measurableSet_Ioc]
  congr 2
  exact inter_eq_left.mpr (Set.Ioc_subset_Icc_self.trans fun r hr =>
    ⟨hr.1, hr.2.trans ht.2⟩)

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- Spatial observables have the same time integral on the Bochner representative
and on the continuous Hilbert representative extended to the real line. -/
theorem reverseTime_integral_representative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {hΩ : IsOpen Ω} {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    {w : ReverseTimeL2V hΩ T} {W : C(Icc 0 T, PDE.ScalarLp Ω 2)}
    (hW : ReverseTimeHilbertRepresentativeAgrees hΩ T w W)
    (F : ℝ → PDE.ScalarLp Ω 2 → E) :
    (∫ r in Ioc 0 t, F r (valueCLM hΩ (w r)) ∂reverseTimeVolume T) =
      ∫ r in Ioc 0 t, F r (IccExtend hT W r) := by
  rw [← setIntegral_Ioc_reverseTimeVolume_eq_volume _ ht]
  apply integral_congr_ae
  have h := hW.ae_IccExtend hT
  rw [← restrict_Ioo_eq_restrict_Icc] at h
  filter_upwards [ae_restrict_of_ae h] with r hr
  rw [hr]

private theorem reverseTimeL2V_eq_of_hilbertRepresentative_eq_zero
    (hΩ : IsOpen Ω) (T : ℝ)
    (u v : ReverseTimeL2V hΩ T)
    (W : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)))
    (hW : ReverseTimeHilbertRepresentativeAgrees hΩ T (u - v) W)
    (hWzero : ∀ t : ℝ, ∀ ht : t ∈ Set.Icc 0 T, W ⟨t, ht⟩ = 0) :
    u = v := by
  apply Lp.ext
  filter_upwards [hW, ae_restrict_mem measurableSet_Ioo, Lp.coeFn_sub u v]
    with τ hWτ hτ huv
  have hτcc : τ ∈ Set.Icc 0 T := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  have hvaluezero : valueCLM hΩ ((u - v) τ) = 0 := by
    rw [← hWτ hτ]
    exact hWzero τ hτcc
  have hdiffzero : (u - v) τ = 0 := by
    apply valueCLM_injective hΩ
    simpa only [ContinuousLinearMap.map_zero] using hvaluezero
  rw [huv] at hdiffzero
  simpa only [Pi.sub_apply] using sub_eq_zero.mp hdiffzero

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private theorem reverseTimeL2V_eq_of_differenceEnergyBound
    (r₀ r₁ lam K : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam) (hK : 0 ≤ K)
    (hΩ : IsOpen Ω)
    (u : ReverseTimeL2V hΩ (r₁ - r₀)) (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (v : ReverseTimeL2V hΩ (r₁ - r₀)) (k : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdv : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k)
    (htrace : reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu =
      reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k hdv)
    (hbound : HasReverseTimeDifferenceEnergyBound r₀ r₁ lam K h₀₁ hΩ
      u g hdu v k hdv) :
    u = v := by
  let hT : 0 < r₁ - r₀ := sub_pos.mpr h₀₁
  let hdiff : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) hT (u - v) (g - k) :=
    hasGelfandWeakTimeDerivative_sub hdu hdv
  let W := reverseTimeHilbertRepresentative hΩ (r₁ - r₀) hT (u - v) (g - k) hdiff
  have hW := (reverseTimeHilbertRepresentative_spec hΩ (r₁ - r₀) hT
    (u - v) (g - k) hdiff).1
  have hrep := reverseTimeHilbertRepresentative_sub_eq hΩ (r₁ - r₀) hT
    u g hdu v k hdv hdiff
  have hrep_at (t : ℝ) (ht : t ∈ Icc 0 (r₁ - r₀)) : W ⟨t, ht⟩ =
      reverseTimeHilbertRepresentative hΩ (r₁ - r₀) hT u g hdu ⟨t, ht⟩ -
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) hT v k hdv ⟨t, ht⟩ :=
    congrArg (fun z => z ⟨t, ht⟩) hrep
  have ht₀ : (0 : ℝ) ∈ Icc 0 (r₁ - r₀) := ⟨le_rfl, hT.le⟩
  have hWzero : W ⟨0, ht₀⟩ = 0 := by
    rw [hrep_at]
    change reverseTimeInitialTrace hΩ (r₁ - r₀) hT u g hdu -
      reverseTimeInitialTrace hΩ (r₁ - r₀) hT v k hdv = 0
    rw [htrace, sub_self]
  let F := IccExtend hT.le W
  have hE : ∀ t ∈ Icc 0 (r₁ - r₀), ‖F t‖ ^ 2 ≤ 2 * K * ∫ r in Ioc 0 t, ‖F r‖ ^ 2 := by
    intro t ht
    have henergy := hbound 0 t ht₀ ht ht.1
    rw [← hrep_at t ht, ← hrep_at 0 ht₀, hWzero, norm_zero, zero_pow (by decide), sub_zero] at henergy
    have hgrad : 0 ≤ ∫ r in Ioc 0 t, ‖gradientCLM hΩ (u r - v r)‖ ^ 2
        ∂reverseTimeVolume (r₁ - r₀) := integral_nonneg fun _ => sq_nonneg _
    have hvalue : (∫ r in Ioc 0 t, ‖valueCLM hΩ (u r - v r)‖ ^ 2
        ∂reverseTimeVolume (r₁ - r₀)) = ∫ r in Ioc 0 t, ‖F r‖ ^ 2 := by
      rw [← reverseTime_integral_representative hT.le ht hW (fun _ x => ‖x‖ ^ 2)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub u v)] with r hr
      rw [hr, Pi.sub_apply]
    rw [hvalue] at henergy
    simpa only [F, IccExtend_of_mem hT.le W ht] using
      (le_add_of_nonneg_right (mul_nonneg hlam.le hgrad)).trans henergy
  have hz := eq_zero_on_Icc_of_norm_sq_le_mul_integral hT (mul_nonneg (by norm_num) hK)
    F W.continuous.Icc_extend' hE
  apply reverseTimeL2V_eq_of_hilbertRepresentative_eq_zero hΩ (r₁ - r₀) u v W hW
  intro t ht
  simpa only [F, IccExtend_of_mem hT.le W ht] using hz t ht

/-- Two reverse-time variational energy solutions with common initial trace are equal. -/
theorem reverseTimeVariationalEnergySolution_unique
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (hFSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu)
    (v : ReverseTimeL2V hΩ (r₁ - r₀))
    (k : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdv : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) v k)
    (hv : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial v k hdv) :
    u = v ∧ g = k := by
  obtain ⟨K, hK, hboundAll⟩ :=
    exists_reverseTimeVariationalEnergy_difference_constant r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
      a b c haSmooth hbSmooth hcSmooth hLower hcNonpos
  have hbound := hboundAll F hFSmooth initial u g hdu hu v k hdv hv
  have htrace : reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu =
      reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k hdv := by
    calc
      reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g hdu = initial := hu.1
      _ = reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) v k hdv := hv.1.symm
  have huv : u = v := reverseTimeL2V_eq_of_differenceEnergyBound r₀ r₁ lam K h₀₁ hlam hK
    hΩ u g hdu v k hdv htrace hbound
  have hdv' : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u k :=
    hdv.congr huv.symm rfl
  exact ⟨huv, hdu.unique hdv'⟩

end
