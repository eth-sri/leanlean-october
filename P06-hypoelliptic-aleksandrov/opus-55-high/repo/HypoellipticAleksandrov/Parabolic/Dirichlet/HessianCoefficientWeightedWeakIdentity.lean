module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothNeighborhoodProduct
public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeSpacetimeTest
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedRawIntegrability

/-! # Coefficient-weighted weak Hessian identities

Proof-local prerequisites for the fixed-index weighted weak identity. -/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal BigOperators Matrix.Norms.Elementwise MatrixOrder
namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω O : Set (PDE.Vec d)} (r₀ r₁ : ℝ)

private theorem integrable_mul_compact_of_locallyIntegrableOn
     {S : Set (TimeVelocity d)} {f q : TimeVelocity d → ℝ}
    (hf : LocallyIntegrableOn f S volume) (hq : Continuous q)
    (hc : HasCompactSupport q) (hs : tsupport q ⊆ S) :
    Integrable (fun z => f z * q z) (timeVelocityVolumeOn S) := by
  have hfK := hf.integrableOn_compact_subset hs hc.isCompact
  have hp : IntegrableOn (fun z => f z * q z) (tsupport q) volume := by
    simpa using hfK.smul_continuousOn hq.continuousOn hc.isCompact
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hp |>.restrict
  intro z hz
  exact tsupport_mul_subset_right (subset_closure hz)

private theorem velocityGradient_mul_at
     (f q : TimeVelocity d → ℝ) (z : TimeVelocity d) (i : Fin d)
    (hf : DifferentiableAt ℝ f z) (hq : DifferentiableAt ℝ q z) :
    velocityGradient (f * q) z i =
      f z * velocityGradient q z i + q z * velocityGradient f z i := by
  unfold velocityGradient
  rw [fderiv_mul hf hq]
  simp

private theorem velocityGradient_tsupport_subset
     (q : TimeVelocity d → ℝ) (i : Fin d) :
    tsupport (fun z => velocityGradient q z i) ⊆ tsupport q := by
  unfold velocityGradient
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  intro hzero
  apply hz
  simp [hzero]


private theorem velocityGradient_eq_spatialSlice_fderiv
     {f : TimeVelocity d → ℝ} (z : TimeVelocity d) (i : Fin d)
    (hf : DifferentiableAt ℝ f z) :
    velocityGradient f z i =
      (fderiv ℝ (fun y : PDE.Vec d => f (z.1, y)) z.2) (PDE.basisVec i) := by
  have hs : HasFDerivAt (fun y : PDE.Vec d => f (z.1, y))
      ((fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d))) z.2 := by
    simpa using! hf.hasFDerivAt.comp z.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  rw [hs.fderiv]
  rfl

private theorem separatedBase_admissible
     {O : Set (PDE.Vec d)} (hO : IsOpen O) (τ₁ τ₂ : ℝ)
    (eta : OriginalTimeScalarTest τ₁ τ₂) (psi : PDE.WeakTestFunction O) :
    let base : TimeVelocity d → ℝ := fun z => eta z.1 * psi z.2
    ContDiff ℝ (⊤ : ℕ∞) base ∧ HasCompactSupport base ∧
      tsupport base ⊆ Set.Ioo τ₁ τ₂ ×ˢ O := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using!
      (eta.contDiff.comp contDiff_fst).mul (psi.contDiff.comp contDiff_snd)
  · simpa only [originalTimeSeparatedProduct] using!
      (originalTimeSeparatedProductSupportedIn eta psi).hasCompactSupport
  · intro z hz
    have hz' : z ∈ tsupport (eta : ℝ → ℝ) ×ˢ
        tsupport (psi : PDE.Vec d → ℝ) := by
      
      rw [show tsupport (fun w : TimeVelocity d => eta w.1 * psi w.2) =
          tsupport (eta : ℝ → ℝ) ×ˢ tsupport (psi : PDE.Vec d → ℝ) by
        rw [← tsupport_originalTimeSeparatedProductTestFunction hO]
        rfl] at hz
      exact hz
    exact ⟨eta.tsupport_subset hz'.1, psi.tsupport_subset hz'.2⟩

private theorem weighted_admissible
     {S K : Set (TimeVelocity d)} {c q : TimeVelocity d → ℝ}
    (hc : IsSmoothOnNeighborhood c K) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqCompact : HasCompactSupport q) (hqS : tsupport q ⊆ S) (hSK : S ⊆ K) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => c z * q z) ∧
      HasCompactSupport (fun z => c z * q z) ∧
      tsupport (fun z => c z * q z) ⊆ S := ⟨IsSmoothOnNeighborhood.contDiff_mul_of_tsupport_subset
      hc hq (hqS.trans hSK),
    hqCompact.mul_left, tsupport_mul_subset_right.trans hqS⟩

private theorem reverseTime_coefficient_smoothOn_closedCylinder
     {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (a : CoefficientField d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (i j : Fin d) :
    IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => reverseTimeCoefficient r₁ a z.1 z.2 i j)
      (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω) := IsSmoothOnNeighborhood.reverseTime r₁
    (reverseTimeCompactCylinder_mapsTo r₀ r₁)
    (IsSmoothOnNeighborhood.coefficientEntry a ha i j)

private theorem velocityGradient_separatedBase
     {O : Set (PDE.Vec d)} {τ₁ τ₂ : ℝ}
    (eta : OriginalTimeScalarTest τ₁ τ₂) (psi : PDE.WeakTestFunction O)
    (z : TimeVelocity d) (i : Fin d) :
    velocityGradient (fun w : TimeVelocity d => eta w.1 * psi w.2) z i =
      eta z.1 * psi.partialDeriv i z.2 := by
  have hbase : DifferentiableAt ℝ
      (fun w : TimeVelocity d => eta w.1 * psi w.2) z :=
    ((eta.contDiff.comp contDiff_fst).mul
      (psi.contDiff.comp contDiff_snd)).differentiable (by simp) z
  rw [velocityGradient_eq_spatialSlice_fderiv z i hbase]
  rw [fderiv_const_mul
    (psi.contDiff.differentiable (by simp) z.2) (eta z.1)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
    PDE.WeakTestFunction.partialDeriv]

private theorem velocityGradient_reverseTimeCoefficient_mul_separatedBase
     (τ₁ τ₂ : ℝ)
    (htime : Set.Ioo τ₁ τ₂ ⊆ reverseTimeOpenInterval (r₁ - r₀))
    (hOΩ : O ⊆ Ω) (a : CoefficientField d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (i j : Fin d)
    (eta : OriginalTimeScalarTest τ₁ τ₂) (psi : PDE.WeakTestFunction O)
    (z : TimeVelocity d) (hz : z ∈ Set.Ioo τ₁ τ₂ ×ˢ O) :
    velocityGradient (fun w : TimeVelocity d =>
        reverseTimeCoefficient r₁ a w.1 w.2 i j * (eta w.1 * psi w.2)) z i =
      reverseTimeCoefficient r₁ a z.1 z.2 i j *
          (eta z.1 * psi.partialDeriv i z.2) +
        (eta z.1 * psi z.2) *
          (fderiv ℝ
            (fun y : PDE.Vec d => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
            (PDE.basisVec i) := by
  let c : TimeVelocity d → ℝ := fun w =>
    reverseTimeCoefficient r₁ a w.1 w.2 i j
  let base : TimeVelocity d → ℝ := fun w => eta w.1 * psi w.2
  have ht := htime hz.1
  have hzK : z ∈ Set.Icc 0 _ ×ˢ closure Ω :=
    ⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, subset_closure (hOΩ hz.2)⟩
  have hcSmooth := reverseTime_coefficient_smoothOn_closedCylinder r₀ r₁ a ha i j
  have hcDiff : DifferentiableAt ℝ c z :=
    IsSmoothOnNeighborhood.differentiableAt hcSmooth hzK
  have hbaseDiff : DifferentiableAt ℝ base z :=
    ((eta.contDiff.comp contDiff_fst).mul
      (psi.contDiff.comp contDiff_snd)).differentiable (by simp) z
  change velocityGradient (c * base) z i = _
  rw [velocityGradient_mul_at c base z i hcDiff hbaseDiff,
    show velocityGradient base z i = eta z.1 * psi.partialDeriv i z.2 by
      exact velocityGradient_separatedBase eta psi z i,
    show velocityGradient c z i =
        (fderiv ℝ
          (fun y : PDE.Vec d => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
          (PDE.basisVec i) by
      exact velocityGradient_eq_spatialSlice_fderiv z i hcDiff]

/-- Weak integration by parts for one ordered Hessian entry against a
reverse-time coefficient-weighted separated test. -/
theorem reverseTime_coefficient_weighted_weak_identity
     (hO : IsOpen O) (hOΩ : O ⊆ Ω)
    (τ₁ τ₂ : ℝ)
    (htime : Set.Ioo τ₁ τ₂ ⊆ reverseTimeOpenInterval (r₁ - r₀))
    (a : CoefficientField d)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (Gij Hij : TimeVelocity d → ℝ)
    (hGloc : LocallyIntegrableOn Gij
      (Set.Ioo τ₁ τ₂ ×ˢ O) volume)
    (hHloc : LocallyIntegrableOn Hij
      (Set.Ioo τ₁ τ₂ ×ˢ O) volume)
    (i j : Fin d)
    (hweak : HasWeakVelocityPartialDerivOn
      (Set.Ioo τ₁ τ₂ ×ˢ O) i Gij Hij)
    (eta : OriginalTimeScalarTest τ₁ τ₂)
    (psi : PDE.WeakTestFunction O) :
    let grouped : TimeVelocity d → ℝ := fun z =>
      Gij z *
        (reverseTimeCoefficient r₁ a z.1 z.2 i j *
            (eta z.1 * psi.partialDeriv i z.2) +
          (eta z.1 * psi z.2) *
            (fderiv ℝ
              (fun y : PDE.Vec d =>
                reverseTimeCoefficient r₁ a z.1 y i j) z.2)
              (PDE.basisVec i))
    let hessianPair : TimeVelocity d → ℝ := fun z =>
      Hij z *
        (reverseTimeCoefficient r₁ a z.1 z.2 i j *
          (eta z.1 * psi z.2))
    Integrable grouped
        (timeVelocityVolumeOn (Set.Ioo τ₁ τ₂ ×ˢ O)) ∧
      Integrable hessianPair
        (timeVelocityVolumeOn (Set.Ioo τ₁ τ₂ ×ˢ O)) ∧
      (∫ z in Set.Ioo τ₁ τ₂ ×ˢ O, grouped z
          ∂(volume : Measure (TimeVelocity d))) =
        -∫ z in Set.Ioo τ₁ τ₂ ×ˢ O, hessianPair z
          ∂(volume : Measure (TimeVelocity d)) := by
  let S : Set (TimeVelocity d) := Set.Ioo τ₁ τ₂ ×ˢ O
  let K : Set (TimeVelocity d) := Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω
  let c : TimeVelocity d → ℝ := fun z =>
    reverseTimeCoefficient r₁ a z.1 z.2 i j
  let base : TimeVelocity d → ℝ := fun z => eta z.1 * psi z.2
  let weighted  := fun z => c z * base z
  have hSK : S ⊆ K := by
    rintro z ⟨hztime, hzO⟩
    have ht := htime hztime
    exact ⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, subset_closure (hOΩ hzO)⟩
  obtain ⟨hbaseSmooth, hbaseCompact, hbaseSupport⟩ :=
    separatedBase_admissible hO τ₁ τ₂ eta psi
  have hcSmooth : IsSmoothOnNeighborhood c K :=
    reverseTime_coefficient_smoothOn_closedCylinder r₀ r₁ a haSmooth i j
  obtain ⟨hweightedSmooth, hweightedCompact, hweightedSupport⟩ :=
    weighted_admissible hcSmooth hbaseSmooth hbaseCompact hbaseSupport hSK
  have hgradContinuous : Continuous (fun z => velocityGradient weighted z i) := by
    unfold velocityGradient
    simpa using
      (hweightedSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgradCompact : HasCompactSupport (fun z => velocityGradient weighted z i) := by
    unfold velocityGradient
    simpa using hweightedCompact.fderiv_apply (𝕜 := ℝ)
      _
  have hgradSupport : tsupport _ ⊆ S :=
    (velocityGradient_tsupport_subset weighted i).trans hweightedSupport
  have hGgrad : Integrable _
      (timeVelocityVolumeOn S) :=
    integrable_mul_compact_of_locallyIntegrableOn hGloc hgradContinuous
      hgradCompact hgradSupport
  have hHweighted : Integrable (fun z => Hij z * weighted z)
      (timeVelocityVolumeOn S) :=
    integrable_mul_compact_of_locallyIntegrableOn hHloc
      hweightedSmooth.continuous hweightedCompact hweightedSupport
  have hweakWeighted := hweak weighted hweightedSmooth hweightedCompact hweightedSupport
  have hformula : ∀ z ∈ S, velocityGradient weighted z i =
      reverseTimeCoefficient r₁ a z.1 z.2 i j *
          (eta z.1 * psi.partialDeriv i z.2) +
        (eta z.1 * psi z.2) *
          (fderiv ℝ
            (fun y : PDE.Vec d => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
            (PDE.basisVec i) := by
    intro z hz
    exact velocityGradient_reverseTimeCoefficient_mul_separatedBase
      r₀ r₁ τ₁ τ₂ htime hOΩ a haSmooth i j eta psi z hz
  have hgrouped : Integrable (fun z => Gij z *
      (reverseTimeCoefficient r₁ a z.1 z.2 i j *
          (eta z.1 * psi.partialDeriv i z.2) +
        (eta z.1 * psi z.2) *
          (fderiv ℝ
            (fun y : PDE.Vec d => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
            (PDE.basisVec i))) (timeVelocityVolumeOn S) := by
    apply hGgrad.congr
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hO.measurableSet)] with z hz
    rw [hformula z hz]
  refine ⟨hgrouped, ?_, ?_⟩
  · simpa [weighted, c, base] using hHweighted
  · rw [← hweakWeighted]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hO.measurableSet)] with z hz
    rw [hformula z hz]

end HypoellipticAleksandrov.Parabolic.Dirichlet
