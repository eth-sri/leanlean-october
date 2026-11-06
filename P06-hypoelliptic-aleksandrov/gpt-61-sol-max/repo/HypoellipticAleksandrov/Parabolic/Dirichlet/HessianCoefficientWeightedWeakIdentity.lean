module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothNeighborhoodProduct
public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeSpacetimeTest
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Calculus.RegularityOrder



open private HypoellipticAleksandrov.Parabolic.integrable_restrict_mul_of_locallyIntegrableOn from HypoellipticAleksandrov.Parabolic.WeakDerivativesAlgebra
open private HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTime_coefficient_smoothOn_closedCylinder from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder
open private HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeMap_image_closedCylinder_subset from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder
section
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
private alias _sharedProof_198_5 := HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset
end


/-! # Coefficient-weighted weak Hessian identities

Proof-local prerequisites for the fixed-index weighted weak identity. -/

 public section

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.Elementwise MatrixOrder

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ}




private theorem velocityGradient_mul_at
     (f q : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d) (i : Fin d)
    (hf : DifferentiableAt ℝ f z) (hq : DifferentiableAt ℝ q z) :
    velocityGradient (f * q) z i =
      f z * velocityGradient q z i + q z * velocityGradient f z i := by
  unfold velocityGradient
  rw [fderiv_mul hf hq]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem velocityGradient_tsupport_subset
     (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (i : Fin d) :
    tsupport (fun z => velocityGradient q z i) ⊆ tsupport q := _sharedProof_198_5





private theorem velocityGradient_eq_spatialSlice_fderiv
     {f : HypoellipticAleksandrov.Parabolic.ScalarField d} (z : TimeVelocity d) (i : Fin d)
    (hf : DifferentiableAt ℝ f z) :
    velocityGradient f z i =
      (fderiv ℝ (fun y  => f (z.1, y)) z.2) (PDE.basisVec i) := by
  have hs : HasFDerivAt (fun y  => f (z.1, y))
      ((fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d))) z.2 := by
    simpa only [Function.comp_def] using! hf.hasFDerivAt.comp z.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  rw [hs.fderiv]
  rfl

private theorem separatedBase_admissible
     {O : PDE.VelocityRegion d} (hO : IsOpen O) (τ₁ τ₂ : ℝ)
    (eta : OriginalTimeScalarTest τ₁ τ₂) (psi : PDE.WeakTestFunction O) :
    let base : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => eta z.1 * psi z.2
    ContDiff ℝ PDE.smoothOrder base ∧ HasCompactSupport base ∧
      tsupport base ⊆ Set.Ioo τ₁ τ₂ ×ˢ O := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Function.comp_def, Pi.mul_def] using!
      (eta.contDiff.comp contDiff_fst).mul (psi.contDiff.comp contDiff_snd)
  · simpa only [originalTimeSeparatedProduct] using!
      (originalTimeSeparatedProductSupportedIn eta psi).hasCompactSupport
  · intro z hz
    have hz' : z ∈ tsupport (eta : ℝ → ℝ) ×ˢ
        tsupport (psi : PDE.ScalarField d) := by
      change z ∈ tsupport (fun w : TimeVelocity d => eta w.1 * psi w.2) at hz
      rw [show tsupport (fun w : TimeVelocity d => eta w.1 * psi w.2) =
          tsupport (eta : ℝ → ℝ) ×ˢ tsupport (psi : PDE.ScalarField d) by
        rw [← tsupport_originalTimeSeparatedProductTestFunction hO eta psi]
        rfl] at hz
      exact hz
    exact ⟨eta.tsupport_subset hz'.1, psi.tsupport_subset hz'.2⟩

private theorem weighted_admissible
     {S K : HypoellipticAleksandrov.Parabolic.Region d} {c q : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hc : IsSmoothOnNeighborhood c K) (hq : ContDiff ℝ PDE.smoothOrder q)
    (hqCompact : HasCompactSupport q) (hqS : tsupport q ⊆ S) (hSK : S ⊆ K) :
    ContDiff ℝ PDE.smoothOrder (fun z => c z * q z) ∧
      HasCompactSupport (fun z => c z * q z) ∧
      tsupport (fun z => c z * q z) ⊆ S := ⟨IsSmoothOnNeighborhood.contDiff_mul_of_tsupport_subset
      hc hq (hqS.trans hSK),
    hqCompact.mul_left, tsupport_mul_subset_right.trans hqS⟩




private theorem velocityGradient_separatedBase
     {O : PDE.VelocityRegion d} {τ₁ τ₂ : ℝ}
    (eta : OriginalTimeScalarTest τ₁ τ₂) (psi : PDE.WeakTestFunction O)
    (z : TimeVelocity d) (i : Fin d) :
    velocityGradient (fun w  => eta w.1 * psi w.2) z i =
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

variable {Ω O : PDE.VelocityRegion d} (r₀ r₁ : ℝ)

private theorem velocityGradient_reverseTimeCoefficient_mul_separatedBase
      (τ₁ τ₂ : ℝ)
    (htime : Set.Ioo τ₁ τ₂ ⊆ reverseTimeOpenInterval (r₁ - r₀))
    (hOΩ : O ⊆ Ω) (a : CoefficientField d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (i j : Fin d)
    (eta : OriginalTimeScalarTest τ₁ τ₂) (psi : PDE.WeakTestFunction O)
    (z : TimeVelocity d) (hz : z ∈ Set.Ioo τ₁ τ₂ ×ˢ O) :
    velocityGradient (fun w  =>
        reverseTimeCoefficient r₁ a w.1 w.2 i j * (eta w.1 * psi w.2)) z i =
      reverseTimeCoefficient r₁ a z.1 z.2 i j *
          (eta z.1 * psi.partialDeriv i z.2) +
        (eta z.1 * psi z.2) *
          (fderiv ℝ
            (fun y  => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
            (PDE.basisVec i) := by
  let c : HypoellipticAleksandrov.Parabolic.ScalarField d := fun w =>
    reverseTimeCoefficient r₁ a w.1 w.2 i j
  let base : HypoellipticAleksandrov.Parabolic.ScalarField d := fun w => eta w.1 * psi w.2
  have ht := htime hz.1


  have hcDiff : DifferentiableAt ℝ c z :=
    IsSmoothOnNeighborhood.differentiableAt (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTime_coefficient_smoothOn_closedCylinder r₀ r₁ a ha i j) (⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, subset_closure (hOΩ hz.2)⟩)
  have hbaseDiff : DifferentiableAt ℝ base z :=
    ((eta.contDiff.comp contDiff_fst).mul
      (psi.contDiff.comp contDiff_snd)).differentiable (by simp) z
  change velocityGradient (c * base) z i = _
  rw [velocityGradient_mul_at c base z i hcDiff hbaseDiff,
    show velocityGradient base z i = eta z.1 * psi.partialDeriv i z.2 from velocityGradient_separatedBase eta psi z i,
    show velocityGradient c z i =
        (fderiv ℝ
          (fun y  => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
          (PDE.basisVec i) from velocityGradient_eq_spatialSlice_fderiv z i hcDiff]

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
    (Gij Hij : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hGloc : LocallyIntegrableOn Gij
      (Set.Ioo τ₁ τ₂ ×ˢ O) )
    (hHloc : LocallyIntegrableOn Hij
      (Set.Ioo τ₁ τ₂ ×ˢ O) )
    (i j : Fin d)
    (hweak : HasWeakVelocityPartialDerivOn
      (Set.Ioo τ₁ τ₂ ×ˢ O) i Gij Hij)
    (eta : OriginalTimeScalarTest τ₁ τ₂)
    (psi : PDE.WeakTestFunction O) :
    let grouped : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z =>
      Gij z *
        (reverseTimeCoefficient r₁ a z.1 z.2 i j *
            (eta z.1 * psi.partialDeriv i z.2) +
          (eta z.1 * psi z.2) *
            (fderiv ℝ
              (fun y : PDE.Vec d =>
                reverseTimeCoefficient r₁ a z.1 y i j) z.2)
              (PDE.basisVec i))
    let hessianPair : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z =>
      Hij z *
        (reverseTimeCoefficient r₁ a z.1 z.2 i j *
          (eta z.1 * psi z.2))
    Integrable grouped
        (timeVelocityVolumeOn (Set.Ioo τ₁ τ₂ ×ˢ O)) ∧
      Integrable hessianPair
        (timeVelocityVolumeOn (Set.Ioo τ₁ τ₂ ×ˢ O)) ∧
      (∫ z in Set.Ioo τ₁ τ₂ ×ˢ O, grouped z
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)) =
        -∫ z in Set.Ioo τ₁ τ₂ ×ˢ O, hessianPair z
          ∂(HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) := by
  let S : HypoellipticAleksandrov.Parabolic.Region d := Set.Ioo τ₁ τ₂ ×ˢ O
  let K : HypoellipticAleksandrov.Parabolic.Region d := Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω
  let c : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z =>
    reverseTimeCoefficient r₁ a z.1 z.2 i j
  let base : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => eta z.1 * psi z.2
  let weighted  := fun z => c z * base z

  obtain ⟨hbaseSmooth, hbaseCompact, hbaseSupport⟩ :=
    separatedBase_admissible hO τ₁ τ₂ eta psi
  have hcSmooth : IsSmoothOnNeighborhood c K :=
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTime_coefficient_smoothOn_closedCylinder r₀ r₁ a haSmooth i j
  obtain ⟨hweightedSmooth, hweightedCompact, hweightedSupport⟩ :=
    weighted_admissible hcSmooth hbaseSmooth hbaseCompact hbaseSupport (show _ by
        rintro z ⟨hztime, hzO⟩
        have ht := htime hztime
        exact ⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, subset_closure (hOΩ hzO)⟩)


  have hgradSupport : tsupport (fun z => velocityGradient weighted z i) ⊆ S :=
    (velocityGradient_tsupport_subset weighted i).trans hweightedSupport
  have hGgrad : Integrable (fun z => Gij z * velocityGradient weighted z i)
      (timeVelocityVolumeOn S) :=
    _root_.HypoellipticAleksandrov.Parabolic.integrable_restrict_mul_of_locallyIntegrableOn hGloc (show _ by
        unfold velocityGradient
        simpa using
          (hweightedSmooth.continuous_fderiv (by simp)).clm_apply continuous_const)
      (show _ by
          unfold velocityGradient
          simpa using hweightedCompact.fderiv_apply (𝕜 := ℝ)
            ((0, Pi.single i 1) )) hgradSupport
  have hHweighted : Integrable (fun z => Hij z * weighted z)
      (timeVelocityVolumeOn S) :=
    _root_.HypoellipticAleksandrov.Parabolic.integrable_restrict_mul_of_locallyIntegrableOn hHloc
      hweightedSmooth.continuous hweightedCompact hweightedSupport
  have hweakWeighted := hweak weighted hweightedSmooth hweightedCompact hweightedSupport
  have hformula : ∀ z ∈ S, velocityGradient weighted z i =
      reverseTimeCoefficient r₁ a z.1 z.2 i j *
          (eta z.1 * psi.partialDeriv i z.2) +
        (eta z.1 * psi z.2) *
          (fderiv ℝ
            (fun y  => reverseTimeCoefficient r₁ a z.1 y i j) z.2)
            (PDE.basisVec i) := by
    intro z hz
    exact velocityGradient_reverseTimeCoefficient_mul_separatedBase
      r₀ r₁ τ₁ τ₂ htime hOΩ a haSmooth i j eta psi z hz
  dsimp only

  refine ⟨(show _ by
      apply hGgrad.congr
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hO.measurableSet)] with z hz
      rw [hformula z hz]), ?_, ?_⟩
  · exact hHweighted
  · rw [← hweakWeighted]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hO.measurableSet)] with z hz
    rw [hformula z hz]

end HypoellipticAleksandrov.Parabolic.Dirichlet
