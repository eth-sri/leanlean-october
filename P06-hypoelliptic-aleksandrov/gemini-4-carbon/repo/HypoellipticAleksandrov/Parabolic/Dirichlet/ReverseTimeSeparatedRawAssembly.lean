module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGradientProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorContinuity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialForm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGelfandPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourcePairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductMeasure
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

private theorem reverseTimeCompactCylinder_mapsTo
    {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) :
    reverseTimeMap r₁ '' (Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω) ⊆
      scalarParabolicClosedCylinder r₀ r₁ Ω := by
  rintro _ ⟨z, hz, rfl⟩
  rcases z with ⟨τ, y⟩
  rcases hz with ⟨hτ, hy⟩
  simp only [reverseTimeMap_apply]
  exact ⟨⟨by linarith [hτ.2], by linarith [hτ.1]⟩, hy⟩


private theorem integrable_mul_of_memLp_two_of_continuousOn_reverseTime
    {d : ℕ} {S K : Set (TimeVelocity d)} (hSmeas : MeasurableSet S)
    (hSK : S ⊆ K) (hKcompact : IsCompact K) (hSfinite : volume S < ⊤)
    (W q : TimeVelocity d → ℝ)
    (hW : MemLp W 2 (timeVelocityVolumeOn S)) (hq : ContinuousOn q K) :
    Integrable (fun z => W z * q z) (timeVelocityVolumeOn S) := by
  letI : Fact (volume S < ⊤) := ⟨hSfinite⟩
  letI : IsFiniteMeasure (timeVelocityVolumeOn S) := by
    change IsFiniteMeasure (volume.restrict S)
    infer_instance
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hq
  refine (hW.integrable (by norm_num)).mul_bdd
    ((hq.mono hSK).aestronglyMeasurable hSmeas) (c := C) ?_
  filter_upwards [ae_restrict_mem hSmeas] with z hz
  exact hC z (hSK hz)

private theorem integrable_of_continuousOn_reverseTime
    {d : ℕ} {S K : Set (TimeVelocity d)} (hSmeas : MeasurableSet S)
    (hSK : S ⊆ K) (hKcompact : IsCompact K) (hSfinite : volume S < ⊤)
    (q : TimeVelocity d → ℝ) (hq : ContinuousOn q K) :
    Integrable q (timeVelocityVolumeOn S) := by
  letI : Fact (volume S < ⊤) := ⟨hSfinite⟩
  letI : IsFiniteMeasure (timeVelocityVolumeOn S) := by
    change IsFiniteMeasure (volume.restrict S)
    infer_instance
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hq
  have hqLp : MemLp q 2 (timeVelocityVolumeOn S) :=
    MemLp.of_bound ((hq.mono hSK).aestronglyMeasurable hSmeas) C (by
      filter_upwards [ae_restrict_mem hSmeas] with z hz
      exact hC z (hSK hz))
  exact hqLp.integrable (by norm_num)


/-- The five families in the reverse-time separated raw expression are integrable. -/
theorem raw_reverseTime_separated_product_families_integrable
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
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
    (U : TimeVelocity d → ℝ)
    (hU : MemLp U (2 : ℝ≥0∞)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (G : Fin d → TimeVelocity d → ℝ)
    (hG : ∀ j, MemLp (G j) (2 : ℝ≥0∞)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (psi : PDE.WeakTestFunction Ω) :
    Integrable (fun z : TimeVelocity d =>
      U z * eta.deriv z.1 * psi z.2)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) ∧
    (∀ i j : Fin d, Integrable (fun z : TimeVelocity d =>
      reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
        psi.partialDeriv i z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) ∧
    (∀ j : Fin d, Integrable (fun z : TimeVelocity d =>
      reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
        G j z * psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) ∧
    Integrable (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z *
        psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) ∧
    Integrable (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ F z.1 z.2 *
        psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))   := by
  have continuousOn_of_smoothOnNeighborhood {K : Set (TimeVelocity d)} {f : TimeVelocity d → ℝ} (hf : IsSmoothOnNeighborhood f K) :
      ContinuousOn f K := by
    rcases hf with ⟨V, hVopen, hKV, hV⟩
    exact hV.continuousOn.mono hKV
  have reverseTime_openCylinder_volume_lt_top {Ω : Set (PDE.Vec d)} {T : ℝ} (hΩbounded : Bornology.IsBounded Ω) :
      volume (reverseTimeOpenInterval T ×ˢ Ω : Set (TimeVelocity d)) < ⊤ := by
    exact ((Metric.isBounded_Ioo 0 T).prod hΩbounded).measure_lt_top
  let S := reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω
  let K := Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω
  have hSmeas : MeasurableSet S := by
    have htime : IsOpen (reverseTimeOpenInterval (r₁ - r₀)) := by
      simpa only [reverseTimeOpenInterval] using isOpen_Ioo
    exact (htime.prod hΩ).measurableSet
  have hSK : S ⊆ K := by
    rintro ⟨τ, y⟩ ⟨hτ, hy⟩
    exact ⟨⟨le_of_lt hτ.1, le_of_lt hτ.2⟩, subset_closure hy⟩
  have hKcompact : IsCompact K := isCompact_Icc.prod hΩbounded.isCompact_closure
  have hSfinite : volume S < ⊤ :=
    reverseTime_openCylinder_volume_lt_top hΩbounded
  have hmap := reverseTimeCompactCylinder_mapsTo (d := d) (Ω := Ω) r₀ r₁
  have hpsi :=
    (psi.contDiff.continuous.comp continuous_snd).mul
      (eta.contDiff.continuous.comp continuous_fst)
  have hmassMultiplier : Continuous (fun z : TimeVelocity d => eta.deriv z.1 * psi z.2) :=
    (eta.contDiff.continuous_deriv (by simp)).comp continuous_fst |>.mul
      (psi.contDiff.continuous.comp continuous_snd)
  have hprincipal : ∀ i j : Fin d, Integrable (fun z =>
      reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
        psi.partialDeriv i z.2 * eta z.1) (timeVelocityVolumeOn S) := by
    intro i j
    have hsmooth := IsSmoothOnNeighborhood.reverseTime r₁ hmap
      (IsSmoothOnNeighborhood.coefficientEntry a haSmooth i j)
    have hcoeff : ContinuousOn (fun z =>
        reverseTimeCoefficient r₁ a z.1 z.2 i j) K := by
      simpa only [Function.comp_def, reverseTimeMap_apply,
        reverseTimeCoefficient_apply] using continuousOn_of_smoothOnNeighborhood hsmooth
    have hpartial : Continuous (fun z : TimeVelocity d =>
        psi.partialDeriv i z.2 * eta z.1) :=
      ((psi.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const |>.comp
        continuous_snd).mul (eta.contDiff.continuous.comp continuous_fst)
    have h := integrable_mul_of_memLp_two_of_continuousOn_reverseTime hSmeas hSK
      hKcompact hSfinite (G j) (fun z =>
        reverseTimeCoefficient r₁ a z.1 z.2 i j *
          (psi.partialDeriv i z.2 * eta z.1)) (hG j)
        (hcoeff.mul hpartial.continuousOn)
    refine h.congr (ae_of_all _ fun z => ?_)
    ring
  have hdrift : ∀ j : Fin d, Integrable (fun z =>
      reverseTimeDivergenceDrift r₁ a b z.1 z.2 j * G j z *
        psi z.2 * eta z.1) (timeVelocityVolumeOn S) := by
    intro j
    have hcoeff : ContinuousOn (fun z =>
        reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) K := by
      simpa [Function.comp_def, reverseTimeMap_apply, reverseTimeDivergenceDrift, scalarSpatialCoefficientDivergence_reverseTimeCoefficient, reverseTimeVectorCoefficient_apply] using
          continuousOn_of_smoothOnNeighborhood (IsSmoothOnNeighborhood.reverseTime r₁ hmap (IsSmoothOnNeighborhood.divergenceDriftEntry a b haSmooth hbSmooth j))
    refine (integrable_mul_of_memLp_two_of_continuousOn_reverseTime hSmeas hSK hKcompact hSfinite (G j) (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j * (psi z.2 * eta z.1)) (hG j) (hcoeff.mul hpsi.continuousOn)).congr (ae_of_all _ fun z => ?_)
    ring
  have hscalarCoeff : ContinuousOn (fun z =>
      reverseTimeScalarCoefficient r₁ c z.1 z.2) K := by
    simpa only [Function.comp_def, reverseTimeMap_apply,
      reverseTimeScalarCoefficient_apply] using
        continuousOn_of_smoothOnNeighborhood (IsSmoothOnNeighborhood.reverseTime r₁ hmap hcSmooth)
  have hsourceCoeff : ContinuousOn (fun z =>
      reverseTimeScalarCoefficient r₁ F z.1 z.2) K := by
    simpa only [Function.comp_def, reverseTimeMap_apply,
      reverseTimeScalarCoefficient_apply] using
        continuousOn_of_smoothOnNeighborhood (IsSmoothOnNeighborhood.reverseTime r₁ hmap hFSmooth)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [S, mul_assoc] using (integrable_mul_of_memLp_two_of_continuousOn_reverseTime hSmeas hSK hKcompact hSfinite U _ hU hmassMultiplier.continuousOn)
  · intro i j; simpa only [S] using hprincipal i j
  · intro j; simpa only [S] using hdrift j
  · refine (integrable_mul_of_memLp_two_of_continuousOn_reverseTime hSmeas hSK hKcompact hSfinite U (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2 * (psi z.2 * eta z.1)) hU (hscalarCoeff.mul hpsi.continuousOn)).congr (ae_of_all _ fun z => ?_)
    ring
  · simpa only [S] using (integrable_of_continuousOn_reverseTime hSmeas hSK hKcompact hSfinite (fun z => reverseTimeScalarCoefficient r₁ F z.1 z.2 * psi z.2 * eta z.1) ((hsourceCoeff.mul (psi.contDiff.continuous.comp continuous_snd).continuousOn).mul (eta.contDiff.continuous.comp continuous_fst).continuousOn))

/-- Integrability of the five families implies integrability of the literal raw sum. -/
theorem integrable_full_reverseTime_separated_product_of_raw_families
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (U : TimeVelocity d → ℝ) (G : Fin d → TimeVelocity d → ℝ)
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (psi : PDE.WeakTestFunction Ω)
    (hmass : Integrable (fun z : TimeVelocity d =>
      U z * eta.deriv z.1 * psi z.2)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hprincipal : ∀ i j : Fin d, Integrable (fun z : TimeVelocity d =>
      reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
        psi.partialDeriv i z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hdrift : ∀ j : Fin d, Integrable (fun z : TimeVelocity d =>
      reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
        G j z * psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hscalar : Integrable (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z *
        psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hsource : Integrable (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ F z.1 z.2 *
        psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) :
    Integrable (fun z : TimeVelocity d =>
      U z * eta.deriv z.1 * psi z.2 -
        (∑ i : Fin d, ∑ j : Fin d,
          reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
            psi.partialDeriv i z.2) * eta z.1 -
        (∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
            G j z * psi z.2) * eta z.1 +
        reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z *
          psi z.2 * eta z.1 -
        reverseTimeScalarCoefficient r₁ F z.1 z.2 *
          psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
  have hprincipalSum : Integrable (fun z =>
      ∑ i : Fin d, ∑ j : Fin d,
        reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
          psi.partialDeriv i z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
    apply integrable_finset_sum Finset.univ
    intro i _
    apply integrable_finset_sum Finset.univ
    intro j _
    exact hprincipal i j
  have hdriftSum : Integrable (fun z =>
      ∑ j : Fin d,
        reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
          G j z * psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
    apply integrable_finset_sum Finset.univ
    intro j _
    exact hdrift j
  have hprincipal' : Integrable (fun z =>
      (∑ i : Fin d, ∑ j : Fin d,
        reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
          psi.partialDeriv i z.2) * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
    refine hprincipalSum.congr (ae_of_all _ fun z => ?_)
    simp only [Finset.sum_mul]
  have hdrift' : Integrable (fun z : TimeVelocity d =>
      (∑ j : Fin d,
        reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
          G j z * psi z.2) * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
    refine hdriftSum.congr (ae_of_all _ fun z => ?_)
    simp only [Finset.sum_mul]
  exact (((hmass.sub hprincipal').sub hdrift').add hscalar).sub hsource


private theorem integral_double_sum
    {d : ℕ} {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (p : Fin d → Fin d → X → ℝ)
    (hp : ∀ i j : Fin d, Integrable (p i j) μ) :
    (∫ x, ∑ i : Fin d, ∑ j : Fin d, p i j x ∂μ) =
      ∑ i : Fin d, ∑ j : Fin d, ∫ x, p i j x ∂μ := by
  have hpi (i : Fin d) : Integrable (fun x => ∑ j : Fin d, p i j x) μ :=
    integrable_finset_sum Finset.univ fun j _ => hp i j
  rw [integral_finset_sum Finset.univ (fun i _ => hpi i)]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hp _ j)]

private theorem integral_single_sum
    {d : ℕ} {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (q : Fin d → X → ℝ) (hq : ∀ j : Fin d, Integrable (q j) μ) :
    (∫ x, ∑ j : Fin d, q j x ∂μ) = ∑ j : Fin d, ∫ x, q j x ∂μ := by
  exact integral_finset_sum Finset.univ fun j _ => hq j

/-- Fixed-time integration of the literal reverse-time raw slice agrees with the three
expanded residual scalars. -/
theorem reverseTime_raw_slice_integral_eq_residual
    {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ}
    (r₁ τ : ℝ)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (U : TimeVelocity d → ℝ) (G : Fin d → TimeVelocity d → ℝ)
    (eta : ReverseTimeScalarTest T) (psi : PDE.WeakTestFunction Ω)
    (M A S : ℝ)
    (hmass : Integrable (fun y => U (τ, y) * eta.deriv τ * psi y)
      (PDE.volumeOn Ω))
    (hprincipal : ∀ i j : Fin d, Integrable (fun y =>
      reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
        psi.partialDeriv i y * eta τ) (PDE.volumeOn Ω))
    (hdrift : ∀ j : Fin d, Integrable (fun y =>
      reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) *
        psi y * eta τ) (PDE.volumeOn Ω))
    (hscalar : Integrable (fun y =>
      reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) *
        psi y * eta τ) (PDE.volumeOn Ω))
    (hsource : Integrable (fun y =>
      reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ)
      (PDE.volumeOn Ω))
    (hmassExpand : M = ∫ y, U (τ, y) * psi y ∂PDE.volumeOn Ω)
    (hformExpand : A =
      (∑ i : Fin d, ∑ j : Fin d,
        ∫ y, reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
          psi.partialDeriv i y ∂PDE.volumeOn Ω) +
      (∑ j : Fin d, ∫ y,
        reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * psi y
          ∂PDE.volumeOn Ω) -
      ∫ y, reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y
        ∂PDE.volumeOn Ω)
    (hsourceExpand : S =
      -(∫ y, reverseTimeScalarCoefficient r₁ F τ y * psi y
        ∂PDE.volumeOn Ω)) :
    (∫ y,
      U (τ, y) * eta.deriv τ * psi y -
        (∑ i : Fin d, ∑ j : Fin d,
          reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
            psi.partialDeriv i y) * eta τ -
        (∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * psi y) * eta τ +
        reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ -
        reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ
      ∂PDE.volumeOn Ω) =
      M * eta.deriv τ - A * eta τ + S * eta τ := by
  let p : Fin d → Fin d → PDE.Vec d → ℝ := fun i j y =>
    reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
      psi.partialDeriv i y * eta τ
  let q : Fin d → PDE.Vec d → ℝ := fun j y =>
    reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * psi y * eta τ
  have hpSum : Integrable (fun y => ∑ i : Fin d, ∑ j : Fin d, p i j y)
      (PDE.volumeOn Ω) :=
    integrable_finset_sum Finset.univ fun i _ =>
      integrable_finset_sum Finset.univ fun j _ => hprincipal i j
  have hqSum : Integrable (fun y => ∑ j : Fin d, q j y) (PDE.volumeOn Ω) :=
    integrable_finset_sum Finset.univ fun j _ => hdrift j
  have hraw : Integrable (fun y =>
      U (τ, y) * eta.deriv τ * psi y -
        (∑ i : Fin d, ∑ j : Fin d, p i j y) -
        (∑ j : Fin d, q j y) +
        reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ -
        reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ)
      (PDE.volumeOn Ω) :=
    (((hmass.sub hpSum).sub hqSum).add hscalar).sub hsource
  simp_rw [Finset.sum_mul]
  change (∫ y, ((((fun y => U (τ, y) * eta.deriv τ * psi y) -
      (fun y => ∑ i : Fin d, ∑ j : Fin d, p i j y)) -
      (fun y => ∑ j : Fin d, q j y)) +
      (fun y => reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ)) y -
      reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ
      ∂PDE.volumeOn Ω) = _
  rw [integral_sub (((hmass.sub hpSum).sub hqSum).add hscalar) hsource]
  change ((∫ y, ((((fun y => U (τ, y) * eta.deriv τ * psi y) -
      (fun y => ∑ i : Fin d, ∑ j : Fin d, p i j y)) -
      (fun y => ∑ j : Fin d, q j y)) y +
      reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ)
      ∂PDE.volumeOn Ω) - _) = _
  rw [integral_add ((hmass.sub hpSum).sub hqSum) hscalar]
  change ((((∫ y, (((fun y => U (τ, y) * eta.deriv τ * psi y) -
      (fun y => ∑ i : Fin d, ∑ j : Fin d, p i j y)) y -
      ∑ j : Fin d, q j y) ∂PDE.volumeOn Ω) + _) - _)) = _
  rw [integral_sub (hmass.sub hpSum) hqSum]
  change (((((∫ y, U (τ, y) * eta.deriv τ * psi y -
      ∑ i : Fin d, ∑ j : Fin d, p i j y ∂PDE.volumeOn Ω) - _) + _) - _)) = _
  rw [integral_sub hmass hpSum,
    integral_double_sum (PDE.volumeOn Ω) p (by
      intro i j
      simpa only [p] using hprincipal i j),
    integral_single_sum (PDE.volumeOn Ω) q (by
      intro j
      simpa only [q] using hdrift j)]
  have hmassPull :
      (∫ y, U (τ, y) * eta.deriv τ * psi y ∂PDE.volumeOn Ω) =
        (∫ y, U (τ, y) * psi y ∂PDE.volumeOn Ω) * eta.deriv τ := by
    calc
      _ = ∫ y, (U (τ, y) * psi y) * eta.deriv τ ∂PDE.volumeOn Ω := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = _ := integral_mul_const _ _
  have hprincipalPull (i j : Fin d) :
      (∫ y, p i j y ∂PDE.volumeOn Ω) =
        (∫ y, reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
          psi.partialDeriv i y ∂PDE.volumeOn Ω) * eta τ := by
    dsimp only [p]
    exact integral_mul_const _ _
  have hdriftPull (j : Fin d) :
      (∫ y, q j y ∂PDE.volumeOn Ω) =
        (∫ y, reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * psi y
          ∂PDE.volumeOn Ω) * eta τ := by
    dsimp only [q]
    exact integral_mul_const _ _
  have hscalarPull :
      (∫ y, reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ
        ∂PDE.volumeOn Ω) =
      (∫ y, reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y
        ∂PDE.volumeOn Ω) * eta τ :=
    integral_mul_const _ _
  have hsourcePull :
      (∫ y, reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ
        ∂PDE.volumeOn Ω) =
      (∫ y, reverseTimeScalarCoefficient r₁ F τ y * psi y
        ∂PDE.volumeOn Ω) * eta τ :=
    integral_mul_const _ _
  rw [hmassPull, hscalarPull, hsourcePull]
  simp_rw [hprincipalPull, hdriftPull]
  simp_rw [← Finset.sum_mul]
  rw [← hmassExpand, hformExpand, hsourceExpand]
  ring


/-- A joint reverse-time value representative expands the fixed-time mass pairing. -/
theorem reverseTime_raw_mass_expand_ae
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (T : ℝ) (hΩ : IsOpen Ω)
    (u : ReverseTimeL2V hΩ T)
    (U : TimeVelocity d → ℝ)
    (hUslice : ∀ᵐ τ ∂reverseTimeVolume T,
      (fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u τ) y)
    (ψ : PDE.WeakTestFunction Ω) :
    ∀ᵐ τ ∂reverseTimeVolume T,
      inner ℝ (valueCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ))
        (valueCLM hΩ (u τ)) =
      ∫ y, U (τ, y) * ψ y ∂PDE.volumeOn Ω := by
  filter_upwards [hUslice] with τ hU
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ, hU] with y hψ hy
  rw [hψ, ← hy]
  simp only [RCLike.inner_apply, conj_trivial]

/-- The reverse-time negative source expands to the literal negative source integral. -/
theorem reverseTime_raw_source_expand
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (τ : ℝ) (hτ : τ ∈ Set.Ioo 0 (r₁ - r₀))
    (ψ : PDE.WeakTestFunction Ω) :
    reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) =
      -(∫ y, reverseTimeScalarCoefficient r₁ F τ y * ψ y ∂PDE.volumeOn Ω) := by
  have hτIcc : τ ∈ Set.Icc 0 (r₁ - r₀) :=
    ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  rw [reverseTimeNegativeSourceRaw_eq_sourceFunctional_of_mem_Icc
      r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ hτIcc,
    reverseTimeSourceFunctional_apply, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards
    [coeFn_reverseTimeSourceSlice r₁ τ F
      (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
        r₀ r₁ hΩ hΩbounded F hFSmooth τ hτIcc),
      ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ] with y hF hψ
  rw [hψ, hF]
  simp only [RCLike.inner_apply, conj_trivial, reverseTimeScalarCoefficient_apply]

/-- Joint reverse-time value and gradient representatives expand the spatial form. -/
theorem reverseTime_raw_spatialForm_expand_ae
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (T r₁ : ℝ) (hΩ : IsOpen Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (u : ReverseTimeL2V hΩ T)
    (U : TimeVelocity d → ℝ)
    (hUslice : ∀ᵐ τ ∂reverseTimeVolume T,
      (fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u τ) y)
    (G : Fin d → TimeVelocity d → ℝ)
    (hGslice : ∀ᵐ τ ∂reverseTimeVolume T, ∀ j,
      (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => gradientCLM hΩ (u τ) y j)
    (ψ : PDE.WeakTestFunction Ω) :
    ∀ᵐ τ ∂reverseTimeVolume T,
      reverseTimeSpatialForm hΩ r₁ τ a b c (u τ)
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) =
        (∑ i : Fin d, ∑ j : Fin d,
          ∫ y, reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
            ψ.partialDeriv i y ∂PDE.volumeOn Ω) +
          (∑ j : Fin d, ∫ y,
            reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * ψ y
              ∂PDE.volumeOn Ω) -
          ∫ y, reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * ψ y
            ∂PDE.volumeOn Ω := by
  filter_upwards [hUslice, hGslice] with τ hU hG
  rw [reverseTimeSpatialForm_apply]
  have hprincipal (i j : Fin d) :
      (∫ y in Ω, a (r₁ - τ) y i j *
          (PDE.hilbertVectorLpCoord Ω 2 j
            (gradientCLM hΩ (u τ))) y *
          (PDE.hilbertVectorLpCoord Ω 2 i
            (gradientCLM hΩ
              (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ))) y) =
        ∫ y, reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
          ψ.partialDeriv i y ∂PDE.volumeOn Ω := by
    apply integral_congr_ae
    filter_upwards
      [PDE.coeFn_hilbertVectorLpCoord Ω 2 j
        (gradientCLM hΩ (u τ)), hG j,
       PDE.coeFn_hilbertVectorLpCoord Ω 2 i
        (gradientCLM hΩ
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)),
       ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ i] with
        y hGj hGyi hψi hψ
    rw [hGj, ← hGyi, hψi, hψ]
    simp only [reverseTimeCoefficient_apply]
  have hdrift (j : Fin d) :
      (∫ y in Ω, reverseTimeDivergenceDrift r₁ a b τ y j *
          (PDE.hilbertVectorLpCoord Ω 2 j
            (gradientCLM hΩ (u τ))) y *
          (valueCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)) y) =
        ∫ y, reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * ψ y
          ∂PDE.volumeOn Ω := by
    apply integral_congr_ae
    filter_upwards
      [PDE.coeFn_hilbertVectorLpCoord Ω 2 j
        (gradientCLM hΩ (u τ)), hG j,
       ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ] with y hGj hGyi hψ
    rw [hGj, ← hGyi, hψ]
  have hscalar :
      (∫ y in Ω, reverseTimeScalarCoefficient r₁ c τ y *
          (valueCLM hΩ (u τ)) y *
          (valueCLM hΩ
            (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)) y) =
        ∫ y, reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * ψ y
          ∂PDE.volumeOn Ω := by
    apply integral_congr_ae
    filter_upwards
      [hU, ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ] with y hUyi hψ
    rw [← hUyi, hψ]
  simp_rw [hprincipal, hdrift, hscalar]



private theorem integral_sub_add_eq_zero_of_pairing
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (mass form source dual : α → ℝ)
    (hmass : Integrable mass μ) (hform : Integrable form μ)
    (hsource : Integrable source μ)
    (hmassEq : (∫ x, mass x ∂μ) = -(∫ x, dual x ∂μ))
    (hformEq : (∫ x, form x ∂μ) = (∫ x, source x ∂μ) - ∫ x, dual x ∂μ) :
    (∫ x, mass x - form x + source x ∂μ) = 0 := by
  change (∫ x, (mass - form) x + source x ∂μ) = 0
  rw [integral_add (hmass.sub hform) hsource]
  change (∫ x, mass x - form x ∂μ) + ∫ x, source x ∂μ = 0
  rw [integral_sub hmass hform, hmassEq, hformEq]
  ring

/-- A reverse-time variational energy solution satisfies the separated-test residual identity. -/
theorem reverseTime_separated_residual_of_variationalEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu)
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (v : H10HilbertGraph hΩ) :
    Integrable (fun tau =>
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau -
        reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau +
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau)
      (reverseTimeVolume (r₁ - r₀)) ∧
    (∫ tau,
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau -
        reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau +
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau
      ∂reverseTimeVolume (r₁ - r₀)) = 0  := by
  have integrable_reverseTimeNegativeSourceRaw_mul_test {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (F : ℝ → PDE.Vec d → ℝ) (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (eta : ReverseTimeScalarTest (r₁ - r₀)) (v : H10HilbertGraph hΩ) :
      Integrable
      (fun tau => reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau)
      (reverseTimeVolume (r₁ - r₀)) := by
    let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
    let z := reverseTimeSeparatedVTest hΩ eta v
    have hPair : Integrable (fun tau => S tau (z tau)) (reverseTimeVolume (r₁ - r₀)) :=
      integrable_reverseTimeDualPairing hΩ (r₁ - r₀) z S
    refine hPair.congr ?_
    filter_upwards
      [(memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).coeFn_toLp,
        ae_reverseTimeSeparatedVTest hΩ eta v] with tau hS hz
    dsimp only [S, z]
    calc
      reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
          (reverseTimeSeparatedVTest hΩ eta v tau) =
          reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau (eta tau • v) :=
        congrArg (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau) hz
      _ = eta tau * reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v := by
        rw [ContinuousLinearMap.map_smul]
        rfl
      _ = eta tau * reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v :=
        congrArg (fun q => eta tau * q v) hS
      _ = reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau :=
        mul_comm _ _
  obtain ⟨hmassLift, hg, hmassLiftEq⟩ := hdu v eta
  have hmass : Integrable (fun tau =>
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau)
      (reverseTimeVolume (r₁ - r₀)) := by
    refine hmassLift.congr ?_
    filter_upwards [coeFn_reverseTimeValueCLM hΩ (r₁ - r₀) u] with tau huValue
    rw [huValue]
  have hmassEq : (∫ tau,
      inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * eta.deriv tau
      ∂reverseTimeVolume (r₁ - r₀)) =
      -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume (r₁ - r₀)) := by
    calc
      _ = ∫ tau,
          inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ (r₁ - r₀) u tau) * eta.deriv tau
          ∂reverseTimeVolume (r₁ - r₀) := by
        apply integral_congr_ae
        filter_upwards [coeFn_reverseTimeValueCLM hΩ (r₁ - r₀) u] with tau huValue
        rw [huValue]
      _ = _ := hmassLiftEq
  have hsource := integrable_reverseTimeNegativeSourceRaw_mul_test r₀ r₁ h₀₁ hΩ hΩbounded F
    hFSmooth eta v
  have hformEq : ∀ᵐ tau ∂reverseTimeVolume (r₁ - r₀),
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau =
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau -
          (g tau) v * eta tau := by
    filter_upwards [hu.2, ae_restrict_mem measurableSet_Ioo] with tau hEquation htau
    have hRaw : reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau =
        reverseTimeSourceFunctional hΩ
          (reverseTimeSourceSlice r₁ tau F
            (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F hFSmooth
              tau ⟨le_of_lt htau.1, le_of_lt htau.2⟩)) :=
      reverseTimeNegativeSourceRaw_eq_sourceFunctional_of_mem_Icc r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
        tau ⟨le_of_lt htau.1, le_of_lt htau.2⟩
    have hPoint := hEquation htau v
    rw [← hRaw] at hPoint
    calc
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau =
          ((g tau) v + reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v - (g tau) v) * eta tau := by
            ring
      _ = (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v -
          (g tau) v) * eta tau := by
            rw [hPoint]
      _ = _ := sub_mul _ _ _
  have hform : Integrable (fun tau =>
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau)
      (reverseTimeVolume (r₁ - r₀)) :=
    (hsource.sub hg).congr (by
      filter_upwards [hformEq] with tau htau
      exact htau.symm)
  have hformEqIntegral : (∫ tau,
      reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * eta tau
      ∂reverseTimeVolume (r₁ - r₀)) =
      (∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau
        ∂reverseTimeVolume (r₁ - r₀)) -
        ∫ tau, (g tau) v * eta tau ∂reverseTimeVolume (r₁ - r₀) := by
    calc
      _ = ∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * eta tau -
          (g tau) v * eta tau ∂reverseTimeVolume (r₁ - r₀) := integral_congr_ae hformEq
      _ = _ := integral_sub hsource hg
  constructor
  · exact (hmass.sub hform).add hsource
  · exact integral_sub_add_eq_zero_of_pairing (reverseTimeVolume (r₁ - r₀)) _ _ _ _
      hmass hform hsource hmassEq hformEqIntegral


/-- A reverse-time variational energy solution and joint value and gradient representatives
satisfy the global separated-product raw distribution identity. -/
theorem reverseTime_global_separated_product_distribution_of_reverseTimeVariationalEnergy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
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
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution
      r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu)
    (U : TimeVelocity d → ℝ)
    (hU : MemLp U (2 : ℝ≥0∞)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hUslice : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      (fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u τ) y)
    (G : Fin d → TimeVelocity d → ℝ)
    (hG : ∀ j, MemLp (G j) (2 : ℝ≥0∞)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hGslice : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ j,
      (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => gradientCLM hΩ (u τ) y j)
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (psi : PDE.WeakTestFunction Ω) :
    let raw : TimeVelocity d → ℝ := fun z =>
      U z * eta.deriv z.1 * psi z.2 -
        (∑ i : Fin d, ∑ j : Fin d,
          reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
            psi.partialDeriv i z.2) * eta z.1 -
        (∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
            G j z * psi z.2) * eta z.1 +
        reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z *
          psi z.2 * eta z.1 -
        reverseTimeScalarCoefficient r₁ F z.1 z.2 * psi z.2 * eta z.1
    Integrable raw
        (timeVelocityVolumeOn
          (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) ∧
      (∫ z, raw z
        ∂timeVelocityVolumeOn
          (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) = 0 := by
  dsimp only
  letI : SFinite (reverseTimeVolume (r₁ - r₀)) := by
    dsimp only [reverseTimeVolume]
    infer_instance
  obtain ⟨hmass, hprincipal, hdrift, hscalar, hsource⟩ :=
    raw_reverseTime_separated_product_families_integrable r₀ r₁ hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth U hU G hG eta psi
  have hraw := integrable_full_reverseTime_separated_product_of_raw_families
    a b c F U G eta psi hmass hprincipal hdrift hscalar hsource
  refine ⟨hraw, ?_⟩
  have hprod := reverseTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn (r₁ - r₀) Ω
  rw [← hprod] at hmass hprincipal hdrift hscalar hsource hraw
  have hprincipalAE : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ i j : Fin d,
      Integrable (fun y => reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
        psi.partialDeriv i y * eta τ) (PDE.volumeOn Ω) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact (hprincipal i j).prod_right_ae
  have hdriftAE : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀), ∀ j : Fin d,
      Integrable (fun y => reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) *
        psi y * eta τ) (PDE.volumeOn Ω) := by
    rw [ae_all_iff]
    intro j
    exact (hdrift j).prod_right_ae
  have hslice : ∀ᵐ τ ∂reverseTimeVolume (r₁ - r₀),
      (∫ y,
        U (τ, y) * eta.deriv τ * psi y -
          (∑ i : Fin d, ∑ j : Fin d,
            reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
              psi.partialDeriv i y) * eta τ -
          (∑ j : Fin d,
            reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * psi y) * eta τ +
          reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ -
          reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ
        ∂PDE.volumeOn Ω) =
        inner ℝ (valueCLM hΩ (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ psi))
          (valueCLM hΩ (u τ)) * eta.deriv τ -
        reverseTimeSpatialForm hΩ r₁ τ a b c (u τ)
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ psi) * eta τ +
        reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ
          (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ psi) * eta τ := by
    filter_upwards [hmass.prod_right_ae, hprincipalAE, hdriftAE, hscalar.prod_right_ae,
      hsource.prod_right_ae,
      reverseTime_raw_mass_expand_ae (r₁ - r₀) hΩ u U hUslice psi,
      reverseTime_raw_spatialForm_expand_ae
        (r₁ - r₀) r₁ hΩ a b c u U hUslice G hGslice psi,
      ae_restrict_mem measurableSet_Ioo] with τ hm hp hq hc hs hM hA hτ
    exact reverseTime_raw_slice_integral_eq_residual (T := r₁ - r₀) r₁ τ
      a b c F U G eta psi _ _ _ hm hp hq hc hs hM hA
      (reverseTime_raw_source_expand r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ hτ psi)
  obtain ⟨_, hresidual⟩ := reverseTime_separated_residual_of_variationalEnergy
    r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu hu eta
      (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ psi)
  rw [← hprod]
  calc
    _ = ∫ τ, ∫ y,
        U (τ, y) * eta.deriv τ * psi y -
          (∑ i : Fin d, ∑ j : Fin d,
            reverseTimeCoefficient r₁ a τ y i j * G j (τ, y) *
              psi.partialDeriv i y) * eta τ -
          (∑ j : Fin d,
            reverseTimeDivergenceDrift r₁ a b τ y j * G j (τ, y) * psi y) * eta τ +
          reverseTimeScalarCoefficient r₁ c τ y * U (τ, y) * psi y * eta τ -
          reverseTimeScalarCoefficient r₁ F τ y * psi y * eta τ
        ∂PDE.volumeOn Ω ∂reverseTimeVolume (r₁ - r₀) := by
      exact integral_prod _ hraw
    _ = _ := (integral_congr_ae hslice).trans hresidual

end HypoellipticAleksandrov.Parabolic.Dirichlet

