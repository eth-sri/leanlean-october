module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGradientProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorContinuity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder

open private HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeMap_image_closedCylinder_subset from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10NonprincipalRemainder


/-!
# Integrability of reverse-time separated raw terms

This module isolates the analytic integrability of the five raw families used
in the reverse-time separated product distribution identity.
-/

 public section

open MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise MatrixOrder



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ}

variable {Ω : PDE.VelocityRegion d}




private theorem reverseTime_openCylinder_volume_lt_top
      {T : ℝ}
    (hΩbounded : Bornology.IsBounded Ω) :
    volume (reverseTimeOpenInterval T ×ˢ Ω ) < ⊤ := ((Metric.isBounded_Ioo 0 T).prod hΩbounded).measure_lt_top

section
variable {S K : HypoellipticAleksandrov.Parabolic.Region d} (hSmeas : MeasurableSet S) (hSK : S ⊆ K) (hKcompact : IsCompact K) (hSfinite : volume S < ⊤)

include hSmeas hSK hKcompact hSfinite
private theorem integrable_mul_of_memLp_two_of_continuousOn_reverseTime

    (W q : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hW : MemLp W 2 (timeVelocityVolumeOn S)) (hq : ContinuousOn q K) :
    Integrable (fun z => W z * q z) (timeVelocityVolumeOn S) := by
  letI : Fact (volume S < ⊤) := ⟨hSfinite⟩
  letI : IsFiniteMeasure (timeVelocityVolumeOn S) := (id inferInstance)
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hq
  refine (hW.integrable (by norm_num)).mul_bdd
    ((hq.mono hSK).aestronglyMeasurable hSmeas) (c := C) ?_
  filter_upwards [ae_restrict_mem hSmeas] with z hz
  exact hC z (hSK hz)

private theorem integrable_of_continuousOn_reverseTime

    (q : HypoellipticAleksandrov.Parabolic.ScalarField d) (hq : ContinuousOn q K) :
    Integrable q (timeVelocityVolumeOn S) := by
  letI : Fact (volume S < ⊤) := ⟨hSfinite⟩
  letI : IsFiniteMeasure (timeVelocityVolumeOn S) := (id inferInstance)
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hq
  have hqLp : MemLp q (2 ) (timeVelocityVolumeOn S) :=
    MemLp.of_bound ((hq.mono hSK).aestronglyMeasurable hSmeas) C (by
      filter_upwards [ae_restrict_mem hSmeas] with z hz
      exact hC z (hSK hz))
  exact hqLp.integrable (by norm_num)
end


private theorem continuousOn_of_smoothOnNeighborhood
     {K : HypoellipticAleksandrov.Parabolic.Region d} {f : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hf : IsSmoothOnNeighborhood f K) : ContinuousOn f K := by
  rcases hf with ⟨V, hVopen, hKV, hV⟩
  exact hV.continuousOn.mono hKV

variable {Ω : PDE.VelocityRegion d}

/-- The five families in the reverse-time separated raw expression are integrable. -/
theorem raw_reverseTime_separated_product_families_integrable

    (r₀ r₁ : ℝ)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
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
    (U : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hU : MemLp U (2 )
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (G : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hG : ∀ j, MemLp (G j) (2 )
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (psi : PDE.WeakTestFunction Ω) :
    Integrable (fun z  =>
      U z * eta.deriv z.1 * psi z.2)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) ∧
    (∀ i j : Fin d, Integrable (fun z  =>
      reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
        psi.partialDeriv i z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) ∧
    (∀ j : Fin d, Integrable (fun z  =>
      reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
        G j z * psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) ∧
    Integrable (fun z  =>
      reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z *
        psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) ∧
    Integrable (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ F z.1 z.2 *
        psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)) := by
  let S  := reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω
  let K  := Set.Icc 0 (r₁ - r₀) ×ˢ closure Ω
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
  have hmap := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeMap_image_closedCylinder_subset (d := d) (Ω := Ω) r₀ r₁
  have hpsi : Continuous (fun z : TimeVelocity d => psi z.2 * eta z.1) :=
    (psi.contDiff.continuous.comp continuous_snd).mul
      (eta.contDiff.continuous.comp continuous_fst)
  have hmassMultiplier : Continuous (fun z : TimeVelocity d => eta.deriv z.1 * psi z.2) :=
    (eta.contDiff.continuous_deriv (by simp)).comp continuous_fst |>.mul
      (psi.contDiff.continuous.comp continuous_snd)
  have hmass := integrable_mul_of_memLp_two_of_continuousOn_reverseTime
    hSmeas hSK hKcompact hSfinite U _ hU hmassMultiplier.continuousOn




  have hscalar := integrable_mul_of_memLp_two_of_continuousOn_reverseTime hSmeas hSK
    hKcompact hSfinite U (fun z =>
      reverseTimeScalarCoefficient r₁ c z.1 z.2 * (psi z.2 * eta z.1)) hU
      ((show ContinuousOn (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ c z.1 z.2) K by
          exact continuousOn_of_smoothOnNeighborhood (IsSmoothOnNeighborhood.reverseTime r₁ hmap hcSmooth)).mul hpsi.continuousOn)

  have hsourceCoeff : ContinuousOn (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ F z.1 z.2) K := by
    exact continuousOn_of_smoothOnNeighborhood (IsSmoothOnNeighborhood.reverseTime r₁ hmap hFSmooth)
  have hsource := integrable_of_continuousOn_reverseTime hSmeas hSK hKcompact hSfinite
    (fun z => reverseTimeScalarCoefficient r₁ F z.1 z.2 * psi z.2 * eta z.1)
    ((hsourceCoeff.mul (psi.contDiff.continuous.comp continuous_snd).continuousOn).mul
      (eta.contDiff.continuous.comp continuous_fst).continuousOn)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [S, mul_assoc] using hmass
  · intro i j; exact (show ∀ i j : Fin d, Integrable (fun z  =>
      reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
        psi.partialDeriv i z.2 * eta z.1) (timeVelocityVolumeOn S) by
      intro i j
      have hsmooth := IsSmoothOnNeighborhood.reverseTime r₁ hmap
        (IsSmoothOnNeighborhood.coefficientEntry a haSmooth i j)

      have hpartial : Continuous (fun z : TimeVelocity d =>
          psi.partialDeriv i z.2 * eta z.1) :=
        ((psi.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const |>.comp
          continuous_snd).mul (eta.contDiff.continuous.comp continuous_fst)
      have h := integrable_mul_of_memLp_two_of_continuousOn_reverseTime hSmeas hSK
        hKcompact hSfinite (G j) (fun z =>
          reverseTimeCoefficient r₁ a z.1 z.2 i j *
            (psi.partialDeriv i z.2 * eta z.1)) (hG j)
          ((show ContinuousOn (fun z : TimeVelocity d =>
          reverseTimeCoefficient r₁ a z.1 z.2 i j) K by
              exact continuousOn_of_smoothOnNeighborhood hsmooth).mul hpartial.continuousOn)
      refine h.congr (ae_of_all _ fun z => ?_)
      ring) i j
  · intro j; exact (show ∀ j : Fin d, Integrable (fun z  =>
      reverseTimeDivergenceDrift r₁ a b z.1 z.2 j * G j z *
        psi z.2 * eta z.1) (timeVelocityVolumeOn S) by
      intro j
      have hsmooth := IsSmoothOnNeighborhood.reverseTime r₁ hmap
        (IsSmoothOnNeighborhood.divergenceDriftEntry a b haSmooth hbSmooth j)

      have h := integrable_mul_of_memLp_two_of_continuousOn_reverseTime hSmeas hSK
        hKcompact hSfinite (G j) (fun z =>
          reverseTimeDivergenceDrift r₁ a b z.1 z.2 j * (psi z.2 * eta z.1))
          (hG j) ((show ContinuousOn (fun z : TimeVelocity d =>
          reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) K by
              simpa only [Function.comp_def, reverseTimeMap_apply,
                reverseTimeDivergenceDrift, scalarSpatialCoefficientDivergence_reverseTimeCoefficient,
                reverseTimeVectorCoefficient_apply, Pi.sub_apply] using
                  continuousOn_of_smoothOnNeighborhood hsmooth).mul hpsi.continuousOn)
      refine h.congr (ae_of_all _ fun z => ?_)
      ring) j
  · refine hscalar.congr (ae_of_all _ fun z => ?_)
    ring
  · exact hsource

/-- Integrability of the five families implies integrability of the literal raw sum. -/
theorem integrable_full_reverseTime_separated_product_of_raw_families
      {r₀ r₁ : ℝ}
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    (U : HypoellipticAleksandrov.Parabolic.ScalarField d) (G : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (eta : ReverseTimeScalarTest (r₁ - r₀))
    (psi : PDE.WeakTestFunction Ω)
    (hmass : Integrable (fun z  =>
      U z * eta.deriv z.1 * psi z.2)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hprincipal : ∀ i j : Fin d, Integrable (fun z  =>
      reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
        psi.partialDeriv i z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hdrift : ∀ j : Fin d, Integrable (fun z  =>
      reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
        G j z * psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hscalar : Integrable (fun z  =>
      reverseTimeScalarCoefficient r₁ c z.1 z.2 * U z *
        psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))
    (hsource : Integrable (fun z : TimeVelocity d =>
      reverseTimeScalarCoefficient r₁ F z.1 z.2 *
        psi z.2 * eta z.1)
      (timeVelocityVolumeOn
        (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω))) :
    Integrable (fun z  =>
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
  let sharedTerm_398f0ffdf7 := ((timeVelocityVolumeOn (reverseTimeOpenInterval (r₁ - r₀) ×ˢ Ω)))




  exact (((hmass.sub (by
      refine (show Integrable (fun z  =>
      ∑ i : Fin d, ∑ j : Fin d,
        reverseTimeCoefficient r₁ a z.1 z.2 i j * G j z *
          psi.partialDeriv i z.2 * eta z.1)
      sharedTerm_398f0ffdf7 by
          apply integrable_finset_sum Finset.univ
          intro i _
          apply integrable_finset_sum Finset.univ
          intro j _
          exact hprincipal i j).congr (ae_of_all _ fun z => ?_)
      simp only [Finset.sum_mul])).sub (by
      refine (show Integrable (fun z  =>
      ∑ j : Fin d,
        reverseTimeDivergenceDrift r₁ a b z.1 z.2 j *
          G j z * psi z.2 * eta z.1)
      sharedTerm_398f0ffdf7 by
          apply integrable_finset_sum Finset.univ
          intro j _
          exact hdrift j).congr (ae_of_all _ fun z => ?_)
      simp only [Finset.sum_mul])).add hscalar).sub hsource

end HypoellipticAleksandrov.Parabolic.Dirichlet
