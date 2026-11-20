module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspGrowth.KernelTorusPeriodicity
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CuspKernelTorus.ProbabilityMeasure

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory
set_option maxHeartbeats 1200000
namespace DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth
open KPContFlatCuspIncomingEvaluation
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (hι : Function.Injective ι) (f : ℂ → S)
    (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
    (a : Cusps F ζ hζ C R P H U) (s : ℂ) (hs : s ∈ KPContActualChamberNormalSeries.V)
include hι hf hs

theorem actualCuspSheet_kernel_continuous
    (t : ℝ) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    Continuous (fun z : KernelTorus F ζ hζ C R P H U a =>
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b ε) := by
  let u : KPCuspCharts.Horizontal F → ℂ := fun x =>
    KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t x b ε
  have hu : Continuous u := by
    have hh := (KPContActualChamberNormalSeries.smooth F ζ hζ U ι f hι hf s hs).1
    have harch : Continuous (fun x : KPCuspCharts.Horizontal F => KPCuspCharts.toArch F ((x,b),t)) :=
      (KPCuspCharts.toArch_contDiff F).continuous.comp
        ((continuous_id.prodMk continuous_const).prodMk continuous_const)
    have hsec := (KPContSectorArchSphericalFibers.section_continuous F ζ hζ).comp harch
    have hins := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp hsec
    simpa only [u, KPContActualChamberCasimirJets.cuspSheet, KPContActualChamberCasimirJets.jet,
      iteratedDerivWithin_zero, cuspGroup, localGroup, Function.comp_def, Pi.mul_apply] using
      hh.comp (continuous_const.mul (hins.mul continuous_const))
  have hrel : ∀ x y, (QuotientAddGroup.leftRel
      (KPCuspCharts.translationLattice F (KPCuspGenuineMonodromy.kernelLattice
        (stabilizer F ζ hζ C R P H U a) (parabolic F ζ hζ C R P H U a)
        (rho F ζ hζ C R P H U a)))).r x y → u x = u y := fun x y h => actualCuspSheet_kernel_representative F ζ hζ C R P H U ι hι f hf a s hs
      t x y b ε (Quotient.sound h)
  have heq : (fun z : KernelTorus F ζ hζ C R P H U a => u (Quotient.out z)) =
      Quotient.lift u hrel := by
    funext z
    conv_rhs => rw [← Quotient.out_eq z]
    rfl
  rw [show (fun z : KernelTorus F ζ hζ C R P H U a =>
    KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b ε) =
    (fun z : KernelTorus F ζ hζ C R P H U a => u (Quotient.out z)) from rfl, heq]
  exact hu.quotient_lift hrel

theorem actualCuspSheet_kernel_integrable
    (t : ℝ) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    Integrable (fun z : KernelTorus F ζ hζ C R P H U a =>
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b ε)
      (KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) := by
  letI := (monodromy F ζ hζ C R P H U a).compact
  letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U a
  letI := KPContActualChamberOutgoingAdapter.fiber_probability F ζ hζ C R P H U a
  exact (actualCuspSheet_kernel_continuous F ζ hζ C R P H U ι hι f hf a s hs t b ε).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end DedekindZetaZeroFree.KPContinuation.ChamberModerateGrowth

end
