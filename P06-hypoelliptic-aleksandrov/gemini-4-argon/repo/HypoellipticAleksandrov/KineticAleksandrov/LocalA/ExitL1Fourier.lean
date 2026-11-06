module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDisintegration
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.Sequences
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourier
import HypoellipticAleksandrov.KineticAleksandrov.Reconstruction.FiberDisintegration
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Fourier exit data in the complete space over the actual exit marginal -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Filter Topology Parabolic
open scoped ENNReal
open ProbabilityTheory Reconstruction

variable {d : ℕ}

/- Fourier exit data as an element of the complete `L¹` space of its marginal. -/
def exitL1Fourier (ν : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ν]
    (ξ : PDE.Vec d) : Lp ℂ 1 (exitMarginal ν) :=
  (integrable_exitFourierRep ν ξ).toL1 (exitFourierRep ν ξ)

/- The `L¹` Fourier element has the jointly measurable conditional representative. -/
theorem norm_exitL1Fourier (ν : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ν]
    (ξ : PDE.Vec d) :
    ‖exitL1Fourier ν ξ‖ = ((exitFourier ν ξ).variation univ).toReal := by
  have _h_xinl_0 : exitFourier ν ξ = (exitMarginal ν).withDensityᵥ (exitFourierRep ν ξ) := by
    ext E hE
    have _h_xinl_0 : (∫ z in E, exitFourierRep ν ξ z ∂exitMarginal ν) = exitFourier ν ξ E := by
      have hd := exitPositionKernel_disintegrate ν
      have hfin : IsFiniteMeasure (exitMarginal ν ⊗ₘ exitPositionKernel ν) :=
        hd.symm ▸ inferInstance
      have hfin' : IsFiniteMeasure
          ((exitMarginal ν).withDensity (fun _ => (1 : ℝ≥0∞)) ⊗ₘ exitPositionKernel ν) := by
        simpa only [withDensity_const, one_smul] using hfin
      have htop : ∀ᵐ _z ∂exitMarginal ν, (1 : ℝ≥0∞) < ⊤ := by simp
      have h := setIntegral_fiberDensity (m := exitMarginal ν) (g := fun _ => 1)
        measurable_const htop
        (exitPositionKernel ν) ξ hE
      simp only [withDensity_const, one_smul, fiberDensity, ENNReal.toReal_one, Complex.ofReal_one,
        one_mul] at h
      change (∫ z in E, exitFourierRep ν ξ z ∂exitMarginal ν) = _ at h
      rw [hd] at h
      rw [h, exitFourier_apply ν ξ E hE, ← integral_indicator (hE.prod MeasurableSet.univ),
        ← integral_indicator (hE.preimage measurable_snd)]
      rw [integral_map measurable_swap.aemeasurable]
      · apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun p => by
          by_cases hp : p.2 ∈ E <;>
            simp [hp, exitPhase, mul_comm])
      · have hc : Continuous (fun p : TimeVelocity d × PDE.Vec d =>
            Complex.exp (-((PDE.vecDot ξ p.2 : ℝ) * Complex.I))) := by
          unfold PDE.vecDot
          fun_prop
        exact (hc.measurable.indicator (hE.prod MeasurableSet.univ)).aestronglyMeasurable
    rw [withDensityᵥ_apply (integrable_exitFourierRep ν ξ) hE,
      _h_xinl_0]
  rw [_h_xinl_0,
    Measure.variation_withDensityᵥ (integrable_exitFourierRep ν ξ),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact Integrable.norm_toL1_eq_lintegral_enorm _ _

/- Frequency continuity holds in `L¹`, without a Banach-space structure on measures. -/
theorem continuous_exitL1Fourier (ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure ν] : Continuous (exitL1Fourier ν) := by
  apply continuous_iff_seqContinuous.mpr
  intro ξs ξ hξs
  change Tendsto
    (fun n => (memLp_one_iff_integrable.mpr (integrable_exitFourierRep ν (ξs n))).toLp
      (exitFourierRep ν (ξs n))) atTop
    (𝓝 ((memLp_one_iff_integrable.mpr (integrable_exitFourierRep ν ξ)).toLp
      (exitFourierRep ν ξ)))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
  have ht := tendsto_lintegral_norm_of_dominated_convergence
    (μ := exitMarginal ν) (F := fun n => exitFourierRep ν (ξs n))
    (f := exitFourierRep ν ξ) (bound := fun _ => (1 : ℝ))
    (fun n => (integrable_exitFourierRep ν (ξs n)).aestronglyMeasurable)
    (integrable_const (1 : ℝ)).hasFiniteIntegral
    (fun n => Eventually.of_forall (norm_exitFourierRep_le_one ν (ξs n)))
    (Eventually.of_forall (fun z => (continuous_exitFourierRep ν z).tendsto ξ |>.comp hξs))
  convert ht using 1
  funext n
  rw [eLpNorm_one_eq_lintegral_enorm
    ((integrable_exitFourierRep ν (ξs n)).sub
      (integrable_exitFourierRep ν ξ)).aestronglyMeasurable]
  apply lintegral_congr
  intro z
  exact (ofReal_norm (exitFourierRep ν (ξs n) z - exitFourierRep ν ξ z)).symm

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
