module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsLineWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsParametric
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Literal first and second parameter jets of position convolution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology

/- The scalar position projection used by the parameter jets. -/
def barrierPositionProjection : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ

/- The scalar velocity projection used by the parameter jets. -/
def barrierVelocityProjection : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

/- The actual position convolution integrand, with the integration variable fixed. -/
def barrierConvolutionIntegrand (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) : ℝ := κ (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)

/- The first parameter jet of the actual convolution integrand. -/
def barrierConvolutionJet (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (deriv κ (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)) • barrierPositionProjection +
    (κ (q.1 - Y) * bellmanDv phi (Y, q.2)) • barrierVelocityProjection

/- The second parameter jet, displaying only position kernel and velocity source derivatives. -/
def barrierConvolutionSecondJet (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
  ((deriv (deriv κ) (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)) •
      barrierPositionProjection + (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) •
      barrierVelocityProjection).smulRight barrierPositionProjection +
    ((deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) • barrierPositionProjection +
      (κ (q.1 - Y) * bellmanDvv phi (Y, q.2)) • barrierVelocityProjection).smulRight
      barrierVelocityProjection

/- The extension's velocity slice is differentiable at every nonzero position. -/
theorem barrier_slice_hasFDerivAt {alpha phi}
    (h : IsBellmanHomogeneous alpha phi) (q : ℝ × ℝ) (Y ) (hY : Y ≠ 0) :
    HasFDerivAt (fun p : ℝ × ℝ => bellmanOriginExtension phi (Y, p.2))
      (bellmanDv phi (Y, q.2) • barrierVelocityProjection) q := by
  have hq : (Y, q.2) ∈ bellmanPuncturedSet := fun he => hY (congrArg Prod.fst he)
  have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt
    (by norm_num)
  exact ((bellman_hasDerivAt_second hd).congr_of_eventuallyEq ((barrierExtension_eventuallyEq phi hq).comp_tendsto ((continuous_const.prodMk continuous_id).tendsto q.2))).comp_hasFDerivAt q hasFDerivAt_snd

/- The first velocity jet has its actual second slice derivative off the position origin. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
