module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionC2
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionMollification
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionBounds
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionJets
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsConvolutionWindow
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsLineWeak
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsParametric
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-! # Joint-plane regularity of the position-regularized barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov
open Set MeasureTheory Filter
open scoped Topology

/- The position convolution agrees with the literal parameter integral. -/
theorem barrier_position_regularization_joint {alpha phi}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta) :
    ContDiff ℝ 2 (positionConvolution eta (bellmanOriginExtension phi)) := by
  have _h_inl_7 (eta : ℝ → ℝ) (phi) : positionConvolution eta (bellmanOriginExtension phi) = positionBarrierConvolution eta phi := by
      exact (
    rfl
    )
  rw [_h_inl_7]
  have hκ : ContDiff ℝ 2 eta := (heta.1.of_le (by simp))
  have hs := heta.2.1
  rw [contDiff_iff_contDiffAt]
  exact fun q => (positionBarrierConvolution_jet_spec h ha ha1 eta hκ hs q).1

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
