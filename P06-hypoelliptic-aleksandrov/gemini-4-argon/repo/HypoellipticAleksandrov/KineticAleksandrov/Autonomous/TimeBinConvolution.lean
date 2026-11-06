module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinConvolutionKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityStatement
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforward
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapRestriction
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartDensity
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimeBinConvolutionMass

/-! # The source one-index exponential time-bin convolution

Source: companion paper, Lemma 8.6. No spatial grid or centre-to-radius equality is used.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal Classical

/- The causal time-bin kernel, including the adjacent-bin delay. -/
def entranceBinWeight (c₀ : ℝ) (j k : ℤ) : ℝ≥0∞ :=
  if k ≤ j then ENNReal.ofReal (Real.exp (-c₀ * entranceBinDelay j k)) else 0

/- Each source-bin mixture inherits its mass times the proved restarted-tail norm. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
