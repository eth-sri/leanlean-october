module

public import DedekindZetaZeroFree.Moments.Comparison.TripleMellinKernel

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open MeasureTheory Complex

namespace PrincipalWShift

def kernel (Z : ℝ) (M W ζ L : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ)
    (ξ w z : ℂ) : ℂ :=
  comparisonRealPower (comparisonX Z) (1 / 2 - z) *
    comparisonRealPower Z (ξ + z - 1) *
    comparisonRealPower (comparisonY Z) (w - 1) *
    Complex.exp ((ξ + z - 1) ^ 2) * M z * W w *
    (ζ (6 * z) * ζ w / L ξ) * H ξ w z

def J (Z : ℝ) (M W ζ L : ℂ → ℂ) (H : ℂ → ℂ → ℂ → ℂ)
    (σξ σw σz : ℝ) : ℂ :=
  comparisonTripleVerticalIntegral σξ σw σz (kernel Z M W ζ L H)
