module

public import DedekindZetaZeroFree.Analysis.QuadraticForms.TestDifferentialFriedrichsLaplacian
public import DedekindZetaZeroFree.Analysis.EllipticRegularity.IntegerSobolevEstimates

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPContLocalOrbifold

open MeasureTheory
open KPContLocalNorm KPContLocalEnergy KPContLocalRegularity

structure LineChart (n : ℕ) where
  stabilizer : Type
  group : Group stabilizer
  finite : Fintype stabilizer
  outer : LocalBall n
  densityLower : ℝ
  densityUpper : ℝ
  ellipticityLower : ℝ
  ellipticityUpper : ℝ
  densityLower_pos : 0 < densityLower
  ellipticityLower_pos : 0 < ellipticityLower
  coefficients : Coefficients outer densityLower densityUpper
    ellipticityLower ellipticityUpper

attribute [instance] LineChart.group LineChart.finite

end DedekindZetaZeroFree.KPContLocalOrbifold

end
