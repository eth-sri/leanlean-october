module

public import DedekindZetaZeroFree.Analysis.QuadraticForms.TestDifferentialFriedrichsLaplacian
public import DedekindZetaZeroFree.Analysis.EllipticRegularity.IntegerSobolevEstimates

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPContLocalOrbifold

open MeasureTheory
open KPContLocalNorm KPContLocalEnergy KPContLocalRegularity

structure LineChart (n : ℕ) where
  outer : LocalBall n
  densityLower : ℝ
  densityUpper : ℝ
  ellipticityLower : ℝ
  ellipticityUpper : ℝ
  densityLower_pos : 0 < densityLower
  ellipticityLower_pos : 0 < ellipticityLower
  coefficients : Coefficients outer densityLower densityUpper
    ellipticityLower ellipticityUpper
end DedekindZetaZeroFree.KPContLocalOrbifold

end
