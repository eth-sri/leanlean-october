module
public import OAI.NumberTheory.DirichletL.Detector.GaussianPartition
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Filter
namespace SevenEighths.ProbePhysical
open CompletedGauss

def gaussianDyadicProfile (Z : ℝ) (j : ℕ) (y : ℝ) : ℂ :=
  gaussianAnnulus y*gaussianMellinProfile ((2:ℝ)^j*y/Z)/(Real.sqrt y:ℂ)

lemma gaussianDyadicProfile_Vstar (Z : ℝ) (j : ℕ) (y : ℝ) (hy : 0<y) :
    Vstar (gaussianDyadicProfile Z j) y=
      gaussianAnnulus y*gaussianMellinProfile ((2:ℝ)^j*y/Z) := by
  pm_3642 h y hy
  simp only [Vstar,gaussianDyadicProfile]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
