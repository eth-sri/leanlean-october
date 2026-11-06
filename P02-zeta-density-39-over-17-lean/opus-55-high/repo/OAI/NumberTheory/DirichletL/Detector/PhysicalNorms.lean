module
public import OAI.NumberTheory.DirichletL.Detector.MellinScaling
public import OAI.NumberTheory.DirichletL.Detector.SpectralWeights
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma elementNorm_mul (a b : ActualEisensteinCubic.O) :
    elementNorm (a*b)=elementNorm a*elementNorm b := by
  simp only [elementNorm,←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

lemma elementNorm_pow (a : ActualEisensteinCubic.O) (n : ℕ) :
    elementNorm (a^n)=elementNorm a^n := by
  simp only [elementNorm,←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]

lemma physical_radial_argument (B A s H : ActualEisensteinCubic.O) (X : ℝ)
    (hB : elementNorm B≠0) (hs : elementNorm s≠0) :
    (elementNorm B*elementNorm s*X)*elementNorm H/elementNorm ((B*A)*s)=
      X*elementNorm H/elementNorm A := by
  simp only [elementNorm_mul]
  field_simp

lemma physical_poisson_prefactor (B A S X : ℝ) (hB : 0<B) (hA : 0<A) (hS : 0<S) (hX : 0<X) :
    (Real.sqrt (B*S*X):ℂ)⁻¹*(Real.sqrt S:ℂ)⁻¹*((B*S*X/(B*A):ℝ):ℂ)=
      (Real.sqrt X:ℂ)/(Real.sqrt B:ℂ)/(A:ℂ) := by
  pm_3058 hBc B hB.ne'
  pm_3058 hAc A hA.ne'
  pm_3642 hSb B hB
  pm_3642 hSs S hS
  pm_3642 hSx X hX
  rw [Real.sqrt_mul (mul_pos hB hS).le,Real.sqrt_mul hB.le]
  simp only [Complex.ofReal_mul,Complex.ofReal_div]
  field_simp
  pm_3643 hb B hB.le
  pm_3643 hs S hS.le
  pm_3643 hx X hX.le
  grind

end SevenEighths.ProbePhysical
end

end OAI
