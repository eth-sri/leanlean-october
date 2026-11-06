module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.MellinScaling
public import OAI.NumberTheory.DirichletL.Detector.SpectralWeights

@[expose] public section

namespace OAI


namespace SevenEighths.ProbePhysical

lemma elementNorm_mul  a b  :
    elementNorm (a*b)=elementNorm a*elementNorm b := by
  simp_all [elementNorm]

lemma elementNorm_pow  a   n  :
    elementNorm (a^n)=elementNorm a^n := by
  simp_all [elementNorm]

lemma physical_radial_argument  B A s H   X 
    (hB : elementNorm B≠0) (hs : elementNorm s≠0) :
    (elementNorm B*elementNorm s*X)*elementNorm H/elementNorm ((B*A)*s)=
      X*elementNorm H/elementNorm A := by
  simp only [elementNorm_mul]
  field_simp

lemma physical_poisson_prefactor  B A S X  (hB : 0<B) (hA : 0<A) (hS : 0<S) (hX : 0<X) :
    (Real.sqrt (B*S*X):ℂ)⁻¹*(Real.sqrt S:ℂ)⁻¹*((B*S*X/(B*A):ℝ):ℂ)=
      (Real.sqrt X:ℂ)/(Real.sqrt B:ℂ)/(A:ℂ) := by
  have hBc : (B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hB.ne'
  have hAc : (A:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hSb : (Real.sqrt B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB).ne'
  have hSs : (Real.sqrt S:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hS).ne'
  have hSx : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  rw [Real.sqrt_mul (mul_pos hB hS).le,Real.sqrt_mul hB.le]
  simp only [Complex.ofReal_mul,Complex.ofReal_div]
  field_simp
  
  have hs : (Real.sqrt S:ℂ)^2=(S:ℂ) := by exact_mod_cast Real.sq_sqrt hS.le
  have hx : (Real.sqrt X:ℂ)^2=(X:ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  rw [hs,hx]

end SevenEighths.ProbePhysical


end OAI
