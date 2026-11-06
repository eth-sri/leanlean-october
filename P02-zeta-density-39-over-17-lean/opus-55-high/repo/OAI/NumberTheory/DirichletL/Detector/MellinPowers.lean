module
public import OAI.NumberTheory.DirichletL.Detector.PhysicalNorms
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ProbeEuler

lemma sourceNormPower_identity (I J H X : ℝ) (hI : 0<I) (hJ : 0<J) (hH : 0<H) (hX : 0<X)
    (t z : ℂ) :
    ((I*J ^3:ℝ):ℂ)⁻¹*((X*H/(I*J ^3):ℝ):ℂ)^(-z)*
      ((I:ℂ)^(-t)*(J:ℂ)^(-3*t)) /
      ((Real.sqrt I:ℂ)*(J:ℂ)) * (Real.sqrt X:ℂ) =
      (X:ℂ)^(1/2-z)*(H:ℂ)^(-z)*
        (I:ℂ)^(-(t+1-z)-1/2)*(J:ℂ)^(-(1+3*(t+1-z))) := by
  pm_3058 hi I hI.ne'
  pm_3058 hj J hJ.ne'
  pm_3058 hh H hH.ne'
  pm_3058 hx X hX.ne'
  rw [←cpow_half_eq_sqrt I hI.le,←cpow_half_eq_sqrt X hX.le]
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (mul_pos hX hH).le (mul_pos hI (pow_pos hJ 3)).le]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  rw [Complex.mul_cpow_ofReal_nonneg hX.le hH.le]
  have hmul : ((I:ℂ)*(J:ℂ)^3)^(-z)=(I:ℂ)^(-z)*((J:ℂ)^3)^(-z) := by
    simpa only [Complex.ofReal_pow] using Complex.mul_cpow_ofReal_nonneg hI.le (pow_pos hJ 3).le (-z)
  rw [hmul]
  have hp : ((J:ℂ)^3)^(-z)=(J:ℂ)^((3:ℂ)*(-z)) := by
    pm_5751 hJ.le z
  rw [hp]
  rw [show (J:ℂ)^3=(J:ℂ)^(3:ℂ) by simp]
  pm_7887 hir I hi
  pm_7887 hjr J hj
  simp only [Complex.cpow_def_of_ne_zero hi,Complex.cpow_def_of_ne_zero hj,
    Complex.cpow_def_of_ne_zero hh,Complex.cpow_def_of_ne_zero hx,div_eq_mul_inv,
    mul_inv_rev,←Complex.exp_neg,←Complex.exp_add]
  rw [hir,hjr]
  simp only [←Complex.exp_neg,←Complex.exp_add]
  rw [Complex.exp_log hi,Complex.exp_log hj]
  congr 1
  ring

end SevenEighths.ProbePhysical
end

end OAI
