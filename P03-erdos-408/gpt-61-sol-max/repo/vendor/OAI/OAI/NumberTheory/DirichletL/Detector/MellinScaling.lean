module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.RadialMellin
public import OAI.NumberTheory.DirichletL.Detector.Physical

@[expose] public section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open EisensteinSchwartzPoisson

def sourceMellinWeight (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)  :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)*
    Complex.exp ((x+z-1)^2)*mellin (paperRadialFourier W0) z*mellin W1 w

lemma sourceMellinWeight_marked  W0 W1   X Y Z Q 
    (hZ : 0<Z) (hQ : 0<Q)  x w z  :
    sourceMellinWeight W0 W1 X Y (Z*Q) x w z=
      (Q:ℂ)^(x+z-1)*sourceMellinWeight W0 W1 X Y Z x w z := by
  unfold sourceMellinWeight
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hZ.le hQ.le]
  ring

lemma sourceMellinWeight_rescaled  W0 W1   X Y Z Q 
    (hX : 0<X) (hY : 0<Y) (hQ : 0<Q)  x w z  :
    ((Q^(-(3/2:ℝ)):ℝ):ℂ)*sourceMellinWeight W0 W1 (X/Q) (Y/Q) Z x w z=
      (Q:ℂ)^(z-w-1)*sourceMellinWeight W0 W1 X Y Z x w z := by
  have hQc : (Q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  unfold sourceMellinWeight
  rw [Complex.ofReal_div,Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hX.le hQ.le,Complex.div_cpow_ofReal_nonneg hY.le hQ.le,
    Complex.ofReal_cpow hQ.le]
  simp only [div_eq_mul_inv,←Complex.cpow_neg]
  have he : (Q:ℂ)^((-(3/2:ℝ):ℝ):ℂ)*(Q:ℂ)^(-(1/2-z))*(Q:ℂ)^(-(w-1))=(Q:ℂ)^(z-w-1) := by
    rw [←Complex.cpow_add _ _ hQc,←Complex.cpow_add _ _ hQc]
    congr 1
    push_cast
    ring
  grind

end SevenEighths.ProbePhysical
end

end OAI
