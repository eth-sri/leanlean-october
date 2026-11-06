module

public import Mathlib

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Topology.TietzeExtension

@[expose] public section


noncomputable section
open scoped BigOperators Topology
open Filter Set Complex MeasureTheory
open Classical
namespace DedekindZetaZeroFree.ComplexAnalysis.KernelTaylor.CauchyOperators
variable (w : ℂ) (R : ℝ)

section
variable (g : C(Metric.sphere w R, ℂ))
include g
def circleLift   (t : ℂ)  :=
  if ht : t ∈ Metric.sphere w R then g ⟨t, ht⟩ else 0

lemma circleLift_eq   (t : Metric.sphere w R) :
    circleLift w R g t = g t := by
  unfold circleLift
  rw [dite_eq_left t.property]

lemma circleLift_continuousOn   :
    ContinuousOn (circleLift w R g) (Metric.sphere w R) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert g.continuous using 1
  funext t
  apply circleLift_eq
end


lemma kernel_continuousOn (hR : 0 < R) (g : C(Metric.sphere w R, ℂ)) (q : ℕ) :
    ContinuousOn (fun t => (t-w)⁻¹^q * (t-w)⁻¹ * circleLift w R g t)
      (Metric.sphere w R) := by
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · apply ContinuousOn.pow
      apply ContinuousOn.inv₀ (by fun_prop)
      intro t ht
      intro he
      have  := sub_eq_zero.mp he
      subst t
      apply hR.ne' <;> aesop
    · apply ContinuousOn.inv₀ (by fun_prop)
      intro t ht he
      have  := sub_eq_zero.mp he
      subst t
      apply hR.ne' <;> aesop
  · apply circleLift_continuousOn

def circleCoeff (q : ℕ) (g : C(Metric.sphere w R, ℂ))  :=
  (2 * Real.pi * I : ℂ)⁻¹ * ∮ t in C(w,R),
    (t-w)⁻¹^q * (t-w)⁻¹ * circleLift w R g t

section
variable (hR : 0 < R) (q : ℕ)
include hR q
lemma circleCoeff_add   (g h : C(Metric.sphere w R, ℂ)) :
    circleCoeff w R q (g+h) = circleCoeff w R q g + circleCoeff w R q h := by
  unfold circleCoeff
  rw [← mul_add]
  congr 1
  rw [← circleIntegral.integral_add
    ((kernel_continuousOn w R hR g q).circleIntegrable hR.le)
    ((kernel_continuousOn w R hR h q).circleIntegrable hR.le)]
  apply circleIntegral.integral_congr hR.le
  intro t ht
  simp only [circleLift, dite_eq_left ht, ContinuousMap.add_apply, mul_add]

lemma circleCoeff_smul   (c : ℂ) (g : C(Metric.sphere w R, ℂ)) :
    circleCoeff w R q (c • g) = c • circleCoeff w R q g := by
  unfold circleCoeff
  simp only [smul_eq_mul]
  rw [mul_left_comm c, ← circleIntegral.integral_const_mul c]
  congr 1
  apply circleIntegral.integral_congr hR.le
  intro t ht
  simp only [circleLift, dite_eq_left ht, ContinuousMap.smul_apply, smul_eq_mul]
  ring

lemma circleCoeff_bound   (g : C(Metric.sphere w R, ℂ)) :
    ‖circleCoeff w R q g‖ ≤ R⁻¹^q * ‖g‖ := by
  have hb := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (c := w) (R := R) (C := R⁻¹^q * R⁻¹ * ‖g‖) hR.le
    (f := fun t => (t-w)⁻¹^q * (t-w)⁻¹ * circleLift w R g t)
  have he : R * (R⁻¹^q * R⁻¹ * ‖g‖) = R⁻¹^q * ‖g‖ := by
    field_simp
  rw [← he]
  apply hb
  intro t ht
  have hn : ‖t-w‖ = R := by simpa [dist_eq_norm] using ht
  simp only [norm_mul, norm_pow, norm_inv, hn, circleLift, dite_eq_left ht]
  gcongr
  apply ContinuousMap.norm_coe_le_norm

def circleCoeffCLM   : C(Metric.sphere w R, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := circleCoeff w R q
      map_add' := circleCoeff_add w R hR q
      map_smul' := circleCoeff_smul w R hR q }
    (R⁻¹^q) (circleCoeff_bound w R hR q)
end


end DedekindZetaZeroFree.ComplexAnalysis.KernelTaylor.CauchyOperators

end
