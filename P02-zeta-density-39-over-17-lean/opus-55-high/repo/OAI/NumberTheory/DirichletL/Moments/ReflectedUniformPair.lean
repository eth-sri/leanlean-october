module
public import OAI.NumberTheory.DirichletL.Moments.ReflectedPairEnergy
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedUniformPair
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
open CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy

def heightScale (A n : ℕ) (s t : ℝ) : ℝ := (1+s)^A/(1+‖t‖)^n

def normalizedReflected (V W : ℝ→ℂ) (A n : ℕ) (s t x : ℝ) : ℂ :=
  logWindow V x*((heightScale A n s t:ℝ):ℂ)*
    paperRadialFourier (CompletedHeight.normTwistedSource W t) (s*x)

def envelope (C : ℝ) (J : ℕ) (v : ℝ) : ℝ := C/(1+v^2)/(1+‖v‖)^J

lemma heightScale_pos (A n : ℕ) (s t : ℝ) (hs : 0< s) : 0<heightScale A n s t := by
  unfold heightScale
  positivity

section
variable (C : ℝ)
include C
lemma envelope_pos (hC : 0<C) (J : ℕ) (v : ℝ) : 0<envelope C J v := by
  unfold envelope
  positivity

lemma envelope_weight (J : ℕ) (v : ℝ) :
    envelope C J v*(1+‖v‖)^J=C/(1+v^2) := by
  unfold envelope
  field_simp

lemma envelope_integrable (J : ℕ) :
    Integrable (fun v : ℝ=>envelope C J v*(1+‖v‖)^J) := by
  simp_rw [envelope_weight,div_eq_mul_inv]
  exact integrable_inv_one_add_sq.const_mul C

lemma envelope_integral (J : ℕ) :
    (∫v : ℝ,envelope C J v*(1+‖v‖)^J)=C*Real.pi := by
  simp_rw [envelope_weight,div_eq_mul_inv]
  rw [integral_const_mul,integral_univ_inv_one_add_sq]
end

lemma normalized_density_bound (A n J : ℕ) (s t C : ℝ) (hs : 0< s)
    (b : 𝓢(ℝ,ℂ))
    (hp : ∀v : ℝ,(1+s)^A*(1+‖v‖)^(J+2)*‖b v‖≤C*(1+‖t‖)^n) :
    ∀v : ℝ,‖(((heightScale A n s t:ℝ):ℂ) • b) v‖≤envelope C J v := by
  intro v
  have ht : 0<(1+‖t‖)^n := by positivity
  have hv : 0<(1+‖v‖)^J := by positivity
  have hh : (1+‖v‖)^2*((1+‖v‖)^J*‖(((heightScale A n s t:ℝ):ℂ) • b) v‖)≤C := by
    rw [smul_apply,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (heightScale_pos A n s t hs).le]
    unfold heightScale
    have hh := (div_le_iff₀ ht).mpr (hp v)
    pm_5621
  have hnorm : 0≤(1+‖v‖)^J*‖(((heightScale A n s t:ℝ):ℂ) • b) v‖ := by positivity
  have hb := CubicReflectionKernel.weighted_two_to_cauchy hnorm v hh
  apply (le_div_iff₀ hv).mpr
  grind

end SevenEighths.CenteredMomentReflectedUniformPair

end

end OAI
