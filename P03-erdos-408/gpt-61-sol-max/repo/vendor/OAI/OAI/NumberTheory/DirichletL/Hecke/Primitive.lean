module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Hecke.IdealBridge
public import OAI.NumberTheory.DirichletL.Hecke.MellinIdentity
public import OAI.NumberTheory.DirichletL.GaussianTheta
public import OAI.NumberTheory.DirichletL.PeriodicThetaRegularity

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckePrimitive
open HeckeFamily

variable (c : O) [NeZero c]

theorem span_ne_bot : Ideal.span ({c} : Set O) ≠ ⊥ := by
  simpa only [ne_eq, Ideal.span_singleton_eq_bot] using NeZero.ne c

instance : Fintype (O ⧸ Ideal.span {c}) := by
  letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (span_ne_bot c)
  exact Fintype.ofFinite _

def character (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)  :=
  Character.ofResidue (Ideal.span {c}) (span_ne_bot c) χ hu

omit [NeZero c] in
theorem inverse_unit_trivial (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) :
    ∀ u : Oˣ, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1 := by
  intro u
  rw [MulChar.inv_apply_eq_inv', hu, inv_one]

def scale  := GaussianTheta.parameter c 1

theorem scale_pos : 0 < scale c := GaussianTheta.parameter_pos c 1 zero_lt_one

omit [NeZero c] in
theorem parameter_eq_scale_mul  t  : GaussianTheta.parameter c t = scale c * t := by
  unfold scale GaussianTheta.parameter
  ring

section
variable (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
include χ hu

theorem gaussianTheta_eq  
       t  :
    GaussianTheta.theta c χ t = HeckeTheta.theta (coefficients (character c χ hu))
      (scale c * t) := by
  unfold GaussianTheta.theta HeckeTheta.theta
  rw [← coordinateEquiv.tsum_eq]
  apply tsum_congr
  intro n
  rw [periodicCoeff_eq_elementCoeff]
  change χ (Ideal.Quotient.mk (Ideal.span {c}) (coordinateElement n.1 n.2)) *
      GaussianTheta.gaussian (GaussianTheta.parameter c t)
        (ConcreteTraceCRT.eisEmbedding (coordinateElement n.1 n.2)) = _
  congr 1
  unfold GaussianTheta.gaussian
  rw [Complex.ofReal_exp]
  congr 1
  rw [← Complex.ofReal_pow, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    ← normForm_eq_absNorm_span, parameter_eq_scale_mul]
  push_cast
  ring

def pair (χ )
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ)  :=
  PeriodicThetaRegularity.primitivePair
    (coefficients (character c χ hu))
    (coefficients (character c χ⁻¹ (inverse_unit_trivial c χ hu)))
    (scale c) (scale_pos c) (TraceCharacter.normalizedGauss c χ)
    (GaussianTheta.theta_root_nonzero c χ hp) (by
      intro t ht
      have h := GaussianTheta.theta_inversion c χ hp t ht
      rw [gaussianTheta_eq c χ hu,
        gaussianTheta_eq c χ⁻¹ (inverse_unit_trivial c χ hu)] at h
      simpa only [mul_one_div] using h)

section
variable (hp : FiniteFourier.IsPrimitiveOnIdeals χ)
include hp





def completedL (χ )
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (s : ℂ)  :=
  (pair c χ hu hp).Λ s / 6

section
variable {s : ℂ}
include s

theorem pair_completed_eq_right  
     
        (hs : 1 < s.re) :
    (pair c χ hu hp).Λ s = (scale c : ℂ) ^ (-s) *
      HeckeTheta.completed (coefficients (character c χ hu)) s := by
  let w := coefficients (character c χ hu)
  have h := (pair c χ hu hp).hasMellin hs
  calc
    (pair c χ hu hp).Λ s =
        mellin (fun t => HeckeTheta.theta w (scale c * t) - w (0,0)) s := h.2.symm
    _ = (scale c : ℂ) ^ (-s) * mellin (fun t => HeckeTheta.theta w t - w (0,0)) s :=
      by simpa only [smul_eq_mul] using
        mellin_comp_mul_left (fun t => HeckeTheta.theta w t - w (0,0)) s (scale_pos c)
    _ = (scale c : ℂ) ^ (-s) * HeckeTheta.completed w s := by
      congr 1
      rw [← (HeckeTheta.pair_hasMellin w hs).2]
      unfold mellin
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [HeckeTheta.theta_eq_pair w ht, HeckeTheta.pair_f₀]

section
variable (h0 : s ≠ 0) (h1 : s ≠ 1)
include h0 h1

theorem pair_completed_eq  
     
            :
    (pair c χ hu hp).Λ s = (scale c : ℂ) ^ (-s) *
      HeckeTheta.completed (coefficients (character c χ hu)) s :=
  HeckeMellinIdentity.scaled_eq (pair c χ hu hp)
    (HeckeTheta.pair (coefficients (character c χ hu))) rfl (HeckeTheta.pair_k _)
    (scale c) (scale_pos c) (fun _ hs => pair_completed_eq_right c χ hu hp hs) h0 h1

theorem symm_completed_eq  
     
            :
    (pair c χ hu hp).symm.Λ s =
      (pair c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv).Λ s := by
  apply HeckeMellinIdentity.eq_of_f (pair c χ hu hp).symm
    (pair c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv) rfl rfl _ rfl h0 h1
  solve_by_elim

theorem completedL_functional_equation  
     
            :
    completedL c χ hu hp (1-s) = TraceCharacter.normalizedGauss c χ *
      completedL c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv s := by
  have h := (pair c χ hu hp).functional_equation s
  change (pair c χ hu hp).Λ (1-s) = TraceCharacter.normalizedGauss c χ *
    (pair c χ hu hp).symm.Λ s at h
  grind [symm_completed_eq, completedL]

theorem completedL_eq_gamma_mul_LFunction  
     
       
        (hΓ : Complex.Gamma s ≠ 0) :
    completedL c χ hu hp s = (scale c : ℂ)^(-s) * (Real.pi : ℂ)^(-s) *
      Complex.Gamma s * LFunction (character c χ hu) s := by
  unfold completedL
  rw [pair_completed_eq c χ hu hp h0 h1]
  unfold LFunction continuedLattice HeckeTheta.latticeL
  simp only [Complex.cpow_neg]
  field_simp <;> ring

end

end

end

end

end SevenEighths.HeckePrimitive

end

end OAI
