module
public import OAI.NumberTheory.DirichletL.Detector.LowActualEnergies
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramCoefficient (C : CalibrationData) (σ : RayRing)
    (s : {I : Id // Supported I}) : ℂ :=
  if physicalIdealRay s=σ then lowArithmeticCoefficient C s else 0

def lowGramProfile (W1 : ℝ→ℂ) (v r : ℝ) : ℂ :=
  W1 r*(r:ℂ)^(-1+(v:ℂ)*Complex.I)

def lowGramScale (Y : ℝ) : ℂ := (Y:ℂ)⁻¹*(Real.sqrt Y:ℂ)⁻¹

lemma lowGramProfile_norm (W1 : ℝ→ℂ) (v r : ℝ) (hr : 0< r) :
    ‖lowGramProfile W1 v r‖=‖W1 r‖/r := by
  rw [lowGramProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp only [Complex.add_re,Complex.neg_re,Complex.one_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,
    Real.rpow_neg_one,div_eq_mul_inv]

lemma lowGramScale_mul_star (Y : ℝ) (hY : 0<Y) :
    lowGramScale Y*star (lowGramScale Y)=((Y^3:ℝ):ℂ)⁻¹ := by
  pm_3058 hy Y hY.ne'
  pm_3642 hs Y hY
  pm_3643 hsquare Y hY.le
  pm_382 lowGramScale map_mul map_inv₀ Complex.star_def Complex.conj_ofReal Complex.ofReal_pow
  field_simp
  ring_nf
  grind

theorem lowGaussColumn_unnormalized (C : CalibrationData) (W1 : ℝ→ℂ)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) :
    lowGaussColumn C W1 Y σ v s/(Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ)=
      lowGramScale Y*(lowGramCoefficient C σ s *
        lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y)) := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  have hr : 0<(Ideal.absNorm s.val:ℝ)/Y := div_pos hq hY
  have hrc : (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hsqrt : Real.sqrt (Ideal.absNorm s.val:ℝ)=
      Real.sqrt Y*Real.sqrt ((Ideal.absNorm s.val:ℝ)/Y) := by
    rw [←Real.sqrt_mul hY.le,mul_div_cancel₀ _ hY.ne']
  have hp : (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*
      (Real.sqrt ((Ideal.absNorm s.val:ℝ)/Y):ℂ)⁻¹=
        (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-1+(v:ℂ)*Complex.I) := by
    rw [←ProbeEuler.cpow_half_eq_sqrt _ hr.le,←Complex.cpow_neg,←Complex.cpow_add _ _ hrc]
    congr 1
    ring
  unfold lowGaussColumn lowGramCoefficient
  split_ifs
  · rw [hsqrt,Complex.ofReal_mul]
    simp only [div_eq_mul_inv,mul_inv_rev]
    calc
      _ = (Y:ℂ)⁻¹*(Real.sqrt Y:ℂ)⁻¹*(lowArithmeticCoefficient C s*W1 ((Ideal.absNorm s.val:ℝ)/Y))*
        ((((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*
          (Real.sqrt ((Ideal.absNorm s.val:ℝ)/Y):ℂ)⁻¹) := by ring_nf
      _ = _ := by rw [hp];unfold lowGramScale lowGramProfile;ring_nf
  · simp

end SevenEighths.ProbePhysical
end

end OAI
