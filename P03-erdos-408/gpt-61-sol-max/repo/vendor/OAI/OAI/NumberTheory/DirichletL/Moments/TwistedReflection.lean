module

public import OAI.NumberTheory.DirichletL.Moments.NaturalReflection
public import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge

@[expose] public section

namespace OAI


open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentTwistedReflection
open HeckeFamily CenteredMomentNaturalPrimitive CenteredMomentNaturalReflection
open CenteredMomentReflectionDeletion EisensteinSchwartzPoisson


lemma polynomial_twisted_source  χ   W   X t  (hX : 0<X) :
    HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)=
      HeckeDyadic.polynomial χ false (CompletedHeight.normTwistedSource W t) X 0 0 := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  have hm := HeckeDetectorDyadicBridge.norm_phase (I.val.absNorm:ℝ) X (HeckeDyadic.norm_pos I) hX 0 t
  simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  simp only [Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,CompletedHeight.normTwistedSource]
  simp only [HeckeDyadic.norm,HeckeDyadic.shift] at hm ⊢
  rw [hm]
  simp only [Complex.ofReal_zero]
  ring

end SevenEighths.CenteredMomentTwistedReflection



end OAI
