module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 
open Filter    
open ActualEisensteinCubic
 
open   RationalPrimeExtraction ShortDraftLatticeCount
 
 
 
open EisensteinEmbedding ConcreteTraceCRT  
 
 
open scoped LSeries.notation ArithmeticFunction.Moebius
 
 
 
 
 
 
 
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal      
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
open scoped ContDiff    
 
 
 
 
 
 
 
 
 
 
 
 
 
open   Set
 
 
 
 
 
 
 
 

namespace CompletedGauss
 
 

section
local notation "Eis" => ActualEisensteinCubic.O

lemma nonzeroDualIdeal_norm_pos (I : NonzeroDualIdeal) :
    0<(Ideal.absNorm I.val:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

lemma nonzeroDualIdeal_inv_pow_summable  n  (hn : 1<n) :
    Summable (fun I : NonzeroDualIdeal => ((Ideal.absNorm I.val:ℝ)^n)⁻¹) := by
  have hs := (CubicEisenstein.fullIdealWeight_summable_norm (n:ℂ)
    (by exact_mod_cast hn)).subtype (fun I : Ideal Eis => I≠0)
  apply hs.congr
  intro I
  simp only [Function.comp_apply,CubicEisenstein.fullIdealWeight,ite_eq_right I.property,
    Complex.cpow_neg,Complex.cpow_natCast,norm_inv,norm_pow,Complex.norm_natCast]

def rawDualKernelTerm (V : ℝ→ℂ) (scale ρ q : ℝ)
    (β : ℕ→Ideal Eis→Ideal Eis→ℂ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal)  :=
  β x.1 x.2.1.val x.2.2.val * CubicReflectionKernel.paperKernel V
    (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)

lemma rawDualKernel_inverse_square (scale ρ q : ℝ) (x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal) :
    ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ =
      (scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹) := by
  ring

theorem rawDualKernelTerm_summable_norm
     V  (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (scale ρ q B : ℝ) (hscale : 0<scale) (hρ : 0<ρ) (hq : 1<q)
    (hB : 0≤B)  β 
    (hβ : ∀m,∀I J : NonzeroDualIdeal,‖β m I.val J.val‖≤B) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal =>
      ‖rawDualKernelTerm V scale ρ q β x‖) := by
  obtain ⟨C,hC,hdec⟩:=CubicReflectionKernel.paperKernel_euler_power_decay
    V a b ha hsupp hV 2 0
  have hq6 : 1<q^6 := one_lt_pow₀ hq (by norm_num)
  have hg : Summable (fun m : ℕ => ((q^6)⁻¹)^m) :=
    summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ (by positivity)).mpr hq6)
  have hi := nonzeroDualIdeal_inv_pow_summable 2 (by norm_num)
  have hj := nonzeroDualIdeal_inv_pow_summable 6 (by norm_num)
  have hij := hi.mul_of_nonneg hj (fun I=>by positivity) (fun J=>by positivity)
  have hs := hg.mul_of_nonneg hij (fun m=>by positivity) (fun IJ=>by positivity)
  have hmajor := hs.mul_left (B*C*(scale^2*ρ^6)⁻¹)
  apply hmajor.of_nonneg_of_le (fun _=>norm_nonneg _)
  intro x
  have hn:=nonzeroDualIdeal_norm_pos x.2.1
  have hb:=nonzeroDualIdeal_norm_pos x.2.2
  have hx : 0<scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3 := by positivity
  have hk := (hdec _ hx).2
  simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hk
  norm_num only [Nat.cast_ofNat] at hk
  have hr : (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^(-(2:ℝ))=
      ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ := by
    rw [Real.rpow_neg hx.le,Real.rpow_two]
  rw [hr,rawDualKernel_inverse_square] at hk
  calc
    _ = ‖β x.1 x.2.1.val x.2.2.val‖*
        ‖CubicReflectionKernel.paperKernel V
          (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)‖ := by
        rw [rawDualKernelTerm,norm_mul]
    _ ≤ B*(C*((scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹))) :=
      mul_le_mul (hβ x.1 x.2.1 x.2.2) hk (norm_nonneg _) hB
    _ = _ := by ring

end



open   CanonicalQuadraticSieve CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

namespace ReflectedBranchData

end ReflectedBranchData

end CompletedGauss

namespace CubicEisenstein

section
 
open scoped       MatrixGroups

section
open     CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local instance ramifiedFrequencyUnitsFintype : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma ramifiedFrequencyChar_neg_unit  k   u   n  :
    ramifiedFrequencyChar k (-u) n=ramifiedFrequencyChar k u n := by
  ext x
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  have hp:lambda^2∣(1+3*d)-1:=by
    rw [add_sub_cancel_left]
    exact dvd_mul_of_dvd_left lambda_sq_dvd_three d
  rw [ramifiedFrequencyChar_mk,ramifiedFrequencyChar_mk,Units.val_neg,neg_mul,
    symbol_neg_numerator _ _ hp]

lemma arithmeticResidueSum_neg_unit (h:Eis) (u:Eisˣ)  n  (hn:2≤n) :
    arithmeticResidueSum (-h) (u.val*lambda^n)=
      arithmeticResidueSum h ((-u).val*lambda^n) := by
  by_cases hd:u.val*lambda^n∣3*(-h)
  · obtain ⟨k,hk⟩:=hd
    have hk':3*h=((-u).val*lambda^n)*k:=by
      simp only [Units.val_neg]
      linear_combination -hk
    rw [ramified_arithmetic_character_test (-h) k u n hn hk,
      ramified_arithmetic_character_test h k (-u) n hn hk',ramifiedFrequencyChar_neg_unit]
  · have hl:arithmeticResidueSum (-h) (u.val*lambda^n)=0:=by
      by_contra he
      exact hd (ramified_arithmetic_support (-h) u n hn he)
    have hr:arithmeticResidueSum h ((-u).val*lambda^n)=0:=by
      by_contra he
      obtain ⟨k,hk⟩:=ramified_arithmetic_support h (-u) n hn he
      simp_all
    rw [hl,hr]

lemma principalResidueTerm_neg  h   u   n  :
    principalResidueTerm (-h) u n=principalResidueTerm h (-u) n := by
  simp_all [principalResidueTerm, arithmeticResidueSum_neg_unit]

lemma principalArithmeticResidue_neg  h  :
    principalArithmeticResidue (-h)=principalArithmeticResidue h := by
  by_cases hh:h=0
  · rw [hh,neg_zero]
  let N:=max (ramifiedFrequencyBound (-h)+1) (ramifiedFrequencyBound h+1)
  rw [principalArithmeticResidue_eq_sum (-h) (neg_ne_zero.mpr hh) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum h hh N (le_max_right _ _)]
  apply congrArg (fun z:ℂ=>z/((9*Real.sqrt 3/2:ℝ):ℂ))
  simp_rw [principalResidueTerm_neg]
  exact Fintype.sum_equiv (Equiv.neg Eisˣ)
    (fun u=>∑n∈Finset.range N,principalResidueTerm h (-u) n)
    (fun u=>∑n∈Finset.range N,principalResidueTerm h u n) (fun _=>rfl)

theorem sourceArithmeticResidue_neg  h  :
    sourceArithmeticResidue (-h)=sourceArithmeticResidue h := by
  have hU:unramifiedGaussResidue (-(9*h))=unramifiedGaussResidue (9*h):=by
    have he:=unramifiedGaussResidue_of_initial_relation (-(9*h)) (9*h) 0
      (fun _=>1) (fun _=>0) (fun _ _=>analyticAt_const) (fun _ _=>analyticAt_const)
      continuousAt_const continuousAt_const
      (fun s hs hi=>by simpa only [one_mul,zero_mul,add_zero] using unramifiedCubicGaussSeries_neg s (9*h))
    simpa only [one_mul,zero_mul,add_zero] using he
  simp only [sourceArithmeticResidue,cuspFrequency_neg,
    AddChar.map_neg_eq_inv,inv_eq_one,principalArithmeticResidue_neg,
    mul_neg,hU]

lemma cubicBesselNormalizer_neg  h  : cubicBesselNormalizer (-h)=cubicBesselNormalizer h := by
  simp only [cubicBesselNormalizer,cuspFrequency_neg,norm_neg]

theorem sourceResidualFourierCoefficient_neg  h  :
    sourceResidualFourierCoefficient (-h)=sourceResidualFourierCoefficient h := by
  rw [sourceResidualFourierCoefficient,sourceResidualFourierCoefficient,
    cubicBesselNormalizer_neg,sourceArithmeticResidue_neg]

end

section
open     CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceRayPhase_eq_one_iff_coordinate  h  :
    ShortDraftTrace.breveE (cuspFrequency h)=1 ↔
      (3:ℤ)∣(ActualEisensteinCoordinates.coords h).2 := by
  have he:ShortDraftTrace.breveE (cuspFrequency h)=
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        3 (by norm_num) (Ideal.Quotient.mk _ h):=by
    rw [eisTraceModChar,IdealGaussCRT.traceModChar_mk]
    unfold cuspFrequency
    simp only [map_ofNat]
  rw [he,trace_third_coordinate]
  simpa only [pow_zero,one_mul,Nat.cast_zero,zero_add] using
    omega3_pow_exp_eq_one_iff 0 (ActualEisensteinCoordinates.coords h).2

lemma primary_or_negative_primary_of_source_mask  h  (h3:¬(3:Eis)∣h)
    (hphase:ShortDraftTrace.breveE (cuspFrequency h)=1) :
    lambda^2∣h-1 ∨ lambda^2∣(-h)-1 := by
  let a:ℤ:=(ActualEisensteinCoordinates.coords h).1
  let b:ℤ:=(ActualEisensteinCoordinates.coords h).2
  have heval:h=(a:Eis)+(b:Eis)*omega:=
    (ActualEisensteinCoordinates.eval_coords h).symm
  obtain ⟨B,hB⟩:=(sourceRayPhase_eq_one_iff_coordinate h).mp hphase
  have hBc:(b:Eis)=3*(B:Eis):=by exact_mod_cast hB
  have ha:¬(3:ℤ)∣a:=by
    rintro ⟨A,hA⟩
    apply h3
    refine ⟨(A:Eis)+(B:Eis)*omega,?_⟩
    have hAc:(a:Eis)=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hAc,hBc]
    ring
  have hcases:(3:ℤ)∣a-1 ∨ (3:ℤ)∣a+1:=by omega
  rcases hcases with ⟨A,hA⟩|⟨A,hA⟩
  · left
    apply lambda_sq_dvd_three.trans
    refine ⟨(A:Eis)+(B:Eis)*omega,?_⟩
    have hAc:(a:Eis)-1=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hBc]
    linear_combination hAc
  · right
    apply lambda_sq_dvd_three.trans
    refine ⟨-((A:Eis)+(B:Eis)*omega),?_⟩
    have hAc:(a:Eis)+1=3*(A:Eis):=by exact_mod_cast hA
    rw [heval,hBc]
    linear_combination -hAc

end

open     CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem sourceFourier_supported_three_of_base_zero (hC:infinityCoefficientScalar=0)
     h  (h3:¬(3:Eis)∣h) : sourceResidualFourierCoefficient h=0 := by
  by_cases hm:ShortDraftTrace.breveE (cuspFrequency h)=1
  · rcases primary_or_negative_primary_of_source_mask h h3 hm with hh|hh
    · exact sourceFourier_primary_zero_of_base_zero hC h hh
    · rw [←sourceResidualFourierCoefficient_neg h]
      exact sourceFourier_primary_zero_of_base_zero hC (-h) hh
  simp_all [sourceResidualFourierCoefficient, sourceArithmeticResidue]

end

open     CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

theorem infinityCoefficientScalar_ne_zero : infinityCoefficientScalar≠0 := by
  intro hC
  obtain ⟨h,h3,hn⟩:=exists_source_coefficient_not_three
  exact hn (sourceFourier_supported_three_of_base_zero hC h h3)

theorem normalized_infinityCoefficient_squarefree_cube  I J 
     hI  (hJ:primaryGenerator J≠0) (hsq:Squarefree I) :
    infinityCoefficientScalar⁻¹*
      star (sourceResidualFourierCoefficient (primaryGenerator I*(primaryGenerator J)^3))=
      (‖eisEmbedding (primaryGenerator J)‖:ℂ)*
        star (eisEmbedding (symbol ramifiedTraceLambda (primaryGenerator I)))*gaussTwo I hI := by
  rw [infinityCoefficient_squarefree_cube I J hI hJ hsq]
  grind [infinityCoefficientScalar_ne_zero]

end CubicEisenstein

end

end OAI
