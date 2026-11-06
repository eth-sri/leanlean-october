module

public import OAI.NumberTheory.DirichletL.Moments.RadialCenteredEnergy
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalCappedAmplitude

@[expose] public section

namespace OAI


open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentAllocatedCenteredCapped
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle CenteredMomentExceptionalCappedAmplitude
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge UniqueFactorizationMonoid


variable {ι:Type*} [Fintype ι] [DecidableEq ι]

section
variable (L:Ideal ActualEisensteinCubic.O) (a:Allocation L (Finset.univ:Finset (ι⊕Fin 2))) (P:ι→ℝ)
include L a P

section
variable (hP:∀i,1≤P i)
include hP

lemma plain_norm_le_reduction    
         j :
    (Ideal.absNorm (selectedPlain L a j):ℝ)≤formalReductionFactor L a P:=by
  have hN (k:Fin 2):(1:ℝ)≤Ideal.absNorm (selectedPlain L a k):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr k)))
  have hh:(Ideal.absNorm (selectedPlain L a j):ℝ)≤selectedNorm L a:=by
    fin_cases j
    · exact le_mul_of_one_le_right (by positivity) (hN 1)
    · exact le_mul_of_one_le_left (by positivity) (hN 0)
  exact hh.trans (le_mul_of_one_le_right (selectedNorm_pos L a).le
    (Finset.one_le_prod₀ (fun i _=>hP i)))

lemma allocated_lower    
        (Z r X:ℝ) (hZ:0<Z) (hX:Z^r≤X)  j :
    Z^r/formalReductionFactor L a P≤X/(Ideal.absNorm (selectedPlain L a j):ℝ):=by
  have hn:(0:ℝ)<Ideal.absNorm (selectedPlain L a j):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero L Finset.univ a (Sum.inr j)))
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hZ.le _) hn
    (plain_norm_le_reduction L a P hP j)).trans (div_le_div_of_nonneg_right hX hn.le)

end

lemma remaining_volume    
      (hP:∀i,0<P i)  T :
    (T/selectedNorm L a)*(∏i:liveIndices L a,P i)=
      (T*∏i,P i)/formalReductionFactor L a P:=by
  rw [Finset.prod_coe_sort]
  apply (eq_div_iff (mul_pos (selectedNorm_pos L a) (Finset.prod_pos (fun i _=>hP i))).ne').mpr
  exact raw_scale_identity L a T P

end

end SevenEighths.CenteredMomentAllocatedCenteredCapped



end OAI
