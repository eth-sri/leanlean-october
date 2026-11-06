module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.FirstReduced

@[expose] public section

namespace OAI


open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstActiveFourier
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstMixed CenteredMomentFirstReduced
local notation "O" => ActualEisensteinCubic.O

section
variable {ι : Type*} [Fintype ι] (P : ι → Ideal O) [∀ i,(P i).IsMaximal] (hcop : Pairwise (Function.onFun IsCoprime P)) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i) (hchar : ∀ i,ringChar (O ⧸ P i)≠2) (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
include ι P hcop hg hchar j hj0 hj6

theorem shifted_active_fourier    
       
     
     
     
           v h  :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    (∑' x : Residue r,G (Ideal.Quotient.mk _ v*x)*
      quotientTrace r (finitePrimeModulus_ne_zero P) (Ideal.Quotient.mk _ h*x)) =
      finiteSexticRow P hg j v*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j := by
  dsimp only
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i,P i) := Fintype.ofEquiv (Residue (finitePrimeModulus P)) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  rw [tsum_fintype]
  simp_rw [CenteredMomentFirstReduced.principalSexticRow_mul P hcop hg j
    (finitePrimeModulus P) (span_finitePrimeModulus P),
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P),mul_assoc]
  rw [← Finset.mul_sum,canonical_principal_gauss_transform P hcop hg hchar j hj0 hj6,
    principalSexticRow_mk P hcop hg j (finitePrimeModulus P) (span_finitePrimeModulus P)]
  rfl

theorem tripleFourier_active    
       
     
     
     
         
     a b   ha   hb 
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
     χa   χb   h  :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    tripleFourier a b r ha hb (finitePrimeModulus_ne_zero P) χa χb G h =
      χa (Ideal.Quotient.mk _ (b*r))*χb (Ideal.Quotient.mk _ (a*r))*
        residueGauss a ha χa (Ideal.Quotient.mk _ h)*residueGauss b hb χb (Ideal.Quotient.mk _ h)*
        (finiteSexticRow P hg j (a*b)*star (finiteSexticRow P hg j h)*canonicalGaussSum P hcop hg j) := by
  dsimp only
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let := finite_quotient_span (finitePrimeModulus_ne_zero P)
  let := finite_quotient_span (mul_ne_zero hb (finitePrimeModulus_ne_zero P))
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb (finitePrimeModulus_ne_zero P)))
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (b*finitePrimeModulus P)) := Fintype.ofFinite _
  let : Fintype (Residue (a*(b*finitePrimeModulus P))) := Fintype.ofFinite _
  unfold tripleFourier tripleResidue
  rw [tsum_fintype,three_factor_mixed_fourier a b (finitePrimeModulus P) ha hb
    (finitePrimeModulus_ne_zero P) har hbr]
  simp only [frequencyReduction_mk]
  have hs := shifted_active_fourier P hcop hg hchar j hj0 hj6 (a*b) h
  dsimp only at hs
  rw [tsum_fintype] at hs
  rw [hs]

end

end SevenEighths.CenteredMomentFirstActiveFourier



end OAI
