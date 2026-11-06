module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Reflection.BoundedTemplates

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve FiniteGaussPhase

local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*} {p : ι → Eis} {N a c : Eis} {mode : Bool}

section
variable [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
include hg hcop

lemma frozenCofactorCharacter_cross_norm  
     
     
     i k  (hik : i ≠ k)  j  :
    ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (p k)‖ = 1 := by
  have hn := crossSymbol_norm hg hcop i k hik
  unfold frozenCofactorCharacter
  split_ifs
  · simp only [MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv',norm_pow,norm_inv]
    simp_all [MixedCrossSeparation.crossSymbol]
  · simp only [MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by omega : 2*j+2 ≠ 0),norm_pow]
    simp_all [MixedCrossSeparation.crossSymbol]

lemma frozenCofactorCharacter_product_norm  
     
     
     i   S  (hi : i ∉ S)  j  :
    ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (∏ k ∈ S, p k)‖ = 1 := by
  rw [map_prod,norm_prod]
  apply Finset.prod_eq_one
  intro k hk
  exact frozenCofactorCharacter_cross_norm hg hcop i k (fun h => hi (h ▸ hk)) j

end

variable [Fintype ι]

section
variable [∀ i, (Ideal.span {p i}).IsMaximal] (D : ControlledStratumArithmetic p N a c mode) (hp : ∀ i, p i ≠ 0) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
include D hp hg hchar hcop

lemma frozenPrimeScalar_norm  
     
       
     
     
     i   j  (hj : j < 6) : ‖frozenPrimeScalar (p i) c (hp i) (hg i) j‖ = 1 := by
  have hh := local_phase_norm D hp hg hchar i j hj
  rw [controlled_frozen_phase,norm_mul] at hh
  have hn : ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (cofactor p i)‖ = 1 := frozenCofactorCharacter_product_norm hg hcop i (Finset.univ.erase i) (by simp) j
  simpa only [hn,mul_one] using hh

lemma frozenCore_norm  
     
       
     
     
     j   F  (hj : ∀ i ∈ F, j i < 6) : ‖frozenCore hp hg c j F‖ = 1 := by
  rw [frozenCore,norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [norm_mul,frozenPrimeScalar_norm D hp hg hchar hcop i (j i) (hj i hi),one_mul]
  exact frozenCofactorCharacter_product_norm hg hcop i (F.erase i) (by simp) (j i)

end


end SevenEighths.InverseReflectedPhase

end OAI
