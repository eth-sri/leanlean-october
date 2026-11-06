module
public import OAI.NumberTheory.DirichletL.Moments.SlotNormalization
public import OAI.NumberTheory.DirichletL.Moments.PrimeSlotShift
public import OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer
public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationProfiles

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots CenteredMomentRetainedEnergy CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot CenteredMomentSlotNormalization

lemma plain_zero_height (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    polynomial χ false W X 0 0 = (Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W 0 X := by
  rw [sqrt_inverse_cpow X hX]
  unfold polynomial twistedIdealSum
  congr 1
  have he := tsum_subtype_eq_of_support_subset
    (s := {I : Ideal O | I≠0})
    (f := fun I : Ideal O=>idealCoeff χ I*W ((I.absNorm:ℝ)/X))
    (by intro I hI hi; subst I; exact hI (by simp only [map_zero,zero_mul]))
  change (∑' I : HeckeDyadic.NonzeroIdeal,idealCoeff χ I.val*W ((I.val.absNorm:ℝ)/X))=
    ∑' I : Ideal O,idealCoeff χ I*W ((I.absNorm:ℝ)/X) at he
  simpa only [summand,coefficient,Bool.false_eq_true,ite_false,HeckeDyadic.norm,HeckeDyadic.shift,
    Complex.ofReal_zero,zero_mul,mul_zero,sub_zero,neg_zero,Complex.cpow_zero,mul_one,
    HeckeDyadic.NonzeroIdeal,UnrestrictedIdealReindex.NonzeroIdeal] using he

theorem plain_polynomial_eq_row (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W : ℝ→ℂ) (X σ t : ℝ) (hX : 0<X) :
    polynomial χ false W X σ t = (Real.sqrt X:ℂ)⁻¹*
      rowTwistedSum η m A z (twistProfile W σ t) 0 X := by
  rw [←polynomial_twistProfile,plain_zero_height _ _ X hX,rowTwistedSum_eq η χ m A z hrow]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveSlotRow_eq_product
    (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η m A z (twistProfile W₁ σ t) (twistProfile W₂ σ t) S β P 0 X₁ X₂ =
      polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
        ∏i,normalizedSlot η m A z (S i) (β i) 0 (P i) := by
  rw [←selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ (mul_pos hX₁ hX₂).le (fun i=>(hP i).le)]
  unfold selectedProduct
  rw [plain_polynomial_eq_row η χ m A z hrow W₁ X₁ σ t hX₁,
    plain_polynomial_eq_row η χ m A z hrow W₂ X₂ σ t hX₂,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  ring

theorem oriented_twist_support (reverse : Bool) (W : ℝ→ℂ) (σ t : ℝ) :
    Function.support (twistProfile (HeckeDetectorCoefficientTransfer.orientedProfile reverse W) σ t)
      ⊆Function.support W := by
  apply (twistProfile_support _ _ _).trans
  cases reverse <;> simp only [HeckeDetectorCoefficientTransfer.orientedProfile,ite_true]
  · exact Set.Subset.rfl
  · intro x hx hzero
    exact hx (by simp only [hzero,map_zero])
