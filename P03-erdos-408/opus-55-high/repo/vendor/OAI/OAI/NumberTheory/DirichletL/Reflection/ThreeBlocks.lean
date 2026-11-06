module

public import OAI.NumberTheory.DirichletL.Reflection.Cross

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
noncomputable section
variable {ι : Type*} [Fintype ι] {p : ι → ActualEisensteinCubic.O} {N a c : ActualEisensteinCubic.O} {mode : Bool}
noncomputable local instance threeBlockFinite (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] : Fintype (ActualEisensteinCubic.O ⧸ P) := Fintype.ofFinite _

def residualWithFrozen [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (c : ActualEisensteinCubic.O) (R F : Finset ι) : ℂ :=
  ∏ i ∈ R, (∏ k ∈ R.erase i, MixedCrossSeparation.crossSymbol p hg i k^4)*
    (residualPrimeScalar (p i) c (hp i) (hg i)*∏ k ∈ F, MixedCrossSeparation.crossSymbol p hg i k^4)

def markedWithFrozen [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (c : ActualEisensteinCubic.O) (P F : Finset ι) : ℂ :=
  ∏ i ∈ P, (∏ k ∈ P.erase i, MixedCrossSeparation.crossSymbol p hg i k^2)*
    (markedPrimeScalar (p i) c (hp i) (hg i)*∏ k ∈ F, MixedCrossSeparation.crossSymbol p hg i k^2)

def frozenPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι) : ℂ :=
  ∏ i ∈ F, (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)

theorem activePhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0) :
    D.activePhase hp hg j = residualWithFrozen hp hg c R F *
      markedWithFrozen hp hg c P F * frozenPhase D hp hg j F := by
  let l : ι → ℂ := fun i => if i ∈ R then residualPrimeScalar (p i) c (hp i) (hg i)
    else markedPrimeScalar (p i) c (hp i) (hg i)
  let v : ι → ℂ := fun i => (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)
  have hm : (∏ i ∈ R ∪ P, v i) = ∏ i ∈ R ∪ P,
      (∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^
        (if i ∈ R then 4 else 2))*l i := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hr : i ∈ R
    · simp only [v,hRj i hr,l,hr,ite_true]
      rw [controlled_residual_phase]
      ring
    · have hp' := (Finset.mem_union.mp hi).resolve_left hr
      simp only [v,hPj i hp',l,hr,ite_false]
      rw [controlled_marked_phase]
      ring
  have hfull : D.activePhase hp hg j = (∏ i ∈ R ∪ P, v i)*frozenPhase D hp hg j F := by
    change (∏ i, v i) = (∏ i ∈ R ∪ P, v i)*(∏ i ∈ F, v i)
    rw [← Finset.prod_union hF,hu]
  rw [hfull,hm,ordered_cross_frozen_partition _ l 4 2 R P F hRP hF hu,
    InverseMoment.row_slot_product_phase p hcop hg hprimary R P hRP,mul_one]
  congr 2
  · apply Finset.prod_congr rfl
    grind
  · apply Finset.prod_congr rfl
    grind

end
end SevenEighths.InverseReflectedPhase

end OAI
