module
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalDyads
public import OAI.NumberTheory.DirichletL.Reflection.DyadBudget
public import OAI.NumberTheory.DirichletL.Reflection.MemberChoiceTransport

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

/-- Coprimality, residue characteristic and norm bounds for the dyadic
columns assembled from disjoint lists of primes. -/
theorem choice_tuple_arithmetic {Nlevel : Eis} {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J Q Q₀ : Ideal Eis) (A : Finset (FreeReflection.pool J Q Q₀))
    (lists : σ → Finset (Ideal Eis)) (H : σ → ℝ) {Hslot : ℝ}
    (hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
    (hmax : ∀ i, ∀ P ∈ lists i, P.IsMaximal)
    (hgood : ∀ i, ∀ P ∈ lists i, ConcretePrimeRowBridge.goodLambda ∉ P)
    (hprime : ∀ i, ∀ P ∈ lists i, Prime P)
    (hH : ∀ i, ∀ P ∈ lists i, (Ideal.absNorm P:ℝ)≤H i)
    (hprod : (∏ i,H i)≤Hslot) :
    let G := (poolPrimeFamily J Q Q₀).restrict A
    let FF := (poolPrimeFamily J Q Q₀).ideal
    let tuples := fixedSlotTupleSet lists FF
    let families := memberTupleFamily tuples (originalTupleMax lists FF hmax) (originalTupleGood lists FF hgood)
    (∀ f, IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
    (∀ f, ringChar (Eis⧸G.ideal f)≠2) →
    (∀ i, ∀ P ∈ lists i, IsCoprime (Ideal.span {Nlevel}) P) →
    (∀ i, ∀ P ∈ lists i, ringChar (Eis⧸P)≠2) →
    (∀ p, Pairwise (Function.onFun IsCoprime (G.sum (families p)).ideal)) ∧
    (∀ p b, IsCoprime (Ideal.span {Nlevel}) ((G.sum (families p)).ideal b)) ∧
    (∀ p b, ringChar (Eis⧸(G.sum (families p)).ideal b)≠2) ∧
    (∀ p∈tuples, CubicSieve.Admissible (slotTupleProduct p) ∧
      (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot) := by
  intro G FF tuples families hGN hGchar hLN hLchar
  have htuples : ∀ p∈tuples,∀ i,p i∈lists i := fun p hp => ((mem_fixedSlotTupleSet lists FF p).mp hp).1
  have hpair : ∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (families p)).ideal) := by
    intro p
    apply PrimeFamily.sum_pairwise G _ ((poolPrimeFamily J (Q) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (Q) Q₀) A)
    · intro i j hij
      apply Ideal.isCoprime_of_isMaximal
      intro heq
      change p.val i=p.val j at heq
      exact Finset.disjoint_left.mp (hdis hij) (htuples p.val p.property i)
        (heq.symm ▸ htuples p.val p.property j)
    · intro f i
      apply Ideal.isCoprime_of_isMaximal
      exact (((mem_fixedSlotTupleSet lists FF p.val).mp p.property).2 f.val i).symm
  have hPN : ∀ p : tuples,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (families p)).ideal b) := by
    intro p b
    cases b with
    | inl f => exact hGN f
    | inr i => exact hLN i _ (htuples p.val p.property i)
  have hPchar : ∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (families p)).ideal b)≠2 := by
    intro p b
    cases b with
    | inl f => exact hGchar f
    | inr i => exact hLchar i _ (htuples p.val p.property i)
  have hPnorm : ∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot := by
    intro p hp
    refine ⟨slotTupleProduct_admissible lists hdis hprime ?_ p (htuples p hp),?_⟩
    · intro i P hPi
      let : P.IsMaximal := hmax i P hPi
      exact (primaryPrime_eq_primaryGenerator P).symm ▸ primaryPrime_ne_zero P (hgood i P hPi)
    · exact (slotTupleProduct_norm_bound lists H (fun i P hPi => (hprime i P hPi).ne_zero) hH p (htuples p hp)).2.trans hprod
  exact ⟨hpair,hPN,hPchar,hPnorm⟩


end
end SevenEighths.InverseReflectedPhase

end OAI
