module

public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWeights

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
namespace SevenEighths.InverseInitialHighFrequencyTail
open FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialEnergyCallerWeights
variable {ι σ : Type*} [DecidableEq ι]

theorem marked_support_norm_bound
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hdis : (slots:Set σ).PairwiseDisjoint lists)
    (ha : ∀i∈slots,∀k∈lists i,‖a i k‖≤1)
    (S : Finset ι) (L : ℝ) (hL : 1≤L) (hS : primeProductNorm p S≤L) :
    ‖primeMark slots lists a S‖≤128*L := by
  have heq : boundedPrimeSupports p S L=S.powerset := by
    apply Finset.filter_eq_self.mpr
    intro U hU
    exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hU)).trans hS
  have hc := boundedPrimeSupports_card p hinj S L hL
  rw [heq,Finset.card_powerset] at hc
  exact (primeMark_norm_le_divisor_count slots lists a S hdis ha).trans (by simp_all)

theorem initialColumn_mark_factor
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (Ψ : ActualEisensteinCubic.O→*ℂ) (j C d h : ActualEisensteinCubic.O) (H : Finset ι→ℂ) (S : Finset ι) :
    initialColumn p hp hcop hg Ψ j C d h H S =
      initialColumn p hp hcop hg Ψ j C d h (fun _=>1) S * H S := by
  simp only [initialColumn,mul_one]

theorem initialColumn_mark_norm
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀n,‖Ψ n‖≤1)
    (j C d h : ActualEisensteinCubic.O) (H : Finset ι→ℂ) (S : Finset ι) :
    ‖initialColumn p hp hcop hg Ψ j C d h H S‖≤‖H S‖ := by
  rw [initialColumn_mark_factor,norm_mul]
  exact (mul_le_mul_of_nonneg_right
    ((initialColumn_norm_le p hp hcop hg hc Ψ j C d h S).trans (by grind))
    (norm_nonneg _)).trans_eq (one_mul _)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
