module

public import OAI.NumberTheory.DirichletL.Descent.Completion

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section

theorem bounded_row_square_expansion {β : Type*}
    (C : Finset β) (a : β→ℂ) (r : β→ActualEisensteinCubic.O→ℂ) (hr : ∀b∈C,∀z,‖r b z‖≤1)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑'z:ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/K)*(‖∑b∈C,a b*r b z‖^2:ℝ))=
      ∑b∈C,∑c∈C,(star (a b)*a c)*∑'z:ActualEisensteinCubic.O,(star (r b z)*r c z)*W (‖eisEmbedding z‖^2/K) := by
  have hs (b c : β) (hb:b∈C) (hc:c∈C) : Summable (fun z:ActualEisensteinCubic.O =>
      (star (r b z)*r c z)*W (‖eisEmbedding z‖^2/K)) := by
    have hW : Summable (fun z:ActualEisensteinCubic.O=>‖W (‖eisEmbedding z‖^2/K)‖) := by
      simpa only [EisensteinSchwartzPoisson.scaledRadialTest_apply] using
        EisensteinSchwartzPoisson.actual_eisenstein_summable_norm
          (EisensteinSchwartzPoisson.scaledRadialTest W K hK)
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (by grind) _ hW
    intro z
    simp only [norm_mul,norm_star]
    calc
      _ ≤ 1*1*‖W (‖eisEmbedding z‖^2/K)‖ := by
        gcongr
        · simp_all
        simp_all
      _ = _ := by ring
  have he (z:ActualEisensteinCubic.O) : W (‖eisEmbedding z‖^2/K)*(‖∑b∈C,a b*r b z‖^2:ℝ)=
      ∑b∈C,∑c∈C,(star (a b)*a c)*((star (r b z)*r c z)*W (‖eisEmbedding z‖^2/K)) := by
    rw [Complex.sq_norm (∑b∈C,a b*r b z),Complex.normSq_eq_conj_mul_self]
    simp only [map_sum,map_mul,starRingEnd_apply]
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun b hb=>summable_sum (fun c hc=>(hs b c hb hc).mul_left _))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Summable.tsum_finsetSum (fun c hc=>(hs b c hb hc).mul_left _)]
  apply Finset.sum_congr rfl
  intro c hc
  exact tsum_mul_left

variable {ι : Type*} [DecidableEq ι]
  (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def varyingReopenedRow (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m f : ActualEisensteinCubic.O) (H : (ι→₀ℕ)→Finset ι→ℂ) (z : ActualEisensteinCubic.O) : ℂ :=
  ∑v∈Q,∑S∈pool.powerset,
    (β v*canonicalSourceCoefficient p hp hcop hg Ψ m f (H v) S)*
    (multiplicityRow (fun i=>Ideal.span {p i}) hg pool v z^3*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)

theorem varying_reopened_smoothed_expand
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀v∈Q,v.support⊆pool)
    (β : (ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m f : ActualEisensteinCubic.O) (H : (ι→₀ℕ)→Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑'z:ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/K)*(‖varyingReopenedRow p hp hcop hg pool Q β Ψ m f H z‖^2:ℝ))=
      ∑v₂∈Q,∑v₁∈Q,(star (β v₂)*β v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂ Ψ Ψ m m f (H v₂) (H v₁) W K := by
  let a : (ι→₀ℕ)×Finset ι→ℂ := fun b=>β b.1*canonicalSourceCoefficient p hp hcop hg Ψ m f (H b.1) b.2
  let r : (ι→₀ℕ)×Finset ι→ActualEisensteinCubic.O→ℂ := fun b z=>
    multiplicityRow (fun i=>Ideal.span {p i}) hg pool b.1 z^3*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg b.2 z
  have hr (b : (ι→₀ℕ)×Finset ι) (hb:b∈Q×ˢpool.powerset) (z:ActualEisensteinCubic.O) : ‖r b z‖≤1 := by
    dsimp [r]
    rw [norm_mul,norm_pow]
    calc
      _ ≤ 1 * ‖finiteSquarefreeRow (fun i => Ideal.span {p i}) hg b.2 z‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ (norm_nonneg _) (multiplicityRow_norm_le_one p hg pool b.1 z))
          (norm_nonneg _)
      _ ≤ 1 := by simpa using finiteSquarefreeRow_norm_le_one _ hg b.2 z
  have he:=bounded_row_square_expansion (Q×ˢpool.powerset) a r hr W K hK
  simp only [Finset.sum_product] at he
  change (∑'z:ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/K)*
    (‖varyingReopenedRow p hp hcop hg pool Q β Ψ m f H z‖^2:ℝ))=_ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro v₂ hv₂
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v₁ hv₁
  simp only [canonicalCubeCorrelation,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  have hB₁ : v₁.support⊆v₁.support∪v₂.support:=Finset.subset_union_left
  have hB₂ : v₂.support⊆v₁.support∪v₂.support:=Finset.subset_union_right
  have hr₁ (z:ActualEisensteinCubic.O) : multiplicityRow (fun i=>Ideal.span {p i}) hg pool v₁ z=
      multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₁ z := by
    rw [multiplicityRow_support p hg pool v₁ (by grind),multiplicityRow_support p hg _ v₁ hB₁]
  have hr₂ (z:ActualEisensteinCubic.O) : multiplicityRow (fun i=>Ideal.span {p i}) hg pool v₂ z=
      multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₂ z := by
    rw [multiplicityRow_support p hg pool v₂ (by grind),multiplicityRow_support p hg _ v₂ hB₂]
  simp only [a,r,canonicalCubeSourcePair,star_mul,hr₁,hr₂]
  grind

end
end SevenEighths.InverseMoment

end OAI
