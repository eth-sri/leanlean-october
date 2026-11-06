module

public import OAI.NumberTheory.DirichletL.Descent.SecondTailCost
public import OAI.NumberTheory.DirichletL.Descent.ChildCutoff

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)

local notation "O" => ActualEisensteinCubic.O

theorem full_second_supported_tail  order  :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H lengthScale : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ lengthScale →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
        (128*lengthScale)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+lengthScale^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_uniform_secondSourceTail_bound order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Hcol W B Y H lengthScale hB hY hH hL hcol hsupp K hK
  exact (htail p hp hg hinj hc F Ψ m c d Hcol W Y H hY hH K hK).trans
    (secondSourceTailCost_bounded_test p hp hg hinj F Ψ hΨ m c d Hcol B Y H lengthScale
      (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) order hB hY hH (by positivity) hL hcol hsupp)


end SevenEighths.InverseMoment

end OAI
