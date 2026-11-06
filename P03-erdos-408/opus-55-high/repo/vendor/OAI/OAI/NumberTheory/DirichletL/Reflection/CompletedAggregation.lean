module

public import OAI.NumberTheory.DirichletL.Reflection.PowerfulBudget
public import OAI.NumberTheory.DirichletL.Reflection.RowReindex

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open CompletedGauss
noncomputable section

theorem completed_representative_aggregation (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (Z : ℝ),2≤Z → ∀ (parents : Finset (Ideal ActualEisensteinCubic.O)) (Q : Ideal ActualEisensteinCubic.O),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^L) → Q≠0 → (Ideal.absNorm Q:ℝ)≤Z^L →
      ∀ (E : ℝ) (f : Ideal ActualEisensteinCubic.O→ℝ),0≤E →
      (∀ J∈parents,(∑ I∈representativeRowFiber parents J Q,f I)≤
        E*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ))) →
      (∑ I∈parents,f I)≤C*Z^ε*E := by
  obtain ⟨C,hC,hbudget⟩ := InverseReflectedPhasePowerfulBudget.row_mask_powerful_budget L ε hL hε
  refine ⟨C,hC,?_⟩
  intro Z hZ parents Q hparents hQ hQN E f hE hf
  have hb := hbudget Z hZ parents Q hparents hQ hQN
  simp only [neg_div] at hb
  have hblocks (A T : Ideal ActualEisensteinCubic.O) : (∑ I∈completedRowFiber parents Q A T,f I)≤
      E*(Ideal.absNorm A:ℝ)^(-(1/2:ℝ)) := by
    by_cases he : (completedRowFiber parents Q A T).Nonempty
    · obtain ⟨J,hJ⟩ := he
      obtain ⟨hJS,hJA,hJT⟩ := Finset.mem_filter.mp hJ
      have hh := hf J hJS
      simpa only [representativeRowFiber,hJA,hJT] using hh
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
      positivity
  rw [←sum_completedRowFibers parents Q f]
  calc
    _ ≤ ∑ A∈parents.image rowPowerfulPart,∑ _T∈parents.image (fun I => rowMaskPart I Q),
          E*(Ideal.absNorm A:ℝ)^(-(1/2:ℝ)) :=
      Finset.sum_le_sum (fun A _ => Finset.sum_le_sum (by grind))
    _ = (((parents.image (fun I => rowMaskPart I Q)).card:ℝ)*
          (∑ A∈parents.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-(1/2:ℝ))))*E := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [Finset.mul_sum,Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb hE
end
end SevenEighths.InverseReflectedPhase

end OAI
