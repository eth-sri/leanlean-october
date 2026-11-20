module

public import OAI.NumberTheory.DirichletL.Reflection.SourceCost

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

/-- Freeze the active and inactive choices, then aggregate the row energies. -/
lemma frozen_inactive_sum_energy {γ σ ρ : Type*} [Fintype γ] [Fintype σ] [DecidableEq σ]
    [Fintype ρ] (J F Q Q₀ : Ideal Eis) (H : σ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (r : ℂ) (scalar : γ → ρ → ℂ) (hscalar : ∀ g k, ‖scalar g k‖ ≤ 1)
    (source : γ → Finset (FreeReflection.pool J Q Q₀) → Finset σ → ρ → ℂ)
    (h : ∀ g A T, (∑ k, ‖source g A T k‖ ^ 2) ≤
      (∏ i : {i // i ∉ T}, 256*(columnDyadicLength (H i.val)+1:ℝ))^2 * E) :
    (∑ k, ‖r*∑ g,scalar g k*
      ∑ A,frozenInactiveWeight J F Q Q₀ A*∑ T,source g A T k‖^2) ≤
    ‖r‖^2*(Fintype.card (γ×(Finset (FreeReflection.pool J Q Q₀)×Finset σ)):ℝ)^2*
      (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2*E := by
  let cost i := 256*(columnDyadicLength (H i)+1:ℝ)
  let Labels := γ × (Finset (FreeReflection.pool J Q Q₀) × Finset σ)
  let f (b : Labels) (k : ρ) := (scalar b.1 k*frozenInactiveWeight J F Q Q₀ b.2.1)*source b.1 b.2.1 b.2.2 k
  have hf (b : Labels) : (∑ k, ‖f b k‖^2) ≤ (∏ i,cost i)^2 * E := by
    apply (bounded_row_multiplier_energy Finset.univ _ _ (fun k _ => ?_)).trans
    · apply (h b.1 b.2.1 b.2.2).trans
      apply mul_le_mul_of_nonneg_right _ hE
      apply pow_le_pow_left₀ (by positivity)
      exact subtype_product_le_full (fun i => i ∉ b.2.2) cost
        (fun i => by dsimp [cost]; linarith [Nat.cast_nonneg (α := ℝ) (columnDyadicLength (H i))])
    · rw [norm_mul]
      exact mul_le_one₀ (hscalar b.1 k) (norm_nonneg _) (frozenInactiveWeight_norm J F Q Q₀ b.2.1)
  have hfam := weighted_finite_row_energy_uniform Finset.univ Finset.univ (fun _ : Labels => (1:ℂ))
    f ((∏ i,cost i)^2 * E) (fun b _ => hf b)
  simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hfam
  have hid (k : ρ) : (∑ b : Labels,f b k) = ∑ g,scalar g k*
      ∑ A,frozenInactiveWeight J F Q Q₀ A*∑ T,source g A T k := by
    simp only [Labels,f,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  simp_rw [←hid]
  simp only [norm_mul,mul_pow,←Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left hfam (sq_nonneg _)).trans_eq (by dsimp [Labels,cost]; ring)

theorem original_source_cost_budget {χ : Type*} [Fintype χ]
    (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (H : σ→ℝ),
      Fintype.card σ≤rmax → (∀ i,1≤H i) →
    ∀ (J Q Q₀ : Ideal Eis),J≠0 → Q≠0 → ∀ (Z Lpool Lslot loss : ℝ),1<Z →
      (Ideal.absNorm (J*Q):ℝ)≤Z^Lpool → (∏ i,H i)≤Z^Lslot → ε*(Lpool+Lslot)≤loss →
      (Fintype.card (χ×(Finset (FreeReflection.pool J Q Q₀)×Finset σ)):ℝ)^2*
        (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤C*Z^loss := by
  obtain ⟨C,hC,hb⟩ := original_source_cost (χ:=χ) rmax ε hε
  refine ⟨C,hC,?_⟩
  intro σ _ H hcard hH J Q Q₀ hJ hQ Z Lpool Lslot loss hZ hpool hslot hloss
  have hz : 0<Z := lt_trans zero_lt_one hZ
  apply (hb H hcard hH J Q Q₀ hJ hQ).trans
  calc
    _ ≤ C*(Z^Lpool)^ε*(Z^Lslot)^ε := by
      have hp := Real.rpow_le_rpow (Nat.cast_nonneg (Ideal.absNorm (J*Q))) hpool hε.le
      have hs := Real.rpow_le_rpow (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i))) hslot hε.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hs
        (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i))) _) (by positivity)
    _ = C*Z^(ε*(Lpool+Lslot)) := by
      rw [←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,mul_assoc,←Real.rpow_add hz]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hloss) hC.le
end
end SevenEighths.InverseReflectedPhase

end OAI
