module

public import OAI.NumberTheory.DirichletL.Reflection.SlotMass

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open CanonicalQuadraticSieve
noncomputable section

lemma subtype_product_le_full {σ : Type*} [Fintype σ] (p : σ→Prop) [DecidablePred p]
    (H : σ→ℝ) (hH : ∀ i,1≤H i) :
    (∏ i : {i // p i},H i.val)≤∏ i,H i := by
  rw [←Finset.prod_subtype (Finset.univ.filter p) (by simp) H]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (by simp)
    (by grind) (by grind)

theorem harmonic_product_small_power (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (H : σ→ℝ),
      Fintype.card σ≤rmax → (∀ i,1≤H i) →
      (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤C*(∏ i,H i)^ε := by
  let D := max 1 (256*(2+1/((ε/2)*Real.log 2)))
  have hD : 1≤D := le_max_left _ _
  refine ⟨D^(2*rmax),by positivity,?_⟩
  intro σ _ H hcard hH
  have hp : 0<∏ i,H i := Finset.prod_pos (by grind)
  have he (i : σ) : 256*(columnDyadicLength (H i)+1:ℝ)≤D*(H i)^(ε/2) := by
    apply (mul_le_mul_of_nonneg_left (columnDyadicLength_small_power (ε/2) (by positivity) (H i) (hH i)) (by positivity)).trans
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (by grind) (Real.rpow_nonneg (by grind) _)
  calc
    _ ≤ (∏ i,D*(H i)^(ε/2))^2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact Finset.prod_le_prod₀ (by grind) (by grind)
    _ = D^(2*Fintype.card σ)*(∏ i,H i)^ε := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        Real.finsetProd_rpow Finset.univ H (by grind),mul_pow,←pow_mul,
        ←Real.rpow_mul_natCast hp.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (by omega)) (by positivity)

end
end SevenEighths.InverseReflectedPhase

end OAI
