module
public import OAI.NumberTheory.DirichletL.Reflection.SourceCost
public import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

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
/-- Sum the frozen components after enlarging each inactive slot budget to the full budget. -/
lemma frozen_source_energy {γ α σ κ : Type*} [Fintype γ] [Fintype α] [Fintype σ]
    [DecidableEq σ] [Fintype κ] (s : ℂ) (r : γ → κ → ℂ) (w : α → ℂ)
    (f : γ → α → Finset σ → κ → ℂ) (H : σ → ℝ) {E B : ℝ} (hE : 0≤E)
    (hr : ∀ g k, ‖r g k‖≤1) (hw : ∀ a, ‖w a‖≤1)
    (hf : ∀ g a t, (∑ k, ‖f g a t k‖^2)≤
      (∏ i : {i // i∉t}, 256*(columnDyadicLength (H i.val)+1:ℝ))^2*E)
    (hB : (Fintype.card (γ×(α×Finset σ)):ℝ)^2*
      (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤B) :
    (∑ k, ‖s*∑ g, r g k*∑ a,w a*∑ t, f g a t k‖^2)≤(‖s‖^2+1)*B*E := by
  let L := γ×(α×Finset σ)
  let U : σ → ℝ := fun i => 256*(columnDyadicLength (H i)+1:ℝ)
  have hU (i : σ) : 1≤U i := by
    have : (0:ℝ)≤columnDyadicLength (H i) := Nat.cast_nonneg _
    dsimp [U]
    linarith
  let F := fun (b : L) k => (r b.1 k*w b.2.1)*f b.1 b.2.1 b.2.2 k
  have hF (b : L) : (∑ k, ‖F b k‖^2)≤(∏ i,U i)^2*E := by
    have hw' (k : κ) : ‖r b.1 k*w b.2.1‖≤1 := by
      simpa [norm_mul] using mul_le_mul (hr b.1 k) (hw b.2.1) (norm_nonneg _) zero_le_one
    apply (bounded_row_multiplier_energy Finset.univ _ _ (fun k _ => hw' k)).trans
    apply (hf b.1 b.2.1 b.2.2).trans
    apply mul_le_mul_of_nonneg_right _ hE
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => zero_le_one.trans (hU i.val))
      (subtype_product_le_full (fun i => i∉b.2.2) U hU) _
  have h := weighted_finite_row_energy_uniform (Finset.univ : Finset L) Finset.univ
    (fun _ => (1:ℂ)) F _ (fun b _ => hF b)
  simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  have hid (k : κ) : (∑ b,F b k)=∑ g,r g k*∑ a,w a*∑ t,f g a t k := by
    simp only [L,F,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  simp_rw [←hid, norm_mul, mul_pow, ←Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans
  calc
    _ = ‖s‖^2*((Fintype.card L:ℝ)^2*(∏ i,U i)^2)*E := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul (le_add_of_nonneg_right zero_le_one) hB (by positivity) (by positivity)) hE

end
end SevenEighths.InverseReflectedPhase

end OAI
