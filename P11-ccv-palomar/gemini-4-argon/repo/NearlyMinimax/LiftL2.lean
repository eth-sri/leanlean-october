module
public import Mathlib
public import RoughRegime.PolynomialDerivatives
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000
section
namespace RoughRegime.UpperCovariance
open MeasureTheory ProbabilityTheory
def kernelSum  {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  ∑ e : Fin r ↪ Fin n, H (fun i => X (e i) ω)
def kernelStatistic  {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  (↑r.factorial * (n.descFactorial r : ℝ))⁻¹ * kernelSum H X ω
def centeredKernelExpansion  {n p R : ℕ} (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  c + ∑ r : Fin R, kernelStatistic (H r) X ω
def centeredDerivativeLift  {n p : ℕ} (R : ℕ)
    (F : MvPolynomial (Fin p) ℝ) (m : Fin p → ℝ)
    (Y : Fin n → Ω → Fin p → ℝ) : Ω → ℝ :=
  centeredKernelExpansion (MvPolynomial.eval m F)
    (fun r : Fin R => iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m) Y
end RoughRegime.UpperCovariance
namespace RoughRegime.LiftTranslation
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} {n p q r R : ℕ}
lemma sum_embedding_restriction  [Fintype A] [Fintype B]
    (n : ℕ) (f : (A ↪ Fin n) → ℝ) :
    (∑ e : A ⊕ B ↪ Fin n, f (Function.Embedding.inl.trans e)) =
      ((n - Fintype.card A).descFactorial (Fintype.card B) : ℝ) *
        ∑ e : A ↪ Fin n, f e := by
  let E := Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted (α := A) (β := B) (γ := Fin n)
  have hfirst (e : A ⊕ B ↪ Fin n) : (E e).1 = Function.Embedding.inl.trans e := rfl
  calc
    _ = ∑ e : A ⊕ B ↪ Fin n, f (E e).1 := by simp only [hfirst]
    _ = ∑ u : Σ e : A ↪ Fin n, B ↪ ↥(Set.range e)ᶜ, f u.1 := E.sum_comp (fun u : Σ e : A ↪ Fin n, B ↪ ↥(Set.range e)ᶜ => f u.1)
    _ = ∑ e : A ↪ Fin n, ((n - Fintype.card A).descFactorial (Fintype.card B) : ℝ) * f e := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro e _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_embedding_eq]
      have hcard : Fintype.card ↥(Set.range e)ᶜ = n - Fintype.card A := by
        change Fintype.card {j : Fin n // ¬j ∈ Set.range e} = _
        rw [Fintype.card_subtype_compl, ← Fintype.card_congr e.toEquivRange, Fintype.card_fin]
      rw [hcard]
    _ = _ := (Finset.mul_sum _ _ _).symm
lemma sum_embedding_subtype_restriction  [Fintype A]
    (n : ℕ) (S : Finset A) (f : (↥S ↪ Fin n) → ℝ) :
    (∑ e : A ↪ Fin n, f ((Function.Embedding.subtype (fun i => i ∈ S)).trans e)) =
      ((n - S.card).descFactorial (Fintype.card A - S.card) : ℝ) *
        ∑ e : ↥S ↪ Fin n, f e := by
  classical
  let C := (S : Set A)ᶜ
  let E : (↥S ⊕ C ↪ Fin n) ≃ (A ↪ Fin n) :=
    Equiv.embeddingCongr (Equiv.Set.sumCompl (S : Set A)) (Equiv.refl (Fin n))
  calc
    _ = ∑ e : ↥S ⊕ C ↪ Fin n,
        f ((Function.Embedding.subtype (fun i => i ∈ S)).trans (E e)) :=
      (E.sum_comp (fun e : A ↪ Fin n =>
        f ((Function.Embedding.subtype (fun i => i ∈ S)).trans e))).symm
    _ = ∑ e : ↥S ⊕ C ↪ Fin n, f (Function.Embedding.inl.trans e) := by
      apply Finset.sum_congr rfl
      intro e _
      congr 1
      apply Function.Embedding.ext
      intro i
      change e ((Equiv.Set.sumCompl (S : Set A)).symm (i : A)) = e (Sum.inl i)
      rw [Equiv.Set.sumCompl_symm_apply_of_mem (show (i : A) ∈ (S : Set A) from i.property)]
      rfl
    _ = ((n - Fintype.card ↥S).descFactorial (Fintype.card C) : ℝ) *
        ∑ e : ↥S ↪ Fin n, f e := sum_embedding_restriction n f
    _ = _ := by
      have hcard : Fintype.card C = Fintype.card A - S.card := by
        change Fintype.card {i : A // ¬i ∈ S} = _
        rw [Fintype.card_subtype_compl]
        simp
      rw [hcard]
      simp
lemma range_embedding_of_subset_equiv {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset B) (a : A ≃ ↥S) :
    Set.range (a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))) = S := by
  ext j
  constructor
  · rintro ⟨i, rfl⟩
    exact (a i).property
  · intro hj
    obtain ⟨i, hi⟩ := a.surjective ⟨j, hj⟩
    exact ⟨i, congrArg Subtype.val hi⟩
lemma sum_embeddings_by_range  [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (f : (A ↪ B) → ℝ) :
    (∑ e : A ↪ B, f e) =
      ∑ S : Finset B, ∑ a : A ≃ ↥S,
        f (a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))) := by
  let g : (Σ S : Finset B, A ≃ ↥S) → (A ↪ B) :=
    fun u => u.2.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ u.1))
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨S, a⟩ ⟨T, b⟩ h
      have : S = T := by
        apply Finset.coe_injective
        rw [← range_embedding_of_subset_equiv S a, ← range_embedding_of_subset_equiv T b]
        exact congrArg (fun e : A ↪ B => Set.range (e : A → B)) h
      subst T
      have : a = b := by
        apply Equiv.ext
        intro i
        apply Subtype.ext
        exact congrArg (fun e : A ↪ B => e i) h
      subst b
      rfl
    · intro e
      let S := Finset.univ.map e
      have hS : Set.range e = (S : Set B) := by ext j; simp [S]
      let a : A ≃ ↥S := e.toEquivRange.trans (Set.equivOfEq hS)
      refine ⟨⟨S, a⟩, ?_⟩
      apply Function.Embedding.ext
      intro i
      rfl
  calc
    _ = ∑ u : Σ S : Finset B, A ≃ ↥S, f (g u) :=
      ((Equiv.ofBijective g hg).sum_comp f).symm
    _ = _ := by rw [Fintype.sum_sigma]
lemma sum_samples_subset_equiv  (S : Finset (Fin p))
    (a : Fin r ≃ ↥S) (Y : Fin n → Fin p → ℝ) :
    (∑ e : Fin r ↪ Fin n, ∏ i : Fin r, Y (e i) (a i)) =
      ∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) i := by
  let E : (Fin r ↪ Fin n) ≃ (↥S ↪ Fin n) :=
    Equiv.embeddingCongr a (Equiv.refl (Fin n))
  calc
    _ = ∑ e : Fin r ↪ Fin n, ∏ i : ↥S, Y ((E e) i) i := by
      apply Finset.sum_congr rfl
      intro e _
      rw [← a.prod_comp]
      apply Finset.prod_congr rfl
      intro i _
      simp [E, Equiv.embeddingCongr, Function.Embedding.congr_apply]
    _ = _ := E.sum_comp (fun e => ∏ i : ↥S, Y (e i) i)
lemma monomial_replacement_by_subset  (σ : Fin q → Fin p)
    (S : Finset (Fin q)) (a : Fin r ≃ ↥S) (m : Fin p → ℝ)
    (v : Fin r → Fin p → ℝ) :
    (∏ j : Fin q, if h : j ∈ Set.range
        (a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))) then
      v ((a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))).toEquivRange.symm ⟨j, h⟩)
        (σ j) else m (σ j)) =
      (∏ i : Fin r, v i (σ (a i))) * ∏ j ∈ Sᶜ, m (σ j) := by
  let b : Fin r ↪ Fin q := a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))
  let f : Fin q → ℝ := fun j => if h : j ∈ Set.range b then v (b.toEquivRange.symm ⟨j, h⟩) (σ j)
    else m (σ j)
  change (∏ j : Fin q, f j) = _
  rw [← Finset.prod_mul_prod_compl S f]
  congr 1
  · calc
      _ = ∏ j : ↥S, f j := (Finset.prod_coe_sort S f).symm
      _ = ∏ i : Fin r, f (a i) := (a.prod_comp (fun j => f j)).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        have hi : (a i : Fin q) ∈ Set.range b := ⟨i, rfl⟩
        simp only [f, dite_eq_left hi]
        change v (b.toEquivRange.symm ⟨b i, _⟩) (σ (a i)) = _
        simp
  · apply Finset.prod_congr rfl
    intro j hj
    exact dite_eq_right (by rw [range_embedding_of_subset_equiv S a]; simpa using Finset.mem_compl.mp hj)
lemma monomial_derivative_sample_sum  (σ m) (Y : Fin n → Fin p → ℝ) :
    (∑ e : Fin r ↪ Fin n,
      iteratedFDeriv ℝ r (RoughRegime.PolynomialDerivatives.monomial σ) m (fun i => Y (e i))) =
      ∑ S : Finset (Fin q), (Fintype.card (Fin r ≃ ↥S) : ℝ) *
        ((∏ j ∈ Sᶜ, m (σ j)) * (∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) (σ i))) := by
  simp_rw [RoughRegime.PolynomialDerivatives.monomial_iteratedFDeriv]
  rw [Finset.sum_comm, sum_embeddings_by_range]
  apply Finset.sum_congr rfl
  intro S _
  have hsamp (a : Fin r ≃ ↥S) :
      (∑ e : Fin r ↪ Fin n,
        ∏ j : Fin q, if h : j ∈ Set.range
            (a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))) then
          Y (e ((a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))).toEquivRange.symm
            ⟨j, h⟩)) (σ j) else m (σ j)) =
        (∏ j ∈ Sᶜ, m (σ j)) * (∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) (σ i)) := by
    calc
      _ = ∑ e : Fin r ↪ Fin n, (∏ i : Fin r, Y (e i) (σ (a i))) * (∏ j ∈ Sᶜ, m (σ j)) := by
        apply Finset.sum_congr rfl
        intro e _
        exact monomial_replacement_by_subset σ S a m (fun i => Y (e i))
      _ = _ := by
        rw [← Finset.sum_mul, sum_samples_subset_equiv S a (fun j i => Y j (σ i))]
        exact mul_comm _ _
  simp_rw [hsamp]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
def derivativeLiftAt   (R : ℕ) (f : (Fin p → ℝ) → ℝ)
    (m : Fin p → ℝ) (Y : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  ∑ r ∈ Finset.range (R + 1),
    ((↑r.factorial * (n.descFactorial r : ℝ))⁻¹ * ∑ e : Fin r ↪ Fin n,
      iteratedFDeriv ℝ r f m (fun i => Y (e i) ω))
lemma derivativeLiftAt_monomial_stable  
    (σ : Fin q → Fin p) (Y : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hqR : q ≤ R) (ω : Ω) :
    derivativeLiftAt R (RoughRegime.PolynomialDerivatives.monomial σ) m Y ω =
      derivativeLiftAt q (RoughRegime.PolynomialDerivatives.monomial σ) m Y ω := by
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hqR 1))
  intro r _ hr
  have hzero (e : Fin r ↪ Fin n) :=
    RoughRegime.PolynomialDerivatives.monomial_iteratedFDeriv_above_degree σ m
      (fun i => Y (e i) ω) (by have : ¬r < q + 1 := fun h => hr (Finset.mem_range.mpr h); omega)
  simp only [hzero, Finset.sum_const_zero, mul_zero]
theorem polynomialLift_eq_derivativeLiftAt  
    (F : MvPolynomial (Fin p) ℝ) (Y : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n) (ω : Ω) :
    RoughRegime.Upper.polynomialLift F (fun j ω => Y j ω + m) ω =
      derivativeLiftAt R (fun x => MvPolynomial.eval x F) m Y ω := by
  have h_derivativeLiftAt_polynomial_monomial_sum : derivativeLiftAt R (fun x => MvPolynomial.eval x F) m Y ω =
      ∑ α ∈ F.support, F.coeff α * derivativeLiftAt R
        (RoughRegime.PolynomialDerivatives.monomial (RoughRegime.Upper.exponentCoordinates α)) m Y ω := by
    unfold derivativeLiftAt
    have hstep (r : ℕ) :
        (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ * ∑ e : Fin r ↪ Fin n,
          iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m (fun i => Y (e i) ω)) =
        ∑ α ∈ F.support, F.coeff α *
          ((((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ * ∑ e : Fin r ↪ Fin n,
            iteratedFDeriv ℝ r (RoughRegime.PolynomialDerivatives.monomial
              (RoughRegime.Upper.exponentCoordinates α)) m (fun i => Y (e i) ω))) := by
      simp_rw [RoughRegime.PolynomialDerivatives.polynomial_iteratedFDeriv_monomial_sum]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α _
      ring
    simp_rw [hstep]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    exact (Finset.mul_sum _ _ _).symm
  rw [h_derivativeLiftAt_polynomial_monomial_sum]
  apply Finset.sum_congr rfl
  intro α hα
  congr 1
  have hqR : Fintype.card (RoughRegime.Upper.ExponentSlots α) ≤ R := by
    rw [RoughRegime.Upper.exponentSlots_card]
    exact (MvPolynomial.le_totalDegree hα).trans hdeg
  rw [derivativeLiftAt_monomial_stable _ Y m hqR ω]
  have h_monomialLift_eq_derivativeLiftAt {q : ℕ} (σ : Fin q → Fin p) (hqn : q ≤ n) : RoughRegime.Upper.monomialLift σ (fun j ω => Y j ω + m) ω =
      derivativeLiftAt q (RoughRegime.PolynomialDerivatives.monomial σ) m Y ω := by
    have h_monomialLift_centering : RoughRegime.Upper.monomialLift σ (fun j ω => Y j ω + m) ω =
        ∑ S : Finset (Fin q), (∏ i ∈ Sᶜ, m (σ i)) *
          ((n.descFactorial S.card : ℝ)⁻¹ *
            ∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) ω (σ i)) := by
      classical
      unfold RoughRegime.Upper.monomialLift
      simp only [Pi.add_apply]
      simp_rw [Fintype.prod_add (fun i => Y _ ω (σ i)) (fun i => m (σ i))]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      have hprod (e : Fin q ↪ Fin n) :
          (∏ i ∈ S, Y (e i) ω (σ i)) =
            ∏ i : ↥S, Y (e i) ω (σ i) := by
        exact (Finset.prod_coe_sort S (fun i => Y (e i) ω (σ i))).symm
      simp_rw [hprod]
      rw [← Finset.sum_mul]
      have h : (n.descFactorial q : ℝ)⁻¹ * (∑ e : Fin q ↪ Fin n, ∏ i : ↥S, Y (e i) ω (σ i)) =
          (n.descFactorial S.card : ℝ)⁻¹ * (∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) ω (σ i)) :=
        by
          have h_normalized_embedding_subtype_restriction {A} [Fintype A] (hn : Fintype.card A ≤ n) (S : Finset A) (f : (↥S ↪ Fin n) → ℝ) : (n.descFactorial (Fintype.card A) : ℝ)⁻¹ *
                (∑ e : A ↪ Fin n, f ((Function.Embedding.subtype (fun i => i ∈ S)).trans e)) =
              (n.descFactorial S.card : ℝ)⁻¹ * ∑ e : ↥S ↪ Fin n, f e := by
            rw [sum_embedding_subtype_restriction]
            have : (n.descFactorial (Fintype.card A) : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hn))
            have : (n.descFactorial S.card : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr (S.card_le_univ.trans hn)))
            have hcoeff : (n.descFactorial (Fintype.card A) : ℝ)⁻¹ *
                ((n - S.card).descFactorial (Fintype.card A - S.card) : ℝ) =
                  (n.descFactorial S.card : ℝ)⁻¹ := by
              field_simp
              exact (by exact_mod_cast (Nat.descFactorial_mul_descFactorial S.card_le_univ))
            rw [← mul_assoc, hcoeff]
          simpa using (h_normalized_embedding_subtype_restriction (by simpa using hqn) S (fun e : ↥S ↪ Fin n => ∏ i : ↥S, Y (e i) ω (σ i)))
      linear_combination (∏ i ∈ Sᶜ, m (σ i)) * h
    rw [h_monomialLift_centering]
    have h_normalized_monomial_derivative_sample_sum {n : ℕ} {r : ℕ} (Y : Fin n → Fin p → ℝ) (hrn : r ≤ n) : ((↑r.factorial * (n.descFactorial r : ℝ))⁻¹ * ∑ e : Fin r ↪ Fin n,
        iteratedFDeriv ℝ r (RoughRegime.PolynomialDerivatives.monomial σ) m (fun i => Y (e i))) =
        ∑ S : Finset (Fin q), if S.card = r then
          (∏ j ∈ Sᶜ, m (σ j)) *
            ((n.descFactorial S.card : ℝ)⁻¹ * ∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) (σ i))
          else 0 := by
      rw [monomial_derivative_sample_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      have h_card_equiv_fin_subset (S : Finset (Fin q)) : Fintype.card (Fin r ≃ ↥S) = if S.card = r then r.factorial else 0 := by
        split_ifs with h
        · let a : Fin r ≃ ↥S := Fintype.equivOfCardEq (by simpa using h.symm)
          rw [Fintype.card_equiv a]
          simp
        · have : IsEmpty (Fin r ≃ ↥S) := ⟨fun a => h (by simpa using (Fintype.card_congr a).symm)⟩
          exact Fintype.card_eq_zero
      rw [h_card_equiv_fin_subset]
      split_ifs with h
      · rw [h]
        field_simp
      · simp
    have hexp (r : ℕ) (hr : r ∈ Finset.range (q + 1)) :=
      h_normalized_monomial_derivative_sample_sum (fun j => Y j ω) ((Nat.le_of_lt_succ (Finset.mem_range.mp hr)).trans hqn)
    calc
      _ = ∑ r ∈ Finset.range (q + 1), ∑ S : Finset (Fin q),
          if S.card = r then (∏ j ∈ Sᶜ, m (σ j)) *
            ((n.descFactorial S.card : ℝ)⁻¹ * ∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) ω (σ i)) else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro S _
        have hS : S.card ∈ Finset.range (q + 1) := by
          apply Finset.mem_range.mpr
          have hcard := S.card_le_univ
          simp only [Fintype.card_fin] at hcard
          omega
        simp [hS]
      _ = _ := Finset.sum_congr rfl (fun r hr => (hexp r hr).symm)
  exact h_monomialLift_eq_derivativeLiftAt _ (hqR.trans hRn)
theorem polynomialLift_eq_centeredDerivativeLift  
    (F : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n) :
    RoughRegime.Upper.polynomialLift F X =
      RoughRegime.UpperCovariance.centeredDerivativeLift R F m (fun j ω => X j ω - m) := by
  funext ω
  have hX : (fun j ω => (X j ω - m) + m) = X := by
    funext j ω
    exact sub_add_cancel (X j ω) m
  have h_derivativeLiftAt_eq_centeredDerivativeLift (Y : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ) (ω : Ω) : derivativeLiftAt R (fun x => MvPolynomial.eval x F) m Y ω =
      RoughRegime.UpperCovariance.centeredDerivativeLift R F m Y ω := by
    classical
    unfold derivativeLiftAt RoughRegime.UpperCovariance.centeredDerivativeLift
      RoughRegime.UpperCovariance.centeredKernelExpansion
      RoughRegime.UpperCovariance.kernelStatistic RoughRegime.UpperCovariance.kernelSum
    rw [Finset.sum_range_succ']
    simp only [iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.descFactorial_zero, Nat.cast_one,
      one_mul, inv_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_embedding_eq,
      Fintype.card_fin, Nat.cast_one, one_mul]
    rw [add_comm]
    congr 1
    exact (Fin.sum_univ_eq_sum_range
      (fun r => (((r + 1).factorial : ℝ) * (n.descFactorial (r + 1) : ℝ))⁻¹ *
        ∑ e : Fin (r + 1) ↪ Fin n,
          iteratedFDeriv ℝ (r + 1) (fun x => MvPolynomial.eval x F) m (fun i => Y (e i) ω)) R).symm
  rw [← h_derivativeLiftAt_eq_centeredDerivativeLift, ← polynomialLift_eq_derivativeLiftAt F (fun j ω => X j ω - m) m hdeg hRn ω, hX]
end RoughRegime.LiftTranslation
end
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace NearlyMinimax.LiftL2
set_option backward.isDefEq.respectTransparency false
variable {n p r t R : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
theorem independent_finset_product_integrable [IsProbabilityMeasure μ]
    {ι : Type*} [DecidableEq ι] {Y : ι → Ω → ℝ}
    (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (hint : ∀ i, Integrable (Y i) μ) (s ) :
    Integrable (fun ω => ∏ i ∈ s, Y i ω) μ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hpfun : (∏ j ∈ s, Y j) = (fun ω => ∏ j ∈ s, Y j ω) := by
      funext ω
      simp
    have hprod := (hind.indepFun_finsetProd_of_notMem hmeas hi).symm.integrable_mul
      (hint i) (by rw [hpfun]; exact ih)
    rw [hpfun] at hprod
    have hp : (Y i * (fun ω => ∏ j ∈ s, Y j ω)) =
        (fun ω => Y i ω * ∏ j ∈ s, Y j ω) := by funext ω; rfl
    rw [hp] at hprod
    simpa only [Finset.prod_insert hi] using hprod
theorem independent_finset_product_memLp_two [IsProbabilityMeasure μ]
    {ι : Type*} [DecidableEq ι] {Y : ι → Ω → ℝ}
    (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (hL2 : ∀ i, MemLp (Y i) 2 μ) (s ) :
    MemLp (fun ω => ∏ i ∈ s, Y i ω) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (Finset.measurable_prod s (fun i _ => hmeas i)).aestronglyMeasurable).2
  have hsqind : iIndepFun (fun i ω => Y i ω ^ 2) μ :=
    hind.comp (fun _ => fun y => y ^ 2) (fun _ => measurable_id.pow_const 2)
  have hsq := independent_finset_product_integrable hsqind
    (fun i => (hmeas i).pow_const 2) (fun i => (hL2 i).integrable_sq) s
  simpa only [Finset.prod_pow] using hsq
theorem coordinate_monomial_memLp_two [IsProbabilityMeasure μ]
     (e : Fin r ↪ Fin n) (σ : Fin r → Fin p)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (fun ω => ∏ i, X (e i) ω (σ i)) 2 μ := by
  have hcoord  :=
    (hind.precomp e.injective).comp (fun i => fun v : Fin p → ℝ => v (σ i))
      (fun i => measurable_pi_apply (σ i))
  exact independent_finset_product_memLp_two hcoord
    (fun i => (measurable_pi_apply (σ i)).comp (hmeas (e i)))
    (fun i => hL2 (e i) (σ i)) Finset.univ
theorem coordinate_product_integral_eq_zero [IsProbabilityMeasure μ]
     [Fintype A] 
    (s : A → Fin n) (σ : A → Fin p) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0)
    (k : A) (hk : ∀ i, s i = s k → i = k) :
    (∫ ω, ∏ i, X (s i) ω (σ i) ∂μ) = 0 := by
  have h_coordinate_product_integral_fiberwise : (∫ ω, ∏ i, X (s i) ω (σ i) ∂μ) =
      ∏ j : Fin n, ∫ ω, ∏ i : A with s i = j, X j ω (σ i) ∂μ := by
    let F : Fin n → (Fin p → ℝ) → ℝ := fun j v => ∏ i : A with s i = j, v (σ i)
    have hF : ∀ j, Measurable (F j) := fun j =>
      Finset.measurable_prod _ (fun i _ => measurable_pi_apply (σ i))
    have hfind : iIndepFun (fun j ω => F j (X j ω)) μ := hind.comp F hF
    have hfun : (fun ω => ∏ i, X (s i) ω (σ i)) =
        (fun ω => ∏ j, F j (X j ω)) := by
      funext ω
      rw [← Finset.prod_fiberwise (Finset.univ : Finset A) s
        (fun i => X (s i) ω (σ i))]
      apply Finset.prod_congr rfl
      intro j _
      apply Finset.prod_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    rw [hfun]
    exact hfind.integral_fun_prod_eq_prod_integral
      (fun j => ((hF j).comp (hmeas j)).aestronglyMeasurable)
  rw [h_coordinate_product_integral_fiberwise]
  apply Finset.prod_eq_zero (Finset.mem_univ (s k))
  have hfilter : (Finset.univ.filter (fun i : A => s i = s k)) = {k} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hk i, fun h => by rw [h]⟩
  rw [hfilter]
  simpa using hmean (s k) (σ k)
theorem multilinear_coordinate_expansion 
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (v ) :
    H v = ∑ σ : Fin r → Fin p,
      H (fun i => Pi.single (σ i) 1) * ∏ i, v i (σ i) := by
  calc
    H v = H (fun i => ∑ a : Fin p, v i a • (Pi.single a 1 : Fin p → ℝ)) := congrArg H (by funext i a; simp [Pi.single_apply])
    _ = ∑ σ : Fin r → Fin p, H (fun i => v i (σ i) • (Pi.single (σ i) 1 : Fin p → ℝ)) := H.map_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [H.map_smul_univ]
      simp only [smul_eq_mul]
      exact mul_comm _ _
theorem multilinear_kernel_memLp_two [IsProbabilityMeasure μ]
     (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (fun ω => H (fun i => X (e i) ω)) 2 μ := by
  have hexp : (fun ω => H (fun i => X (e i) ω)) =
      fun ω => ∑ σ : Fin r → Fin p,
        H (fun i => Pi.single (σ i) 1) * ∏ i, X (e i) ω (σ i) := by
    funext ω
    exact multilinear_coordinate_expansion H _
  rw [hexp]
  exact memLp_finsetSum Finset.univ (fun σ _ =>
    (coordinate_monomial_memLp_two e σ X hind hmeas hL2).const_mul _)
theorem multilinear_kernel_pair_integral_eq_zero_left [IsProbabilityMeasure μ]
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : MultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0)
    (k : Fin r) (hk : e k ∉ Set.range f) :
    (∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ) = 0 := by
  have h_coordinate_monomial_pair_integrable (σ : Fin r → Fin p) (τ : Fin t → Fin p) (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j)) (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) : Integrable (fun ω => (∏ i, X (e i) ω (σ i)) *
      (∏ i, X (f i) ω (τ i))) μ := by
    exact ((coordinate_monomial_memLp_two e σ X hind hmeas hL2).integrable_mul
        (coordinate_monomial_memLp_two f τ X hind hmeas hL2)).congr
      (Filter.Eventually.of_forall fun ω => rfl)
  have h_multilinear_pair_coordinate_expansion (v : Fin n → Fin p → ℝ) : H (fun i => v (e i)) * G (fun i => v (f i)) =
      ∑ σ : Fin r → Fin p, ∑ τ : Fin t → Fin p,
        (H (fun i => Pi.single (σ i) 1) * G (fun i => Pi.single (τ i) 1)) *
        ((∏ i, v (e i) (σ i)) * (∏ i, v (f i) (τ i))) := by
    rw [multilinear_coordinate_expansion H, multilinear_coordinate_expansion G,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro τ _
    ring
  have hexp (ω : Ω) := h_multilinear_pair_coordinate_expansion (fun j => X j ω)
  simp_rw [hexp]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro σ _
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro τ _
      have h_coordinate_monomial_pair_integral_eq_zero : (∫ ω, (∏ i, X (e i) ω (σ i)) * (∏ i, X (f i) ω (τ i)) ∂μ) = 0 := by
        have h := coordinate_product_integral_eq_zero (Sum.elim e f) (Sum.elim σ τ)
          X hind hmeas hmean (Sum.inl k) (by
            intro i hi
            cases i with
            | inl i => exact congrArg Sum.inl (e.injective hi)
            | inr i => exact (hk ⟨i, hi⟩).elim)
        simpa [Fintype.prod_sum_type] using h
      rw [integral_const_mul,
        h_coordinate_monomial_pair_integral_eq_zero,
        mul_zero]
    · intro τ _
      exact (h_coordinate_monomial_pair_integrable σ τ X hind hmeas hL2).const_mul _
  · intro σ _
    exact integrable_finsetSum _ fun τ _ =>
      (h_coordinate_monomial_pair_integrable σ τ X hind hmeas hL2).const_mul _
theorem multilinear_kernel_integral_eq_zero [IsProbabilityMeasure μ]
     (hr : 0 < r)
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    (∫ ω, H (fun i => X (e i) ω) ∂μ) = 0 := by
  have hexp (ω : Ω) := multilinear_coordinate_expansion H (fun i => X (e i) ω)
  simp_rw [hexp]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro σ _
    rw [integral_const_mul,
      coordinate_product_integral_eq_zero e σ X hind hmeas hmean ⟨0, hr⟩
        (fun i hi => e.injective hi), mul_zero]
  · intro σ _
    exact ((coordinate_monomial_memLp_two e σ X hind hmeas hL2).integrable
      (by norm_num)).const_mul _
def kernelSum 
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) : Ω → ℝ :=
  fun ω => ∑ e : Fin r ↪ Fin n, H (fun i => X (e i) ω)
theorem kernelSum_memLp_two [IsProbabilityMeasure μ]
     (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (kernelSum H X) 2 μ :=
  memLp_finsetSum Finset.univ (fun e _ => multilinear_kernel_memLp_two H e X hind hmeas hL2)
theorem kernelSum_integral_eq_zero [IsProbabilityMeasure μ]
     (hr : 0 < r)
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    (∫ ω, kernelSum H X ω ∂μ) = 0 := by
  unfold kernelSum
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero (fun e _ => multilinear_kernel_integral_eq_zero
      hr H e X hind hmeas hL2 hmean)
  · exact fun e _ => (multilinear_kernel_memLp_two H e X hind hmeas hL2).integrable
      (by norm_num)
theorem kernelSum_covariance_same_range [IsProbabilityMeasure μ]
     (hr : 0 < r) (ht : 0 < t)
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : MultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    covariance (kernelSum H X) (kernelSum G X) μ =
      ∑ e : Fin r ↪ Fin n, ∑ f : Fin t ↪ Fin n with Set.range e.toFun = Set.range f.toFun,
        ∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ := by
  have h_multilinear_kernel_pair_integrable (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j)) (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) : Integrable (fun ω => H (fun i => X (e i) ω) * G (fun i => X (f i) ω)) μ := by
    exact ((multilinear_kernel_memLp_two H e X hind hmeas hL2).integrable_mul
        (multilinear_kernel_memLp_two G f X hind hmeas hL2)).congr
      (Filter.Eventually.of_forall fun ω => rfl)
  classical
  unfold covariance
  rw [kernelSum_integral_eq_zero hr H X hind hmeas hL2 hmean,
    kernelSum_integral_eq_zero ht G X hind hmeas hL2 hmean]
  simp only [sub_zero]
  unfold kernelSum
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro e _
    rw [integral_finsetSum]
    · symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro f _ hf
      have hef : Set.range e ≠ Set.range f := by simpa using hf
      by_cases hsub : Set.range e ⊆ Set.range f
      · have hnot  := fun h => hef (Set.Subset.antisymm hsub h)
        obtain ⟨j, hj, hje⟩ := Set.not_subset.mp hnot
        obtain ⟨k, rfl⟩ := hj
        simpa only [mul_comm] using
          multilinear_kernel_pair_integral_eq_zero_left G H f e X hind hmeas hL2 hmean k hje
      · obtain ⟨j, hj, hjf⟩ := Set.not_subset.mp hsub
        obtain ⟨k, rfl⟩ := hj
        exact multilinear_kernel_pair_integral_eq_zero_left H G e f X hind hmeas hL2 hmean k hjf
    · exact fun f _ => h_multilinear_kernel_pair_integrable e f X hind hmeas hL2
  · exact fun e _ => integrable_finsetSum _ (fun f _ =>
      h_multilinear_kernel_pair_integrable e f X hind hmeas hL2)
lemma same_range_exists_perm  (e f : Fin r ↪ Fin n)
    (hef : Set.range f = Set.range e) :
    ∃ σ : Equiv.Perm (Fin r), ∀ i, e (σ i) = f i := by
  let σ := (Equiv.ofInjective f f.injective).trans
    ((Set.equivOfEq hef).trans (Equiv.ofInjective e e.injective).symm)
  refine ⟨σ, fun i => ?_⟩
  change e ((Equiv.ofInjective e e.injective).symm
    ((Set.equivOfEq hef) ((Equiv.ofInjective f f.injective) i))) = f i
  exact Equiv.apply_ofInjective_symm e.injective _
lemma embedding_range_comp_perm  (e : Fin r ↪ Fin n)
    (σ : Equiv.Perm (Fin r)) : Set.range (σ.toEmbedding.trans e) = Set.range e := by
  ext j
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨σ i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨σ.symm i, by simp⟩
lemma card_same_range_embeddings  (e : Fin r ↪ Fin n) :
    Fintype.card {f : Fin r ↪ Fin n // Set.range f.toFun = Set.range e.toFun} = r.factorial := by
  let g : Equiv.Perm (Fin r) → {f : Fin r ↪ Fin n // Set.range f.toFun = Set.range e.toFun} :=
    fun σ => ⟨σ.toEmbedding.trans e, embedding_range_comp_perm e σ⟩
  have hg : Function.Bijective g := by
    constructor
    · intro σ τ h
      apply Equiv.ext
      intro i
      apply e.injective
      exact congrArg (fun f => f.val i) h
    · intro f
      obtain ⟨σ, hσ⟩ := same_range_exists_perm e f.val f.property
      refine ⟨σ, ?_⟩
      apply Subtype.ext
      apply Function.Embedding.ext
      exact hσ
  rw [← Fintype.card_congr (Equiv.ofBijective g hg), Fintype.card_perm, Fintype.card_fin]
lemma same_range_card_eq  (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n)
    (hef : Set.range e = Set.range f) : r = t := by
  have h := Fintype.card_congr ((Equiv.ofInjective e e.injective).trans
    ((Set.equivOfEq hef).trans (Equiv.ofInjective f f.injective).symm))
  simpa using h
lemma multilinear_pair_integral_same_range [IsProbabilityMeasure μ]
    (H G : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (hsym : ∀ (σ : Equiv.Perm (Fin r)) v, G (fun i => v (σ i)) = G v)
    (e f e₀ : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hef : Set.range f = Set.range e) :
    (∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ) =
      ∫ ω, H (fun i => X (e₀ i) ω) * G (fun i => X (e₀ i) ω) ∂μ := by
  obtain ⟨σ, hσ⟩ := same_range_exists_perm e f hef
  have hG (ω : Ω) : G (fun i => X (f i) ω) = G (fun i => X (e i) ω) := by
    calc
      G (fun i => X (f i) ω) = G (fun i => X (e (σ i)) ω) :=
        congrArg G (funext fun i => congrArg (fun j => X j ω) (hσ i).symm)
      _ = _ := hsym σ (fun i => X (e i) ω)
  simp_rw [hG]
  have h := IdentDistrib.pi (fun i => hid (e i) (e₀ i))
    (hind.precomp e.injective) (hind.precomp e₀.injective)
  exact (h.comp (H.cont.mul G.cont).measurable).integral_eq
theorem kernelSum_covariance_different_orders [IsProbabilityMeasure μ]
     (hr : 0 < r) (ht : 0 < t) (hrt : r ≠ t)
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : MultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    covariance (kernelSum H X) (kernelSum G X) μ = 0 := by
  rw [kernelSum_covariance_same_range hr ht H G X hind hmeas hL2 hmean]
  apply Finset.sum_eq_zero
  intro e _
  have hfilter : Finset.univ.filter (fun f : Fin t ↪ Fin n =>
      Set.range e.toFun = Set.range f.toFun) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    exact hrt (same_range_card_eq e f (Finset.mem_filter.mp hf).2)
  rw [hfilter, Finset.sum_empty]
def kernelStatistic 
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) : Ω → ℝ :=
  fun ω => ((↑r.factorial * (n.descFactorial r : ℝ))⁻¹) *
    kernelSum H.toMultilinearMap X ω
theorem kernelStatistic_variance [IsProbabilityMeasure μ]
     (hr : 0 < r) (hrn H)
    (hsym : ∀ (σ : Equiv.Perm (Fin r)) v, H (fun i => v (σ i)) = H v)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    variance (kernelStatistic H X) μ =
      (↑r.factorial * (n.descFactorial r : ℝ))⁻¹ *
        ∫ ω, H (fun i => X (Fin.castLEEmb hrn i) ω) ^ 2 ∂μ := by
  unfold kernelStatistic
  have h_kernelSum_covariance : covariance (kernelSum H.toMultilinearMap X) (kernelSum H.toMultilinearMap X) μ =
      (n.descFactorial r : ℝ) * ↑r.factorial *
        ∫ ω, H (fun i => X ((Fin.castLEEmb hrn) i) ω) * H (fun i => X ((Fin.castLEEmb hrn) i) ω) ∂μ := by
    rw [kernelSum_covariance_same_range hr hr H.toMultilinearMap H.toMultilinearMap
      X hind hmeas hL2 hmean]
    let J := ∫ ω, H (fun i => X ((Fin.castLEEmb hrn) i) ω) * H (fun i => X ((Fin.castLEEmb hrn) i) ω) ∂μ
    have hs (e : Fin r ↪ Fin n) :
        (∑ f : Fin r ↪ Fin n with Set.range e.toFun = Set.range f.toFun,
          ∫ ω, H (fun i => X (e i) ω) * H (fun i => X (f i) ω) ∂μ) =
        ↑r.factorial * J := by
      have : (fun f : Fin r ↪ Fin n => Set.range e.toFun = Set.range f.toFun) =
          (fun f : Fin r ↪ Fin n => Set.range f.toFun = Set.range e.toFun) := by
        funext f
        exact propext eq_comm
      have hfilterEq : Finset.univ.filter (fun f : Fin r ↪ Fin n =>
          Set.range e.toFun = Set.range f.toFun) =
          Finset.univ.filter (fun f : Fin r ↪ Fin n =>
          Set.range f.toFun = Set.range e.toFun) := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact eq_comm
      rw [hfilterEq]
      calc
        _ = ∑ f : Fin r ↪ Fin n with Set.range f.toFun = Set.range e.toFun, J := by
          apply Finset.sum_congr rfl
          intro f hf
          exact multilinear_pair_integral_same_range H H hsym e f (Fin.castLEEmb hrn) X hind hid
            (Finset.mem_filter.mp hf).2
        _ = _ := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [← Fintype.card_subtype, card_same_range_embeddings e]
    change (∑ e : Fin r ↪ Fin n,
      ∑ f : Fin r ↪ Fin n with Set.range e.toFun = Set.range f.toFun,
        ∫ ω, H (fun i => X (e i) ω) * H (fun i => X (f i) ω) ∂μ) = _
    simp_rw [hs]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_embedding_eq, Fintype.card_fin]
    ring
  rw [variance_const_mul, ← covariance_self
    (kernelSum_memLp_two H.toMultilinearMap X hind hmeas hL2).aemeasurable,
    h_kernelSum_covariance]
  simp only [← pow_two]
  field_simp
def centeredKernelExpansion  (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ
      (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) : Ω → ℝ :=
  fun ω => c + ∑ r, kernelStatistic (H r) X ω
theorem kernelStatistic_memLp_two [IsProbabilityMeasure μ]
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (kernelStatistic H X) 2 μ :=
  (kernelSum_memLp_two H.toMultilinearMap X hind hmeas hL2).const_mul _
theorem centeredKernelExpansion_memLp_two [IsProbabilityMeasure μ]
     (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ
      (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (centeredKernelExpansion c H X) 2 μ :=
  (memLp_const c).add (memLp_finsetSum Finset.univ (fun r _ =>
    kernelStatistic_memLp_two (H r) X hind hmeas hL2))
theorem centeredKernelExpansion_expectation [IsProbabilityMeasure μ]
     (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ
      (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    (∫ ω, centeredKernelExpansion c H X ω ∂μ) = c := by
  unfold centeredKernelExpansion
  have hs : Integrable (fun ω => ∑ r, kernelStatistic (H r) X ω) μ :=
    (memLp_finsetSum Finset.univ (fun r _ =>
      kernelStatistic_memLp_two (H r) X hind hmeas hL2)).integrable (by norm_num)
  rw [integral_add (integrable_const c) hs, integral_const,
    integral_finsetSum Finset.univ (fun r _ =>
      (kernelStatistic_memLp_two (H r) X hind hmeas hL2).integrable (by norm_num))]
  have h_kernelStatistic_integral_eq_zero {r : ℕ} (hr : 0 < r) (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ) : (∫ ω, kernelStatistic H X ω ∂μ) = 0 := by
    unfold kernelStatistic
    rw [integral_const_mul,
      kernelSum_integral_eq_zero hr H.toMultilinearMap X hind hmeas hL2 hmean, mul_zero]
  have hz : (∑ r : Fin R, ∫ ω, kernelStatistic (H r) X ω ∂μ) = 0 :=
    Finset.sum_eq_zero (fun r _ => (h_kernelStatistic_integral_eq_zero (Nat.succ_pos r.val) (H r)))
  simp [hz]
theorem centeredKernelExpansion_variance [IsProbabilityMeasure μ]
     (c H)
    (hsym : ∀ r (σ : Equiv.Perm (Fin (r.val + 1))) v,
      H r (fun i => v (σ i)) = H r v)
    (X : Fin n → Ω → Fin p → ℝ) (hR : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    variance (centeredKernelExpansion c H X) μ =
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) *
        (n.descFactorial (r.val + 1) : ℝ))⁻¹ *
        ∫ ω, H r (fun i => X
          (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ^ 2 ∂μ := by
  have hstats (r : Fin R) := kernelStatistic_memLp_two (H r) X hind hmeas hL2
  unfold centeredKernelExpansion
  rw [variance_const_add (memLp_finsetSum Finset.univ (fun r _ => hstats r)).aestronglyMeasurable c, variance_fun_sum hstats]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single r]
  · rw [covariance_self (hstats r).aemeasurable]
    exact kernelStatistic_variance (by omega)
      ((Nat.succ_le_of_lt r.isLt).trans hR) (H r) (hsym r) X hind hmeas hid hL2 hmean
  · intro t _ htr
    unfold kernelStatistic
    rw [covariance_const_mul_left, covariance_const_mul_right, kernelSum_covariance_different_orders (by omega) (by omega) (by intro h; apply htr; apply Fin.ext; omega)
      (H r).toMultilinearMap (H t).toMultilinearMap X hind hmeas hL2 hmean]
    ring
  · exact fun h => (h (Finset.mem_univ r)).elim
theorem centerObservations_l2 [IsProbabilityMeasure μ]
     (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    iIndepFun (fun j ω => X j ω - m) μ ∧
      (∀ j, Measurable (fun ω => X j ω - m)) ∧
      (∀ i j, IdentDistrib (fun ω => X i ω - m) (fun ω => X j ω - m) μ μ) ∧
      (∀ j a, MemLp (fun ω => X j ω a - m a) 2 μ) ∧
      (∀ j a, ∫ ω, X j ω a - m a ∂μ = 0) := by
  refine ⟨hind.comp (fun _ => fun v : Fin p → ℝ => v - m)
      (fun _ => measurable_id.sub_const m),
    fun j => (hmeas j).sub_const m,
    fun i j => (hid i j).comp (measurable_id.sub_const m),
    fun j a => (hL2 j a).sub (memLp_const (m a)), ?_⟩
  intro j a
  rw [integral_sub ((hL2 j a).integrable (by norm_num)) (integrable_const (m a)),
    integral_const, hmean]
  simp
theorem polynomialLift_centering_l2 
    (F : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n) :
    RoughRegime.Upper.polynomialLift F X =
      centeredKernelExpansion (MvPolynomial.eval m F)
        (fun r : Fin R => iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m)
        (fun j ω => X j ω - m) := by
  rw [RoughRegime.LiftTranslation.polynomialLift_eq_centeredDerivativeLift F X m hdeg hRn]
  rfl
theorem product_kernel_square_integrable_l2 [IsProbabilityMeasure μ]
     (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (A : Fin r → Ω → Fin p → ℝ) (hm : ∀ i, Measurable (A i))
    (hL2 : ∀ i a, MemLp (fun ω => A i ω a) 2 μ) :
    Integrable (fun ω : Fin r → Ω => H (fun i => A i (ω i)) ^ 2)
      (Measure.pi (fun _ => μ)) := by
  let X : Fin r → (Fin r → Ω) → Fin p → ℝ := fun i ω => A i (ω i)
  exact (multilinear_kernel_memLp_two H.toMultilinearMap (Function.Embedding.refl _) X
    (iIndepFun_pi (fun i => (hm i).aemeasurable)) (fun i => (hm i).comp (measurable_pi_apply i)) (by intro i a; exact (hL2 i a).comp_measurePreserving (measurePreserving_eval (fun _ : Fin r => μ) i))).integrable_sq
lemma integral_pi_succ_l2 [IsProbabilityMeasure μ] 
    (f : (Fin (r + 1) → Ω) → ℝ) (hf : Integrable f (Measure.pi (fun _ => μ))) :
    (∫ x, f x ∂Measure.pi (fun _ : Fin (r + 1) => μ)) =
      ∫ x, ∫ y, f (Fin.cons x y) ∂Measure.pi (fun _ : Fin r => μ) ∂μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => Ω) 0
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => μ) 0
  have hf'  :=
    (he.symm e).integrable_comp_of_integrable hf
  rw [← (he.symm e).integral_comp' f]
  change (∫ x, (f ∘ e.symm) x ∂μ.prod (Measure.pi (fun _ : Fin r => μ))) = _
  rw [integral_prod _ hf']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      apply congrArg f
      funext i
      cases i using Fin.cases <;> simp [e]
lemma kernel_cons_square_integrable_l2 [IsProbabilityMeasure μ] 
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin (r + 1) => Fin p → ℝ) ℝ)
    (A B : Ω → Fin p → ℝ) (hA : Measurable A) (hB : Measurable B)
    (hL2A : ∀ a, MemLp (fun ω => A ω a) 2 μ)
    (hL2B : ∀ a, MemLp (fun ω => B ω a) 2 μ) :
    Integrable (fun xy : Ω × (Fin r → Ω) =>
      H (Fin.cons (A xy.1) (fun j => B (xy.2 j))) ^ 2)
      (μ.prod (Measure.pi (fun _ : Fin r => μ))) := by
  let C : Fin (r + 1) → Ω → Fin p → ℝ := Fin.cons A (fun _ => B)
  have hlpC : ∀ i a, MemLp (fun ω => C i ω a) 2 μ := by
    intro i a
    cases i using Fin.cases
    · simpa [C] using hL2A a
    · simpa [C] using hL2B a
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => Ω) 0
  have hf' := ((measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => μ) 0).symm e).integrable_comp_of_integrable (product_kernel_square_integrable_l2 H C (by intro i; cases i using Fin.cases <;> simp [C, hA, hB]) hlpC)
  apply hf'.congr
  exact Filter.Eventually.of_forall fun xy => by
    change (H (fun i => C i (e.symm xy i))) ^ 2 = _
    apply congrArg (fun z : ℝ => z ^ 2)
    apply congrArg H
    funext i
    cases i using Fin.cases <;> simp [C, e]
theorem multilinear_iid_centering_square_le_l2  [MeasurableSpace Ω]
    (μ ) [IsProbabilityMeasure μ] 
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Ω → Fin p → ℝ) (hm : Measurable X)
    (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 μ)
    (m : Fin p → ℝ) (hmean : ∀ a, ∫ ω, X ω a ∂μ = m a) :
    (∫ ω, H (fun j => X (ω j) - m) ^ 2 ∂Measure.pi (fun _ : Fin r => μ)) ≤
      ∫ ω, H (fun j => X (ω j)) ^ 2 ∂Measure.pi (fun _ : Fin r => μ) := by
  induction r with
  | zero =>
    apply le_of_eq
    congr 1
    funext ω
    congr 2
    funext j
    exact Fin.elim0 j
  | succ r ih =>
    let Y : Ω → Fin p → ℝ := fun ω => X ω - m
    have hY : Measurable Y := hm.sub measurable_const
    have hYlp  := fun a =>
      (hL2 a).sub (memLp_const (m a))
    have hc := kernel_cons_square_integrable_l2 H Y Y hY hY hYlp hYlp
    have hmix := kernel_cons_square_integrable_l2 H X Y hm hY hL2 hYlp
    calc
      _ = ∫ x, ∫ y, H (Fin.cons (Y x) (fun j => Y (y j))) ^ 2
          ∂Measure.pi (fun _ => μ) ∂μ := by
        rw [integral_pi_succ_l2 _ (product_kernel_square_integrable_l2 H (fun _ => Y) (fun _ => hY) (fun _ => hYlp))]
        congr 1
        funext x
        congr 1
        funext y
        congr 2
        funext j
        cases j using Fin.cases <;> simp
      _ = ∫ y, ∫ x, H (Fin.cons (Y x) (fun j => Y (y j))) ^ 2
          ∂μ ∂Measure.pi (fun _ => μ) := integral_integral_swap hc
      _ ≤ ∫ y, ∫ x, H (Fin.cons (X x) (fun j => Y (y j))) ^ 2
          ∂μ ∂Measure.pi (fun _ => μ) := by
        apply integral_mono_ae hc.integral_prod_right hmix.integral_prod_right
        exact Filter.Eventually.of_forall fun y => by
          let L : (Fin p → ℝ) →L[ℝ] ℝ :=
            (ContinuousMultilinearMap.apply ℝ (fun _ => Fin p → ℝ) ℝ
              (fun j => Y (y j))).comp H.curryLeft
          have h_linear_centering_square_le_l2 : (∫ ω, L (X ω - m) ^ 2 ∂μ) ≤ ∫ ω, L (X ω) ^ 2 ∂μ := by
            have h_vector_integral_of_coordinate_moments : Integrable X μ ∧ (∫ ω, X ω ∂μ) = m := by
              have hi  := integrable_pi_iff.mpr fun a =>
                (hL2 a).integrable (by norm_num)
              refine ⟨hi, ?_⟩
              funext a
              exact ((ContinuousLinearMap.proj a : (Fin p → ℝ) →L[ℝ] ℝ).integral_comp_comm hi).symm.trans (hmean a)
            obtain ⟨hi, hvector⟩ := h_vector_integral_of_coordinate_moments
            have hLX : Measurable (fun ω => L (X ω)) := L.continuous.measurable.comp hm
            have hml : (∫ ω, L (X ω) ∂μ) = L m := by
              rw [L.integral_comp_comm hi, hvector]
            have hv := variance_le_expectation_sq (μ := μ) hLX.aestronglyMeasurable
            rw [variance_eq_integral hLX.aemeasurable, hml] at hv
            simpa only [map_sub, Pi.pow_apply] using hv
          simpa only [L, ContinuousLinearMap.comp_apply,
            ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.curryLeft_apply]
            using h_linear_centering_square_le_l2
      _ = ∫ x, ∫ y, H (Fin.cons (X x) (fun j => Y (y j))) ^ 2
          ∂Measure.pi (fun _ => μ) ∂μ := (integral_integral_swap hmix).symm
      _ ≤ ∫ x, ∫ y, H (Fin.cons (X x) (fun j => X (y j))) ^ 2
          ∂Measure.pi (fun _ => μ) ∂μ := by
        apply integral_mono_ae hmix.integral_prod_left (kernel_cons_square_integrable_l2 H X X hm hm hL2 hL2).integral_prod_left
        exact Filter.Eventually.of_forall fun x => by
          simpa only [ContinuousMultilinearMap.curryLeft_apply] using ih (H.curryLeft (X x))
      _ = _ := by
        rw [integral_pi_succ_l2 _ (product_kernel_square_integrable_l2 H (fun _ => X) (fun _ => hm) (fun _ => hL2))]
        congr 1
        funext x
        congr 1
        funext y
        congr 2
        funext j
        cases j using Fin.cases <;> simp
theorem independent_centering_square_le_l2  [MeasurableSpace Ω]
    (μ ) [IsProbabilityMeasure μ] 
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin r → Ω → Fin p → ℝ) (hm : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ i a, MemLp (fun ω => X i ω a) 2 μ)
    (m : Fin p → ℝ) (hmean : ∀ i a, ∫ ω, X i ω a ∂μ = m a) :
    (∫ ω, H (fun i => X i ω - m) ^ 2 ∂μ) ≤ ∫ ω, H (fun i => X i ω) ^ 2 ∂μ := by
  by_cases hr : r = 0
  · subst r
    apply le_of_eq
    congr 1
    funext ω
    congr 2
    funext i
    exact Fin.elim0 i
  · let j : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    have hjointLaw : IdentDistrib (fun ω => fun i => X i ω)
        (fun ω => fun i => X j (ω i)) μ (Measure.pi (fun _ => μ)) := by
      refine ⟨(measurable_pi_iff.mpr hm).aemeasurable, (measurable_pi_iff.mpr fun i => (hm j).comp (measurable_pi_apply i)).aemeasurable, ?_⟩
      rw [hind.map_fun_eq_pi_map (fun i => (hm i).aemeasurable),
        Measure.pi_map_pi (fun _ => (hm j).aemeasurable)]
      congr 1
      funext i
      exact (hid i j).map_eq
    have hc : Measurable (fun v : Fin r → Fin p → ℝ => H (fun i => v i - m) ^ 2) :=
      (H.coe_continuous.measurable.comp
        (measurable_pi_iff.mpr fun i => (measurable_pi_apply i).sub measurable_const)).pow_const 2
    have hcEq : (∫ ω, H (fun i => X i ω - m) ^ 2 ∂μ) =
        ∫ ω, H (fun i => X j (ω i) - m) ^ 2 ∂Measure.pi (fun _ => μ) := by
      simpa only [Function.comp_def] using (hjointLaw.comp hc).integral_eq
    have huEq : (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) =
        ∫ ω, H (fun i => X j (ω i)) ^ 2 ∂Measure.pi (fun _ => μ) := by
      simpa only [Function.comp_def] using (hjointLaw.comp (H.coe_continuous.measurable.pow_const 2)).integral_eq
    rw [hcEq, huEq]
    exact multilinear_iid_centering_square_le_l2 μ H (X j) (hm j) (hL2 j) m (hmean j)
theorem polynomialLift_memLp_two_l2 [IsProbabilityMeasure μ]
     (F )
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (RoughRegime.Upper.polynomialLift F X) 2 μ := by
  rw [polynomialLift_centering_l2 F X m hdeg hRn]
  exact centeredKernelExpansion_memLp_two _ _ _
    (hind.comp (fun _ => fun v => v - m)
      (fun _ => measurable_id.sub_const m))
    (fun j => (hmeas j).sub_const m)
    (fun j a => (hL2 j a).sub (memLp_const (m a)))
theorem polynomialLift_expectation_l2 [IsProbabilityMeasure μ]
     (F )
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    (∫ ω, RoughRegime.Upper.polynomialLift F X ω ∂μ) = MvPolynomial.eval m F := by
  obtain ⟨hi, hm, _, hlp, hzero⟩ := centerObservations_l2 X m hind hmeas hid hL2 hmean
  rw [polynomialLift_centering_l2 F X m hdeg hRn]
  exact centeredKernelExpansion_expectation _ _ _ hi hm hlp hzero
theorem descFactorial_lower_bound {n R k : ℕ} (hRn : R ≤ n) (hkR : k ≤ R)
     (hΛ : 0 ≤ Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    Λ ^ k ≤ (n.descFactorial k ) := by
  have hcast : ((n + 1 - k : ℕ) : ℝ) = ↑n + 1 - k := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have : (k : ℝ) ≤ R := by exact_mod_cast hkR
  have hbase : Λ ≤ ((n + 1 - k : ℕ) : ℝ) := by rw [hcast]; linarith
  calc
    Λ ^ k ≤ (((n + 1 - k : ℕ) : ℝ)) ^ k := pow_le_pow_left₀ hΛ hbase k
    _ ≤ (n.descFactorial k : ℝ) := by exact_mod_cast Nat.pow_sub_le_descFactorial n k
theorem polynomialLift_variance_le_raw_power_l2 [IsProbabilityMeasure μ]
     (F )
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    variance (RoughRegime.Upper.polynomialLift F X) μ ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
        ∫ ω, (iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m
          (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hRn) i) ω)) ^ 2 ∂μ := by
  have h_polynomialLift_variance_le_raw_l2 : variance (RoughRegime.Upper.polynomialLift F X) μ ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) *
        (n.descFactorial (r.val + 1) : ℝ))⁻¹ *
        ∫ ω, (iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m
          (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hRn) i) ω)) ^ 2 ∂μ := by
    have h_polynomialLift_variance_l2 : variance (RoughRegime.Upper.polynomialLift F X) μ =
        ∑ r : Fin R, (((r.val + 1).factorial : ℝ) *
          (n.descFactorial (r.val + 1) : ℝ))⁻¹ *
          ∫ ω, (iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m
            (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hRn) i) ω - m)) ^ 2 ∂μ := by
      obtain ⟨hi, hm, hid', hlp, hzero⟩ := centerObservations_l2 X m hind hmeas hid hL2 hmean
      rw [polynomialLift_centering_l2 F X m hdeg hRn]
      apply centeredKernelExpansion_variance _ _ ?_ _ hRn hi hm hid' hlp hzero
      intro r σ v
      exact (AnalyticOnNhd.eval_mvPolynomial F).analyticOn.iteratedFDeriv_comp_perm v σ
    rw [h_polynomialLift_variance_l2]
    apply Finset.sum_le_sum
    intro r _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    let e := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hRn)
    exact independent_centering_square_le_l2 μ _ (fun i => X (e i))
      (fun i => hmeas (e i)) (hind.precomp e.injective)
      (fun i j => hid (e i) (e j)) (fun i a => hL2 (e i) a) m
      (fun i a => hmean (e i) a)
  apply h_polynomialLift_variance_le_raw_l2.trans
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => sq_nonneg _)
  have hb := descFactorial_lower_bound hRn (Nat.succ_le_of_lt r.isLt) hΛ.le hΛn
  have hfac : 0 < ((r.val + 1).factorial : ℝ) := by positivity
  have hpow : 0 < Λ ^ (r.val + 1) := pow_pos hΛ _
  exact (inv_le_inv₀ (mul_pos hfac (hpow.trans_le hb)) (mul_pos hfac hpow)).2
    (mul_le_mul_of_nonneg_left hb hfac.le)
end NearlyMinimax.LiftL2
