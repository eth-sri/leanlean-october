module

public import Mathlib
public import RoughRegime.UpperCovariance
public import RoughRegime.PolynomialDerivatives

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory

namespace RoughRegime.LiftTranslation
set_option maxHeartbeats 800000

/-- Marginalizing an ordered injective tuple over unused slots gives the exact
remaining falling-factorial multiplicity. -/
lemma sum_embedding_restriction {A B : Type*} [Fintype A] [Fintype B]
    (n : ℕ) (f : (A ↪ Fin n) → ℝ) :
    (∑ e : A ⊕ B ↪ Fin n, f (Function.Embedding.inl.trans e)) =
      ((n - Fintype.card A).descFactorial (Fintype.card B) : ℝ) *
        ∑ e : A ↪ Fin n, f e := by
  classical
  let E := Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted (α := A) (β := B) (γ := Fin n)
  calc
    _ = ∑ e : A ⊕ B ↪ Fin n, f (E e).1 := by rfl
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

section
variable {A : Type*} [Fintype A]
    (n : ℕ)

lemma sum_embedding_subtype_restriction (S : Finset A) (f : (↥S ↪ Fin n) → ℝ) :
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
      norm_num
    _ = ((n - Fintype.card ↥S).descFactorial (Fintype.card C) : ℝ) *
        ∑ e : ↥S ↪ Fin n, f e := sum_embedding_restriction n f
    _ = _ := by
      have hcard : Fintype.card C = Fintype.card A - S.card := by
        change Fintype.card {i : A // ¬i ∈ S} = _
        rw [Fintype.card_subtype_compl]
        simp
      rw [hcard]
      simp

/-- Normalization cancels precisely the multiplicity of unused sample slots. -/
lemma normalized_embedding_subtype_restriction (hn : Fintype.card A ≤ n) (S : Finset A) (f : (↥S ↪ Fin n) → ℝ) :
    (n.descFactorial (Fintype.card A) : ℝ)⁻¹ *
        (∑ e : A ↪ Fin n, f ((Function.Embedding.subtype (fun i => i ∈ S)).trans e)) =
      (n.descFactorial S.card : ℝ)⁻¹ * ∑ e : ↥S ↪ Fin n, f e := by
  classical
  rw [sum_embedding_subtype_restriction]
  have hcancel := Nat.descFactorial_mul_descFactorial (n := n) S.card_le_univ
  have hq : (n.descFactorial (Fintype.card A) : ℝ) ≠ 0 := by
    simp [Nat.descFactorial_eq_zero_iff_lt, not_lt_of_ge hn]
  have hr : (n.descFactorial S.card : ℝ) ≠ 0 := by
    simp [Nat.descFactorial_eq_zero_iff_lt, not_lt_of_ge (S.card_le_univ.trans hn)]
  field_simp
  rw [mul_right_comm, ← Nat.cast_mul, hcancel]

end

/-- Exact centering expansion of one monomial lift. Every subset records the slots
in which a centered observation is used. -/
theorem monomialLift_centering {Ω : Type*} {n p q : ℕ}
    (σ : Fin q → Fin p) (Y : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hqn : q ≤ n) (ω : Ω) :
    RoughRegime.Upper.monomialLift σ (fun j ω => Y j ω + m) ω =
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
        ∏ i : ↥S, Y (e i) ω (σ i) := (Finset.prod_coe_sort S (fun i => Y (e i) ω (σ i))).symm
  simp_rw [hprod]
  rw [← Finset.sum_mul]
  have h : (n.descFactorial q : ℝ)⁻¹ * (∑ e : Fin q ↪ Fin n, ∏ i : ↥S, Y (e i) ω (σ i)) =
      (n.descFactorial S.card : ℝ)⁻¹ * (∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) ω (σ i)) :=
    by
      simpa using (normalized_embedding_subtype_restriction n (by simpa using hqn) S
        (fun e : ↥S ↪ Fin n => ∏ i : ↥S, Y (e i) ω (σ i)))
  linear_combination (∏ i ∈ Sᶜ, m (σ i)) * h

section
variable {A B : Type*} [Fintype A] [Fintype B]

/-- An ordering of a set is equivalently an embedding with that set as range. -/
def embeddingsWithRangeEquiv (S : Set B) : (A ≃ S) ≃ {e : A ↪ B // Set.range e = S} where
  toFun a := ⟨a.toEmbedding.trans (.subtype _), by simp⟩
  invFun e := by
    classical
    exact e.1.toEquivRange.trans (Set.equivOfEq e.2)
  left_inv a := by ext; rfl
  right_inv e := Subtype.ext (Function.Embedding.ext fun _ => rfl)

/-- An ordered injective tuple consists of its unordered range and an ordering of that range. -/
lemma sum_embeddings_by_range [DecidableEq A] [DecidableEq B]
    (f : (A ↪ B) → ℝ) :
    (∑ e : A ↪ B, f e) =
      ∑ S : Finset B, ∑ a : A ≃ ↥S,
        f (a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))) := by
  let g (u : Σ S : Finset B, A ≃ ↥S) := ((embeddingsWithRangeEquiv (u.1 : Set B)) u.2).1
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨S, a⟩ ⟨T, b⟩ h
      have hs : Set.range (g ⟨S, a⟩) = (S : Set B) := ((embeddingsWithRangeEquiv _) a).2
      rw [h] at hs
      have hST := Finset.coe_injective (hs.symm.trans ((embeddingsWithRangeEquiv _) b).2)
      subst T
      exact congrArg (Sigma.mk S) ((embeddingsWithRangeEquiv (S : Set B)).injective (Subtype.ext h))
    · intro e
      let S := Finset.univ.map e
      have hS : Set.range e = (S : Set B) := by ext; simp [S]
      let E : (A ≃ ↥S) ≃ _ := embeddingsWithRangeEquiv (S : Set B)
      exact ⟨⟨S, E.symm ⟨e, hS⟩⟩, congrArg Subtype.val (E.apply_symm_apply ⟨e, hS⟩)⟩
  calc
    _ = ∑ u : Σ S : Finset B, A ≃ ↥S, f (g u) := ((Equiv.ofBijective g hg).sum_comp f).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      exact Fintype.sum_equiv (.refl _) _ _ fun _ => Fintype.sum_equiv (.refl _) _ _ fun _ => rfl

end

/-- The sample sum does not depend on which ordering is chosen for a fixed slot set. -/
lemma sum_samples_subset_equiv {n p r : ℕ} (S : Finset (Fin p))
    (a : Fin r ≃ ↥S) (Y : Fin n → Fin p → ℝ) :
    (∑ e : Fin r ↪ Fin n, ∏ i : Fin r, Y (e i) (a i)) =
      ∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) i := by
  classical
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
    _ = _ := E.sum_comp (fun e : ↥S ↪ Fin n => ∏ i : ↥S, Y (e i) i)

lemma monomial_replacement_by_subset {p q r : ℕ} (σ : Fin q → Fin p)
    (S : Finset (Fin q)) (a : Fin r ≃ ↥S) (m : Fin p → ℝ)
    (v : Fin r → Fin p → ℝ) :
    (∏ j : Fin q, if h : j ∈ Set.range
        (a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))) then
      v ((a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))).toEquivRange.symm ⟨j, h⟩)
        (σ j) else m (σ j)) =
      (∏ i : Fin r, v i (σ (a i))) * ∏ j ∈ Sᶜ, m (σ j) := by
  classical
  let b : Fin r ↪ Fin q := a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))
  let f : Fin q → ℝ := fun j => if h : j ∈ Set.range b then v (b.toEquivRange.symm ⟨j, h⟩) (σ j)
    else m (σ j)
  change (∏ j : Fin q, f j) = _
  rw [← Finset.prod_mul_prod_compl S f]
  congr 1
  · calc
      _ = ∏ j : ↥S, f j := (Finset.prod_coe_sort S f).symm
      _ = ∏ i : Fin r, f (a i) := (a.prod_comp (fun j : ↥S => f j)).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        have hi : (a i : Fin q) ∈ Set.range b := ⟨i, rfl⟩
        simp only [f, dite_eq_left hi]
        change v (b.toEquivRange.symm ⟨b i, _⟩) (σ (a i)) = _
        simp
  · apply Finset.prod_congr rfl
    aesop

/-- Grouping the derivative injections by their range removes all dependence on
how the selected monomial slots are ordered. -/
lemma monomial_derivative_sample_sum {n p q r : ℕ} (σ : Fin q → Fin p)
    (m : Fin p → ℝ) (Y : Fin n → Fin p → ℝ) :
    (∑ e : Fin r ↪ Fin n,
      iteratedFDeriv ℝ r (RoughRegime.PolynomialDerivatives.monomial σ) m (fun i => Y (e i))) =
      ∑ S : Finset (Fin q), (Fintype.card (Fin r ≃ ↥S) : ℝ) *
        ((∏ j ∈ Sᶜ, m (σ j)) * (∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) (σ i))) := by
  classical
  simp_rw [RoughRegime.PolynomialDerivatives.monomial_iteratedFDeriv]
  rw [Finset.sum_comm]
  rw [sum_embeddings_by_range]
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
        simpa only [← Finset.sum_mul, sum_samples_subset_equiv S a (fun j i => Y j (σ i))] using mul_comm _ _
  simp_rw [hsamp]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma card_equiv_fin_subset {q r : ℕ} (S : Finset (Fin q)) :
    Fintype.card (Fin r ≃ ↥S) = if S.card = r then r.factorial else 0 := by
  classical
  split_ifs with h
  · let a : Fin r ≃ ↥S := Fintype.equivOfCardEq (by simpa using h.symm)
    simp_all [Fintype.card_equiv a]
  · have hempty : IsEmpty (Fin r ≃ ↥S) := ⟨fun a => h (by simpa using (Fintype.card_congr a).symm)⟩
    simp

lemma normalized_monomial_derivative_sample_sum {n p q r : ℕ} (σ : Fin q → Fin p)
    (m : Fin p → ℝ) (Y : Fin n → Fin p → ℝ) :
    (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ * ∑ e : Fin r ↪ Fin n,
      iteratedFDeriv ℝ r (RoughRegime.PolynomialDerivatives.monomial σ) m (fun i => Y (e i))) =
      ∑ S : Finset (Fin q), if S.card = r then
        (∏ j ∈ Sᶜ, m (σ j)) *
          ((n.descFactorial S.card : ℝ)⁻¹ * ∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) (σ i))
        else 0 := by
  classical
  rw [monomial_derivative_sample_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [card_equiv_fin_subset]
  split_ifs with h
  · rw [h]
    have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
    grind
  · simp

/-- The derivative-defined distinct-sample expression at any expansion point. -/
def derivativeLiftAt {Ω : Type*} {n p : ℕ} (R : ℕ) (f : (Fin p → ℝ) → ℝ)
    (m : Fin p → ℝ) (Y : Fin n → Ω → Fin p → ℝ) (ω : Ω) : ℝ :=
  ∑ r ∈ Finset.range (R + 1),
    (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ * ∑ e : Fin r ↪ Fin n,
      iteratedFDeriv ℝ r f m (fun i => Y (e i) ω))

section
variable {Ω : Type*}

/-- A monomial lift agrees exactly with the centered derivative expansion at its degree. -/
theorem monomialLift_eq_derivativeLiftAt {n p q : ℕ}
    (σ : Fin q → Fin p) (Y : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hqn : q ≤ n) (ω : Ω) :
    RoughRegime.Upper.monomialLift σ (fun j ω => Y j ω + m) ω =
      derivativeLiftAt q (RoughRegime.PolynomialDerivatives.monomial σ) m Y ω := by
  classical
  rw [monomialLift_centering σ Y m hqn ω]
  unfold derivativeLiftAt
  have hexp (r : ℕ) := normalized_monomial_derivative_sample_sum (r := r) σ m (fun j => Y j ω)
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
    _ = _ := Finset.sum_congr rfl (fun r _ => (hexp r).symm)

lemma derivativeLiftAt_monomial_stable {n p q R : ℕ}
    (σ : Fin q → Fin p) (Y : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hqR : q ≤ R) (ω : Ω) :
    derivativeLiftAt R (RoughRegime.PolynomialDerivatives.monomial σ) m Y ω =
      derivativeLiftAt q (RoughRegime.PolynomialDerivatives.monomial σ) m Y ω := by
  classical
  unfold derivativeLiftAt
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hqR 1))
  intro r _ hr
  have hqr : q < r := by
    simp_all
  have hzero (e : Fin r ↪ Fin n) :=
    RoughRegime.PolynomialDerivatives.monomial_iteratedFDeriv_above_degree σ m
      (fun i => Y (e i) ω) hqr
  simp only [hzero, Finset.sum_const_zero, mul_zero]

lemma derivativeLiftAt_polynomial_monomial_sum {n p : ℕ}
    (R : ℕ) (F : MvPolynomial (Fin p) ℝ) (Y : Fin n → Ω → Fin p → ℝ)
    (m : Fin p → ℝ) (ω : Ω) :
    derivativeLiftAt R (fun x => MvPolynomial.eval x F) m Y ω =
      ∑ α ∈ F.support, F.coeff α * derivativeLiftAt R
        (RoughRegime.PolynomialDerivatives.monomial (RoughRegime.Upper.exponentCoordinates α)) m Y ω := by
  classical
  simp only [derivativeLiftAt]
  simp_rw [RoughRegime.PolynomialDerivatives.polynomial_iteratedFDeriv_monomial_sum, Finset.mul_sum]
  conv_lhs =>
    enter [2, r]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  congr! 3
  ring

/-- The monomial-defined unbiased lift equals the exact derivative-defined lift at
every expansion point. In particular it is invariant under centering the observations. -/
theorem polynomialLift_eq_derivativeLiftAt {n p R : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (Y : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n) (ω : Ω) :
    RoughRegime.Upper.polynomialLift F (fun j ω => Y j ω + m) ω =
      derivativeLiftAt R (fun x => MvPolynomial.eval x F) m Y ω := by
  classical
  rw [derivativeLiftAt_polynomial_monomial_sum]
  unfold RoughRegime.Upper.polynomialLift
  apply Finset.sum_congr rfl
  intro α hα
  congr 1
  have hqR : Fintype.card (RoughRegime.Upper.ExponentSlots α) ≤ R := by
    rw [RoughRegime.Upper.exponentSlots_card]
    exact (MvPolynomial.le_totalDegree hα).trans hdeg
  rw [derivativeLiftAt_monomial_stable _ Y m hqR ω]
  exact monomialLift_eq_derivativeLiftAt _ Y m (hqR.trans hRn) ω

lemma derivativeLiftAt_eq_centeredDerivativeLift {n p : ℕ}
    (R : ℕ) (F : MvPolynomial (Fin p) ℝ) (Y : Fin n → Ω → Fin p → ℝ)
    (m : Fin p → ℝ) (ω : Ω) :
    derivativeLiftAt R (fun x => MvPolynomial.eval x F) m Y ω =
      RoughRegime.UpperCovariance.centeredDerivativeLift R F m Y ω := by
  classical
  unfold derivativeLiftAt RoughRegime.UpperCovariance.centeredDerivativeLift
    RoughRegime.UpperCovariance.centeredKernelExpansion
    RoughRegime.UpperCovariance.kernelStatistic RoughRegime.UpperCovariance.kernelSum
  simp only [ContinuousMultilinearMap.coe_coe]
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

/-- Complete algebraic identity identifying the original coefficient lift with its
centered derivative expansion. The center is arbitrary; no population identity is assumed. -/
theorem polynomialLift_eq_centeredDerivativeLift {n p R : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n) :
    RoughRegime.Upper.polynomialLift F X =
      RoughRegime.UpperCovariance.centeredDerivativeLift R F m (fun j ω => X j ω - m) := by
  funext ω
  have hX : (fun j ω => (X j ω - m) + m) = X := by
    funext j ω
    exact sub_add_cancel (X j ω) m
  simp [← derivativeLiftAt_eq_centeredDerivativeLift, ← polynomialLift_eq_derivativeLiftAt F (fun j ω => X j ω - m) m hdeg hRn ω]

end

end RoughRegime.LiftTranslation
