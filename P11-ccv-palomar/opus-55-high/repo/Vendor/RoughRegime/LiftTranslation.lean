module

public import Mathlib
public import RoughRegime.UpperCovariance
public import RoughRegime.PolynomialDerivatives
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

𝚵

namespace RoughRegime.LiftTranslation
𝚱

𝗃 𝕴 Function.Embedding.subtype fun i => i ∈ ἀ
𝗇 𝔄 𝕴 S
𝗇 𝔍 ↥S ↪ Fin n
𝗇 𝔏 (n.descFactorial S.card : ℝ)⁻¹
𝗇 𝔠 𝘿
𝗇 𝔰 Equiv.refl $ Fin n
𝗃 𝕳 ∑ e : ἀ, f e
section

variable [Fintype A]
    (n)

𝗇 𝔙 A ↪ Fin n
𝗇 𝔛 (n - Fintype.card A).descFactorial $ Fintype.card B
/-- Marginalizing an ordered injective tuple over unused slots gives the exact
remaining falling-factorial multiplicity. -/
theorem sum_embedding_restriction [Fintype B]
    (f : 𝔙 → ℝ) :
     ∑ e : A ⊕ B ↪ Fin n, f (Function.Embedding.inl.trans e) =
      𝔛 *
        𝕳 𝔙 := by
  classical
  let E := Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted (α := A) (β := B) (γ := Fin n)
  calc
    _ = ∑ e : A ⊕ B ↪ Fin n, f (E e).1 := 𝖦₄
    _ = ∑ u : Σ e : 𝔙, B ↪ ↥(Set.range e)ᶜ, f u.1 := E.sum_comp fun u => f u.1
    _ = ∑ e : 𝔙, 𝔛 * f e := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro e _
      have hcard : Fintype.card ↥(Set.range e)ᶜ = n - Fintype.card A := by
        change Fintype.card {j : Fin n // ¬j ∈ Set.range e} = _
        rw [Fintype.card_subtype_compl]
        rw [← Fintype.card_congr e.toEquivRange, Fintype.card_fin]
      simp_all
    𝔠 := 𝘟₂

𝗇 𝔒 (n - S.card).descFactorial $ Fintype.card A - S.card
𝗇 𝕭 (𝔄).trans e
𝗇 𝔧 ∑ e : 𝔙, f 𝕭
𝗇 𝔪 𝕳 𝔍
𝗇 𝔶 ↥S ⊕ C ↪ Fin n
theorem sum_embedding_subtype_restriction (S : Finset A) (f : 𝔍 → ℝ) :
    𝔧 =
      𝔒 *
        𝔪 := by
  classical
  let C := (S : Set A)ᶜ
  let E :=
    Equiv.embeddingCongr (Equiv.Set.sumCompl (S : Set A)) 𝔰
  calc
    _ = ∑ e : 𝔶,
        f ((𝔄).trans $ E e ) :=
      (E.sum_comp fun e =>
        f 𝕭 ).symm
    _ = ∑ e : 𝔶, f (Function.Embedding.inl.trans e) := by
      apply Finset.sum_congr rfl
      intro e _
      congr 1
      apply Function.Embedding.ext
      intro i
      change e ((Equiv.Set.sumCompl S).symm (i : A)) = e (Sum.inl i)
      norm_num
    _ = (n - Fintype.card ↥S).descFactorial (Fintype.card C) *
        𝔪 := sum_embedding_restriction n f
    𝔠 := by
      have hcard : Fintype.card C = Fintype.card A - S.card := by
        change Fintype.card {i : A // ¬𝚒₁} = _
        simp
      simp_all

𝗇 𝔜 n.descFactorial $ Fintype.card A
𝗇 𝔷 (𝔜 : ℝ)⁻¹
/-- Normalization cancels precisely the multiplicity of unused sample slots. -/
theorem normalized_embedding_subtype_restriction (hn : Fintype.card A ≤ n) (S : Finset A) (f : 𝔍 → ℝ) :
    𝔷 *
        𝔧 =
      𝔏 * 𝔪 := by
  classical
  rw [sum_embedding_subtype_restriction]
  have hq : 𝔜 ≠ 0 := by
    simpa
  have hr : n.descFactorial S.card ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt $ Nat.descFactorial_pos.mpr $ S.card_le_univ.trans hn
  have hprod : 𝔒 *
      (n.descFactorial S.card : ℝ) = 𝔜 := by
    exact_mod_cast Nat.descFactorial_mul_descFactorial S.card_le_univ
  have hcoeff : 𝔷 *
      𝔒 =
        𝔏 := by
    field_simp
    exact hprod
  rw [← mul_assoc, hcoeff]

end

𝗇 𝔯 Y $ e i
𝗇 𝔮 𝔯 ω $ σ i
𝗇 𝔅 ∏ i : ↥S, 𝔮
𝗇 𝔉 Fin n → Ω → 𝗓
𝗇 𝔓 fun j ω => Y j ω + m
𝗇 𝔗 Finset $ Fin q
𝗇 𝔟 ∏ i ∈ Sᶜ, m (σ i)
𝗇 𝔡 Fin q → Fin p
𝗇 𝔫 ∑ e : 𝔍, 𝔅
𝗇 𝔱 𝔏 * 𝔫
/-- Exact centering expansion of one monomial lift. Every subset records the slots
in which a centered observation is used. -/
theorem monomialLift_centering
    (σ : 𝔡) (Y : 𝔉) m
    (hqn : q ≤ n) ω :
    RoughRegime.Upper.monomialLift σ 𝔓 ω =
      ∑ S : 𝔗, 𝔟 *
        𝔱 := by
  classical
  unfold RoughRegime.Upper.monomialLift
  simp only [Pi.add_apply]
  simp_rw [Fintype.prod_add (fun i => Y _ ω $ σ i ) fun i => m $ σ i ]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  have hprod (e : Fin q ↪ Fin n) := (Finset.prod_coe_sort S fun i => 𝔮 ).symm
  simp_rw [hprod]
  rw [← Finset.sum_mul]
  have h : (n.descFactorial q : ℝ)⁻¹ * ∑ e : Fin q ↪ Fin n, 𝔅 =
      𝔱 :=
    by
      simpa using normalized_embedding_subtype_restriction n (by simpa using hqn) S
         fun e => 𝔅
  linear_combination 𝔟 * h

𝗇 𝔲 Set.range $ a.toEmbedding.trans 𝔄
section

variable [Fintype A]
    [Fintype B]

𝗇 𝕮 A ≃ ↥S
theorem range_embedding_of_subset_equiv (S : Finset B) (a : 𝕮) :
    𝔲 = S := by
  simp

𝗇 𝔤 Σ S : Finset B, 𝕮
𝗇 𝔳 A ↪ B
/-- An ordered injective tuple consists of its unordered range and an ordering of that range. -/
theorem sum_embeddings_by_range [DecidableEq A] [DecidableEq B]
    (f : 𝔳 → ℝ) :
    𝕳 𝔳 =
      ∑ S : Finset B, ∑ a : 𝕮,
        f (a.toEmbedding.trans 𝔄) := by
  classical
  let g : 𝔤 → 𝔳 :=
    fun u => u.2.toEmbedding.trans 𝕴 u.1
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨S, a⟩ ⟨T, b⟩ h
      have hST : S = T := by
        apply Finset.coe_injective
        rw [← range_embedding_of_subset_equiv S a, ← range_embedding_of_subset_equiv T b]
        grind
      subst T
      have hab : a = b := by
        apply Equiv.ext
        intro i
        apply Subtype.ext
        exact congrArg (fun e => e i) h
      subst b
      rfl
    · intro e
      let S := Finset.univ.map e
      have hS : Set.range e = S := 𝖤₃
      let a := e.toEquivRange.trans $ Set.equivOfEq hS
      tauto
  calc
    _ = ∑ u : 𝔤, f (g u) :=
      ((Equiv.ofBijective g hg).sum_comp f).symm
    𝔠 := by rw [Fintype.sum_sigma]

end

𝗇 𝔎 𝚖₁
𝗇 𝔐 Fin r ≃ ↥S
𝗇 𝔖 𝗓
𝗇 𝔥 ∏ i : ↥S, 𝔯 i
𝗇 𝕬 Fin n → 𝔖
𝗃 𝕶 ∏ i : Fin r, ἀ (a i)
/-- The sample sum does not depend on which ordering is chosen for a fixed slot set. -/
theorem sum_samples_subset_equiv (S : Finset $ Fin p )
    (a : 𝔐) (Y : 𝕬) :
     ∑ e : 𝔎, 𝕶 𝔯 =
      ∑ e : 𝔍, 𝔥 := by
  classical
  let E :=
    Equiv.embeddingCongr a 𝔰
  calc
    _ = ∑ e : 𝔎, ∏ i : ↥S, Y ((E e) i) i := by
      apply Finset.sum_congr rfl
      intro e _
      rw [← a.prod_comp]
      aesop
    𝔠 := E.sum_comp fun e => 𝔥

𝗇 𝔬 m $ σ j
𝗇 𝔇 ∏ j ∈ Sᶜ, 𝔬
𝗇 𝔈 ∑ e : ↥S ↪ Fin n, ∏ i : ↥S, 𝔯 (σ i)
𝗇 𝔘 fun i => 𝔯
𝗇 𝕯 iteratedFDeriv ℝ r
𝗇 𝔨 ∑ e : 𝔎, 𝕯 (RoughRegime.PolynomialDerivatives.monomial σ) m 𝔘
section

variable (σ : 𝔡)

𝗇 𝔞 σ $ a i
𝗇 𝔩 (a.toEmbedding.trans 𝔄).toEquivRange.symm 𝗷₂
theorem monomial_replacement_by_subset (S : 𝔗) (a : 𝔐) (m : 𝔖)
    (v : Fin r → 𝔖) :
    (∏ j : Fin q, if h : j ∈ 𝔲 then
      v 𝔩
        $ σ j else 𝔬) =
      (∏ i : Fin r, v i 𝔞) * 𝔇 := by
  classical
  let b := a.toEmbedding.trans 𝔄
  let f := fun j => if h : j ∈ Set.range b then v (b.toEquivRange.symm 𝗷₂) $ σ j
    else 𝔬
  rw [← Finset.prod_mul_prod_compl S f]
  congr 1
  · calc
      _ = ∏ j : ↥S, f j := (Finset.prod_coe_sort S f).symm
      _ = 𝕶 f := (a.prod_comp fun j => f j ).symm
      𝔠 := by
        apply Finset.prod_congr rfl
        intro i _
        have hi : (a i : Fin q) ∈ Set.range b := ⟨i, rfl⟩
        simp only [f, dite_eq_left hi]
        change v (b.toEquivRange.symm ⟨b i, _⟩) 𝔞 = _
        simp
  · apply Finset.prod_congr rfl
    aesop

/-- Grouping the derivative injections by their range removes all dependence on
how the selected monomial slots are ordered. -/
theorem monomial_derivative_sample_sum m (Y : 𝕬) :
    𝔨 =
      ∑ S : 𝔗, Fintype.card 𝔐 *
        (𝔇 * 𝔈) := by
  classical
  simp_rw [RoughRegime.PolynomialDerivatives.monomial_iteratedFDeriv]
  rw [Finset.sum_comm]
  rw [sum_embeddings_by_range]
  apply Finset.sum_congr rfl
  intro S _
  have hsamp (a : 𝔐) :
      (∑ e : 𝔎,
        ∏ j : Fin q, if h : j ∈ 𝔲 then
          Y (e 𝔩) $ σ j else 𝔬) =
        𝔇 * 𝔈 := by
    calc
      _ = ∑ e : 𝔎, (∏ i : Fin r, 𝔯 𝔞) * 𝔇 := by
        apply Finset.sum_congr rfl
        intro e _
        exact monomial_replacement_by_subset σ S a m 𝔘
      𝔠 := by
        rw [← Finset.sum_mul]
        rw [sum_samples_subset_equiv S a fun j i => Y j $ σ i ]
        ring
  simp_rw [hsamp]
  simp

end

theorem card_equiv_fin_subset (S : 𝔗) :
    Fintype.card 𝔐 = if S.card = r then r.factorial else 0 := by
  classical
  split_ifs with h
  · let a : 𝔐 := Fintype.equivOfCardEq $ by simpa using h.symm
    rw [Fintype.card_equiv a]
    simp
  · have hempty : IsEmpty 𝔐 := ⟨fun a => h $ by simpa using (Fintype.card_congr a).symm ⟩
    exact Fintype.card_eq_zero

𝗇 𝔔 (r.factorial * (n.descFactorial r : ℝ))⁻¹
theorem normalized_monomial_derivative_sample_sum (σ : 𝔡)
    m (Y : 𝕬) (hrn : r ≤ n) :
     𝔔 * 𝔨 =
      ∑ S : 𝔗, if S.card = r then
        𝔇 *
          (𝔏 * 𝔈)
        else 0 := by
  classical
  rw [monomial_derivative_sample_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [card_equiv_fin_subset]
  split_ifs with h
  · rw [h]
    field_simp
  · simp

𝗇 𝔊 fun i => 𝔯 ω
𝗃 𝕲 ∑ e : 𝔎, 𝕯 ἀ m 𝔊
/-- The derivative-defined distinct-sample expression at any expansion point. -/
def derivativeLiftAt (R : ℕ) (f : 𝔖 → ℝ)
    (m : 𝔖) (Y : 𝔉) (ω : Ω) : ℝ :=
  ∑ r ∈ Finset.range $ R + 1 ,
     𝚐₂ * 𝕲 f

section

variable (σ : 𝔡)
    (Y : 𝔉)
    (m)

𝗇 𝔦 Finset.range $ q + 1
𝗃 𝕵 derivativeLiftAt ἀ (RoughRegime.PolynomialDerivatives.monomial σ) m Y ω
𝗇 𝔴 𝕵 q
/-- A monomial lift agrees exactly with the centered derivative expansion at its degree. -/
theorem monomialLift_eq_derivativeLiftAt
    (hqn : q ≤ n) ω :
    RoughRegime.Upper.monomialLift σ 𝔓 ω =
      𝔴 := by
  classical
  rw [monomialLift_centering σ Y m hqn ω]
  have hexp r (hr : r ∈ 𝔦) :=
    normalized_monomial_derivative_sample_sum σ m (fun j => Y j ω)
      $ (Nat.le_of_lt_succ $ Finset.mem_range.mp hr ).trans hqn
  calc
    _ = ∑ r ∈ 𝔦, ∑ S : 𝔗,
        if S.card = r then 𝔇 *
          𝔱 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      have hS : S.card ∈ 𝔦 := by
        apply Finset.mem_range.mpr
        have hcard := S.card_le_univ
        simp at hcard
        omega
      simp [hS]
    𝔠 := Finset.sum_congr rfl fun r hr => (hexp r hr).symm

theorem derivativeLiftAt_monomial_stable
    (hqR : q ≤ R) ω :
    𝕵 R =
      𝔴 := by
  classical
  symm
  apply Finset.sum_subset $ Finset.range_mono $ Nat.add_le_add_right hqR 1
  intro r _ hr
  have hqr : q < r := by
    simp_all
  have hzero (e : 𝔎) :=
    RoughRegime.PolynomialDerivatives.monomial_iteratedFDeriv_above_degree σ m
      𝔊 hqr
  simp only [hzero, Finset.sum_const_zero, mul_zero]

end

𝗇 𝔑 𝘣₁
𝗇 𝔚 𝙩₁
𝗇 𝔭 derivativeLiftAt R 𝔑 m Y ω
𝗇 𝔵 RoughRegime.PolynomialDerivatives.monomial $ RoughRegime.Upper.exponentCoordinates α
theorem derivativeLiftAt_polynomial_monomial_sum
    R (F : 𝔚) (Y : 𝔉)
    m ω :
    𝔭 =
      ∑ α ∈ F.support, F.coeff α * derivativeLiftAt R
        𝔵 m Y ω := by
  classical
  unfold derivativeLiftAt
  have hstep r :
       𝔔 * 𝕲 𝔑 =
      ∑ α ∈ F.support, F.coeff α *
        ( 𝔔 * 𝕲 𝔵 ) := by
    simp_rw [RoughRegime.PolynomialDerivatives.polynomial_iteratedFDeriv_monomial_sum]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.mul_sum]
    ring
  simp_rw [hstep]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  exact 𝘟₂

/-- The monomial-defined unbiased lift equals the exact derivative-defined lift at
every expansion point. In particular it is invariant under centering the observations. -/
theorem polynomialLift_eq_derivativeLiftAt
    (F : 𝔚) (Y : 𝔉) m
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n) ω :
    RoughRegime.Upper.polynomialLift F 𝔓 ω =
      𝔭 := by
  classical
  rw [derivativeLiftAt_polynomial_monomial_sum]
  apply Finset.sum_congr rfl
  intro α hα
  congr 1
  have hqR : Fintype.card (RoughRegime.Upper.ExponentSlots α) ≤ R := by
    rw [RoughRegime.Upper.exponentSlots_card]
    exact (MvPolynomial.le_totalDegree hα).trans hdeg
  rw [derivativeLiftAt_monomial_stable _ Y m hqR ω]
  exact monomialLift_eq_derivativeLiftAt _ Y m (hqR.trans hRn) ω

𝗇 𝔢 𝘜₂
theorem derivativeLiftAt_eq_centeredDerivativeLift
    R (F : 𝔚) (Y : 𝔉)
    m ω :
    𝔭 =
      RoughRegime.UpperCovariance.centeredDerivativeLift R F m Y ω := by
  classical
  unfold derivativeLiftAt RoughRegime.UpperCovariance.centeredDerivativeLift
    RoughRegime.UpperCovariance.centeredKernelExpansion
    RoughRegime.UpperCovariance.kernelStatistic RoughRegime.UpperCovariance.kernelSum
  rw [Finset.sum_range_succ']
  simp only [iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.descFactorial_zero, inv_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_embedding_eq,
    Fintype.card_fin, Nat.cast_one, one_mul]
  rw [add_comm]
  congr 1
  exact (Fin.sum_univ_eq_sum_range
    (fun r => ( (𝔢).factorial * (n.descFactorial 𝔢 : ℝ))⁻¹ *
      ∑ e : Fin 𝔢 ↪ Fin n,
        iteratedFDeriv ℝ 𝔢 𝔑 m 𝔊) R).symm

𝗇 𝕰 X j ω - m
𝗇 𝔣 fun j ω => 𝕰
/-- Complete algebraic identity identifying the original coefficient lift with its
centered derivative expansion. The center is arbitrary; no population identity is assumed. -/
theorem polynomialLift_eq_centeredDerivativeLift
    (F : 𝔚) (X : 𝔉) m
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n) :
    RoughRegime.Upper.polynomialLift F X =
      RoughRegime.UpperCovariance.centeredDerivativeLift R F m 𝔣 := by
  funext ω
  have hX : (fun j ω => 𝕰 + m) = X := by
    simp
  rw [← derivativeLiftAt_eq_centeredDerivativeLift]
  rw [← polynomialLift_eq_derivativeLiftAt F 𝔣 m hdeg hRn ω, hX]
