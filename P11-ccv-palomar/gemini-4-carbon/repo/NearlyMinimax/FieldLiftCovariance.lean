module

public import Mathlib
public import RoughRegime.PolynomialDerivatives
public import RoughRegime.Upper

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical RealInnerProductSpace

-- 0. Hilbert-space localization for square-integrable kernel fields (`LocalizationL2`)

namespace NearlyMinimax.LocalizationL2

set_option backward.isDefEq.respectTransparency false

variable {W E : Type*} [MeasurableSpace W]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {M : Measure W} [IsFiniteMeasure M]

theorem integral_sq_le_mass_mul_integral_sq {f : W → ℝ} (hf : MemLp f 2 M) :
    (∫ w, f w ∂M) ^ 2 ≤ M.real Set.univ * ∫ w, f w ^ 2 ∂M := by
  let a := ∫ w, f w ∂M
  let b := M.real Set.univ
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  by_cases hb0 : b = 0
  · simp [Measure.measure_univ_eq_zero.mp ((measureReal_eq_zero_iff).mp hb0)]
  · have hi : Integrable f M := hf.integrable (by norm_num)
    have h1 : Integrable (fun w => b ^ 2 * f w ^ 2 - 2 * a * b * f w) M :=
      (hf.integrable_sq.const_mul (b ^ 2)).sub (hi.const_mul (2 * a * b))
    have hnon : 0 ≤ ∫ w, (b * f w - a) ^ 2 ∂M := integral_nonneg fun _ => sq_nonneg _
    have heq : (fun w => (b * f w - a) ^ 2) = fun w => (b ^ 2 * f w ^ 2 - 2 * a * b * f w) + a ^ 2 :=
      funext fun _ => by ring
    have ha := integral_add h1 (integrable_const (a ^ 2) : Integrable (fun _ : W => a ^ 2) M)
    have hs := integral_sub (hf.integrable_sq.const_mul (b ^ 2)) (hi.const_mul (2 * a * b))
    change (∫ w, (b ^ 2 * f w ^ 2 - 2 * a * b * f w) + a ^ 2 ∂M) = _ at ha
    change (∫ w, b ^ 2 * f w ^ 2 - 2 * a * b * f w ∂M) = _ at hs
    rw [heq, ha, hs, integral_const_mul, integral_const_mul, integral_const, smul_eq_mul] at hnon
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    nlinarith [show a = ∫ w, f w ∂M from rfl, show b = M.real Set.univ from rfl]

private lemma integral_eq_sum_fibers {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : ℕ} (b : W → Fin q) (hb : Measurable b) {f : W → F} (hf : Integrable f M) :
    (∫ w, f w ∂M) = ∑ c : Fin q, ∫ w in {v | b v = c}, f w ∂M := by
  have hB (c : Fin q) : MeasurableSet {v | b v = c} := measurableSet_eq_fun hb measurable_const
  calc (∫ w, f w ∂M)
    _ = ∫ w, ∑ c : Fin q, ({v | b v = c} : Set W).indicator f w ∂M :=
        integral_congr_ae <| Filter.Eventually.of_forall fun w => by
          change f w = ∑ c : Fin q, ({v | b v = c} : Set W).indicator f w
          rw [Finset.sum_eq_single (b w)]
          · simp
          · intro c _ hc; simp [Set.indicator, Ne.symm hc]
          · exact fun h => (h (Finset.mem_univ (b w))).elim
    _ = ∑ c : Fin q, ∫ w, ({v | b v = c} : Set W).indicator f w ∂M :=
        integral_finsetSum _ fun c _ => hf.indicator (hB c)
    _ = _ := Finset.sum_congr rfl fun c _ => integral_indicator (hB c)

private theorem weighted_field_memLp_two (ν : W → ℝ) (hν : MemLp ν 2 M)
    (K : W → E) (hK : AEStronglyMeasurable K M)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᵐ w ∂M, ‖K w‖ ≤ C) :
    MemLp (fun w => ν w • K w) 2 M := by
  refine (hν.const_mul C).of_le (hν.aestronglyMeasurable.smul hK) ?_
  filter_upwards [hbound] with w hw
  rw [norm_smul, norm_mul, Real.norm_of_nonneg hC, mul_comm C]
  exact mul_le_mul_of_nonneg_left hw (norm_nonneg _)

private lemma inner_integral_right (x : E) {f : W → E} (hf : Integrable f M) :
    ⟪x, ∫ w, f w ∂M⟫ = ∫ w, ⟪x, f w⟫ ∂M :=
  ((innerSL ℝ x).integral_comp_comm hf).symm

private theorem weighted_partition_localization_bound {q : ℕ}
    (b : W → Fin q) (hb : Measurable b) (ν : W → ℝ) (hν : MemLp ν 2 M)
    (K : W → E) (hK : AEStronglyMeasurable K M)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᵐ w ∂M, ‖K w‖ ≤ C)
    (horth : ∀ w v, b w ≠ b v → ⟪K w, K v⟫ = 0)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    ‖∫ w, ν w • K w ∂M‖ ^ 2 ≤ L * ∫ w, ν w ^ 2 * ‖K w‖ ^ 2 ∂M := by
  let F (w : W) := ν w • K w
  have hFlp : MemLp F 2 M := weighted_field_memLp_two ν hν K hK C hC hbound
  have hFint : Integrable F M := hFlp.integrable (by norm_num)
  have hB (c : Fin q) : MeasurableSet {w | b w = c} := measurableSet_eq_fun hb measurable_const
  let I (c : Fin q) : E := ∫ w in {w | b w = c}, F w ∂M
  have hIorth {c d : Fin q} (hcd : c ≠ d) : ⟪I c, I d⟫ = 0 := by
    dsimp [I]
    rw [← integral_indicator (hB d), inner_integral_right _ (hFint.indicator (hB d))]
    refine integral_eq_zero_of_ae <| Filter.Eventually.of_forall fun v => ?_
    change ⟪∫ w in {w | b w = c}, F w ∂M, ({w | b w = d} : Set W).indicator F v⟫ = 0
    rw [real_inner_comm, ← integral_indicator (hB c), inner_integral_right _ (hFint.indicator (hB c))]
    refine integral_eq_zero_of_ae <| Filter.Eventually.of_forall fun w => ?_
    change ⟪({w | b w = d} : Set W).indicator F v, ({w | b w = c} : Set W).indicator F w⟫ = 0
    by_cases hv : v ∈ ({w | b w = d} : Set W) <;> by_cases hw : w ∈ ({w | b w = c} : Set W)
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hw]
      simp only [F, real_inner_smul_left, real_inner_smul_right,
        horth v w (by change b v = d at hv; change b w = c at hw; rw [hv, hw]; exact hcd.symm), mul_zero]
    · simp [Set.indicator_of_notMem hw]
    · simp [Set.indicator_of_notMem hv]
    · simp [Set.indicator_of_notMem hv]
  have hsum : ‖∑ c : Fin q, I c‖ ^ 2 = ∑ c : Fin q, ‖I c‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_sum, Finset.sum_eq_single c (fun d _ hdc => hIorth hdc.symm) fun h => (h (Finset.mem_univ c)).elim]
    exact real_inner_self_eq_norm_sq _
  rw [integral_eq_sum_fibers b hb hFint]; change ‖∑ c : Fin q, I c‖ ^ 2 ≤ _
  rw [hsum]
  have hnorm_sum := (integral_eq_sum_fibers b hb hFlp.norm.integrable_sq).symm
  simp only [F, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hnorm_sum
  rw [← hnorm_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have hcauchy : ‖I c‖ ^ 2 ≤ (M.restrict {w | b w = c}).real Set.univ * ∫ w in {w | b w = c}, ‖F w‖ ^ 2 ∂M :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2).trans
      (integral_sq_le_mass_mul_integral_sq (hFlp.restrict _).norm)
  rw [measureReal_restrict_apply_univ] at hcauchy
  simpa only [F, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using
    hcauchy.trans (mul_le_mul_of_nonneg_right (hL c) (integral_nonneg fun _ => sq_nonneg _))

theorem toLp_norm_sq_eq_integral_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with ω hω
  rw [hω]; simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem toLp_inner_eq_zero_of_disjoint {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hdisjoint : ∀ᵐ ω ∂μ, f ω * g ω = 0) :
    ⟪hf.toLp f, hg.toLp g⟫ = 0 := by
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp, hdisjoint] with ω hfω hgω hω
  change inner ℝ ((hf.toLp f) ω) ((hg.toLp g) ω) = 0
  rw [hfω, hgω]; simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using hω

theorem weighted_kernel_series_localization_bound {D q : ℕ}
    (b : W → Fin q) (hb : Measurable b) (ν : W → ℝ) (hν : MemLp ν 2 M)
    (K : Fin D → W → E) (hK : ∀ r, AEStronglyMeasurable (K r) M)
    (C : Fin D → ℝ) (hC : ∀ r, 0 ≤ C r) (hbound : ∀ r, ∀ᵐ w ∂M, ‖K r w‖ ≤ C r)
    (horth : ∀ r w v, b w ≠ b v → ⟪K r w, K r v⟫ = 0)
    (δ : Fin D → ℝ) (hδ : ∀ r, 0 ≤ δ r)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    (∑ r : Fin D, δ r * ‖∫ w, ν w • K r w ∂M‖ ^ 2) ≤
      L * ∫ w, ν w ^ 2 * ∑ r : Fin D, δ r * ‖K r w‖ ^ 2 ∂M := by
  have hi (r : Fin D) : Integrable (fun w => ν w ^ 2 * ‖K r w‖ ^ 2) M := by
    simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using
      (weighted_field_memLp_two ν hν (K r) (hK r) (C r) (hC r) (hbound r)).norm.integrable_sq
  have heq : (∫ w, ν w ^ 2 * ∑ r : Fin D, δ r * ‖K r w‖ ^ 2 ∂M) =
      ∑ r : Fin D, δ r * ∫ w, ν w ^ 2 * ‖K r w‖ ^ 2 ∂M := by
    simp_rw [Finset.mul_sum]
    rw [show (fun w => ∑ r : Fin D, ν w ^ 2 * (δ r * ‖K r w‖ ^ 2)) =
      fun w => ∑ r : Fin D, δ r * (ν w ^ 2 * ‖K r w‖ ^ 2) from funext fun _ =>
        Finset.sum_congr rfl fun _ _ => by ring,
      integral_finsetSum _ fun r _ => (hi r).const_mul (δ r)]
    simp_rw [integral_const_mul]
  refine (Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
    (weighted_partition_localization_bound b hb ν hν (K r) (hK r) (C r) (hC r) (hbound r) (horth r) L hL)
    (hδ r)).trans_eq ?_
  rw [heq, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

end NearlyMinimax.LocalizationL2

-- 1. Algebraic centering translation (`LiftTranslation` directly into `LiftL2`)

namespace NearlyMinimax.LiftL2

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def kernelSum {Ω : Type*} {n p r : ℕ}
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) : Ω → ℝ :=
  fun ω => ∑ e : Fin r ↪ Fin n, H (fun i => X (e i) ω)

def kernelStatistic {Ω : Type*} {n p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) : Ω → ℝ :=
  fun ω => (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹) * kernelSum H.toMultilinearMap X ω

def centeredKernelExpansion {Ω : Type*} {n p R : ℕ} (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) : Ω → ℝ :=
  fun ω => c + ∑ r, kernelStatistic (H r) X ω

private lemma normalized_embedding_subtype_restriction {A : Type*} [Fintype A]
    (n : ℕ) (hn : Fintype.card A ≤ n) (S : Finset A) (f : (↥S ↪ Fin n) → ℝ) :
    (n.descFactorial (Fintype.card A) : ℝ)⁻¹ *
        (∑ e : A ↪ Fin n, f ((Function.Embedding.subtype (fun i => i ∈ S)).trans e)) =
      (n.descFactorial S.card : ℝ)⁻¹ * ∑ e : ↥S ↪ Fin n, f e := by
  let C := (S : Set A)ᶜ
  let E1 : (↥S ⊕ C ↪ Fin n) ≃ (A ↪ Fin n) :=
    Equiv.embeddingCongr (Equiv.Set.sumCompl (S : Set A)) (Equiv.refl (Fin n))
  let E2 := Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted (α := ↥S) (β := C) (γ := Fin n)
  have hsum : (∑ e : A ↪ Fin n, f ((Function.Embedding.subtype (fun i => i ∈ S)).trans e)) =
      ((n - S.card).descFactorial (Fintype.card A - S.card) : ℝ) * ∑ e : ↥S ↪ Fin n, f e := by
    calc _ = ∑ e : ↥S ⊕ C ↪ Fin n, f ((Function.Embedding.subtype (fun i => i ∈ S)).trans (E1 e)) :=
            (E1.sum_comp _).symm
      _ = ∑ e : ↥S ⊕ C ↪ Fin n, f (E2 e).1 := Finset.sum_congr rfl fun e _ => congrArg f <|
            Function.Embedding.ext fun i => by
              change e ((Equiv.Set.sumCompl (S : Set A)).symm (i : A)) = e (Sum.inl i)
              rw [Equiv.Set.sumCompl_symm_apply_of_mem (show (i : A) ∈ (S : Set A) from i.property)]; rfl
      _ = ∑ u : Σ e : ↥S ↪ Fin n, C ↪ ↥(Set.range e)ᶜ, f u.1 := E2.sum_comp (fun u => f u.1)
      _ = ∑ e : ↥S ↪ Fin n, ((n - S.card).descFactorial (Fintype.card A - S.card) : ℝ) * f e := by
            rw [Fintype.sum_sigma]
            refine Finset.sum_congr rfl fun e _ => ?_
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_embedding_eq]
            have hc1 : Fintype.card ↥(Set.range e)ᶜ = n - S.card := by
              change Fintype.card {j : Fin n // ¬j ∈ Set.range e} = _
              rw [Fintype.card_subtype_compl, ← Fintype.card_congr e.toEquivRange]; simp
            have hc2 : Fintype.card C = Fintype.card A - S.card := by
              change Fintype.card {i : A // ¬i ∈ S} = _
              rw [Fintype.card_subtype_compl]; simp
            rw [hc1, hc2]
      _ = _ := (Finset.mul_sum ..).symm
  rw [hsum, ← mul_assoc]
  congr 1
  have hq : (n.descFactorial (Fintype.card A) : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.mpr hn).ne'
  have hr : (n.descFactorial S.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.mpr (S.card_le_univ.trans hn)).ne'
  field_simp
  exact_mod_cast Nat.descFactorial_mul_descFactorial S.card_le_univ

private lemma range_embedding_of_subset_equiv {A B : Type*} [Fintype A] [Fintype B]
    (S : Finset B) (a : A ≃ ↥S) :
    Set.range (a.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ S))) = S := by
  ext j; constructor
  · rintro ⟨i, rfl⟩; exact (a i).property
  · intro hj; obtain ⟨i, hi⟩ := a.surjective ⟨j, hj⟩; exact ⟨i, congrArg Subtype.val hi⟩

private lemma normalized_monomial_derivative_sample_sum {n p q r : ℕ} (σ : Fin q → Fin p)
    (m : Fin p → ℝ) (Y : Fin n → Fin p → ℝ) (hrn : r ≤ n) :
    (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ * ∑ e : Fin r ↪ Fin n,
      iteratedFDeriv ℝ r (RoughRegime.PolynomialDerivatives.monomial σ) m (fun i => Y (e i))) =
      ∑ S : Finset (Fin q), if S.card = r then
        (∏ j ∈ Sᶜ, m (σ j)) * ((n.descFactorial S.card : ℝ)⁻¹ * ∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) (σ i))
      else 0 := by
  let g : (Σ S : Finset (Fin q), Fin r ≃ ↥S) → (Fin r ↪ Fin q) :=
    fun u => u.2.toEmbedding.trans (Function.Embedding.subtype (fun i => i ∈ u.1))
  have hg : Function.Bijective g := ⟨fun ⟨S, a⟩ ⟨T, b⟩ h => by
      have hST : S = T := Finset.coe_injective <| by
        rw [← range_embedding_of_subset_equiv S a, ← range_embedding_of_subset_equiv T b]
        exact congrArg (fun e : Fin r ↪ Fin q => Set.range (e : Fin r → Fin q)) h
      subst T
      congr; exact Equiv.ext fun i => Subtype.ext (congrArg (fun e : Fin r ↪ Fin q => e i) h),
    fun e => ⟨⟨Finset.univ.map e, e.toEquivRange.trans (Set.equivOfEq (by ext j; simp))⟩,
      Function.Embedding.ext fun _ => rfl⟩⟩
  have hsum_emb (f : (Fin r ↪ Fin q) → ℝ) :
      (∑ e : Fin r ↪ Fin q, f e) = ∑ S : Finset (Fin q), ∑ a : Fin r ≃ ↥S, f (g ⟨S, a⟩) := by
    rw [← (Equiv.ofBijective g hg).sum_comp f, Fintype.sum_sigma]
    rfl
  simp_rw [RoughRegime.PolynomialDerivatives.monomial_iteratedFDeriv]
  rw [Finset.sum_comm, hsum_emb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hsamp (a : Fin r ≃ ↥S) :
      (∑ e : Fin r ↪ Fin n, ∏ j : Fin q, if h : j ∈ Set.range (g ⟨S, a⟩) then
        Y (e ((g ⟨S, a⟩).toEquivRange.symm ⟨j, h⟩)) (σ j) else m (σ j)) =
      (∏ j ∈ Sᶜ, m (σ j)) * (∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) (σ i)) := by
    have hrepl (e : Fin r ↪ Fin n) :
        (∏ j : Fin q, if h : j ∈ Set.range (g ⟨S, a⟩) then
          Y (e ((g ⟨S, a⟩).toEquivRange.symm ⟨j, h⟩)) (σ j) else m (σ j)) =
        (∏ i : Fin r, Y (e i) (σ (a i))) * ∏ j ∈ Sᶜ, m (σ j) := by
      let b := g ⟨S, a⟩
      let fn (j : Fin q) := if h : j ∈ Set.range b then Y (e (b.toEquivRange.symm ⟨j, h⟩)) (σ j) else m (σ j)
      have hb : Set.range b = (S : Set (Fin q)) := range_embedding_of_subset_equiv S a
      change (∏ j : Fin q, fn j) = _
      rw [← Finset.prod_mul_prod_compl S fn]; congr 1
      · rw [← Finset.prod_coe_sort S fn, ← a.prod_comp (fun j : ↥S => fn j)]
        refine Finset.prod_congr rfl fun i _ => ?_
        have hi : (a i : Fin q) ∈ Set.range b := ⟨i, rfl⟩
        simp only [fn, dite_eq_left hi]; change Y (e (b.toEquivRange.symm ⟨b i, _⟩)) (σ (a i)) = _; simp
      · refine Finset.prod_congr rfl fun j hj => dite_eq_right ?_
        rw [hb]; simpa using Finset.mem_compl.mp hj
    simp_rw [hrepl]; rw [← Finset.sum_mul, mul_comm]; congr 1
    let E : (Fin r ↪ Fin n) ≃ (↥S ↪ Fin n) := Equiv.embeddingCongr a (Equiv.refl (Fin n))
    rw [← E.sum_comp (fun e : ↥S ↪ Fin n => ∏ i : ↥S, Y (e i) (σ i))]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← a.prod_comp]
    exact Finset.prod_congr rfl fun i _ => by simp [E, Equiv.embeddingCongr, Function.Embedding.congr_apply]
  simp_rw [hsamp]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  by_cases h : S.card = r
  · have hcard : Fintype.card (Fin r ≃ ↥S) = r.factorial := by
      rw [Fintype.card_equiv (Fintype.equivOfCardEq (by simpa using h.symm))]; simp
    rw [if_pos h, hcard, h]
    have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
    have hdesc : (n.descFactorial r : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.mpr hrn).ne'
    field_simp
  · have hempty : IsEmpty (Fin r ≃ ↥S) := ⟨fun a => h (by simpa using (Fintype.card_congr a).symm)⟩
    rw [if_neg h, Fintype.card_eq_zero]; simp

theorem polynomialLift_centering_l2 {Ω : Type*} {n p R : ℕ}
    (F : MvPolynomial (Fin p) ℝ) (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n) :
    RoughRegime.Upper.polynomialLift F X =
      centeredKernelExpansion (MvPolynomial.eval m F)
        (fun r : Fin R => iteratedFDeriv ℝ (r.val + 1) (fun x => MvPolynomial.eval x F) m)
        (fun j ω => X j ω - m) := by
  funext ω
  let Y (j : Fin n) := X j ω - m
  let liftAt (K : ℕ) (f : (Fin p → ℝ) → ℝ) : ℝ :=
    ∑ r ∈ Finset.range (K + 1), (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ *
      ∑ e : Fin r ↪ Fin n, iteratedFDeriv ℝ r f m (fun i => Y (e i)))
  have hmono_eq {q : ℕ} (σ : Fin q → Fin p) (hqR : q ≤ R) :
      RoughRegime.Upper.monomialLift σ X ω = liftAt R (RoughRegime.PolynomialDerivatives.monomial σ) := by
    have hqn : q ≤ n := hqR.trans hRn
    have h1 : RoughRegime.Upper.monomialLift σ X ω =
        ∑ S : Finset (Fin q), (∏ i ∈ Sᶜ, m (σ i)) *
          ((n.descFactorial S.card : ℝ)⁻¹ * ∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) (σ i)) := by
      have hXY : X = fun j t => (X j t - m) + m := funext fun j => funext fun t => (sub_add_cancel _ _).symm
      conv_lhs => rw [hXY]
      unfold RoughRegime.Upper.monomialLift
      simp only [Pi.add_apply]
      change (n.descFactorial q : ℝ)⁻¹ * ∑ e : Fin q ↪ Fin n, ∏ i : Fin q, (Y (e i) (σ i) + m (σ i)) = _
      simp_rw [Fintype.prod_add (fun i => Y _ (σ i)) (fun i => m (σ i))]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun S _ => ?_
      simp_rw [(Finset.prod_coe_sort S _).symm]
      rw [← Finset.sum_mul]
      have hrest : (n.descFactorial q : ℝ)⁻¹ * (∑ e : Fin q ↪ Fin n, ∏ i : ↥S, Y (e i) (σ i)) =
          (n.descFactorial S.card : ℝ)⁻¹ * (∑ e : ↥S ↪ Fin n, ∏ i : ↥S, Y (e i) (σ i)) := by
        simpa using normalized_embedding_subtype_restriction n (by simpa using hqn) S
          fun e : ↥S ↪ Fin n => ∏ i : ↥S, Y (e i) (σ i)
      linear_combination (∏ i ∈ Sᶜ, m (σ i)) * hrest
    have h2 : liftAt q (RoughRegime.PolynomialDerivatives.monomial σ) = liftAt R (RoughRegime.PolynomialDerivatives.monomial σ) := by
      refine Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hqR 1)) fun r _ hr => ?_
      simp only [Finset.mem_range] at hr
      have hqr : q < r := by omega
      simp [RoughRegime.PolynomialDerivatives.monomial_iteratedFDeriv_above_degree σ m _ hqr]
    rw [h1, ← h2]; dsimp only [liftAt]
    symm
    rw [Finset.sum_congr rfl fun r hr => normalized_monomial_derivative_sample_sum σ m Y
      ((Nat.le_of_lt_succ (Finset.mem_range.mp hr)).trans hqn), Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hS : S.card ∈ Finset.range (q + 1) := Finset.mem_range.mpr (by have := S.card_le_univ; simp at this; omega)
    simp [hS]
  have hpoly_sum : liftAt R (fun x => MvPolynomial.eval x F) =
      ∑ α ∈ F.support, F.coeff α * liftAt R (RoughRegime.PolynomialDerivatives.monomial (RoughRegime.Upper.exponentCoordinates α)) := by
    dsimp only [liftAt]
    have hstep (r : ℕ) : (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ *
        ∑ e : Fin r ↪ Fin n, iteratedFDeriv ℝ r (fun x => MvPolynomial.eval x F) m (fun i => Y (e i))) =
        ∑ α ∈ F.support, F.coeff α * (((r.factorial : ℝ) * (n.descFactorial r : ℝ))⁻¹ *
          ∑ e : Fin r ↪ Fin n, iteratedFDeriv ℝ r
            (RoughRegime.PolynomialDerivatives.monomial (RoughRegime.Upper.exponentCoordinates α)) m (fun i => Y (e i))) := by
      simp_rw [RoughRegime.PolynomialDerivatives.polynomial_iteratedFDeriv_monomial_sum]
      rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp_rw [hstep]; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => (Finset.mul_sum ..).symm
  have hlhs : RoughRegime.Upper.polynomialLift F X ω = liftAt R (fun x => MvPolynomial.eval x F) := by
    rw [hpoly_sum]; unfold RoughRegime.Upper.polynomialLift
    refine Finset.sum_congr rfl fun α hα => congrArg (F.coeff α * ·) (hmono_eq _ ?_)
    rw [RoughRegime.Upper.exponentSlots_card]; exact (MvPolynomial.le_totalDegree hα).trans hdeg
  rw [hlhs]; dsimp only [liftAt, centeredKernelExpansion, kernelStatistic, kernelSum]
  rw [Finset.sum_range_succ']
  simp only [iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.descFactorial_zero, Nat.cast_one,
    one_mul, inv_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_embedding_eq,
    Fintype.card_fin]
  rw [add_comm]; congr 1
  exact (Fin.sum_univ_eq_sum_range
    (fun r => (((r + 1).factorial : ℝ) * (n.descFactorial (r + 1) : ℝ))⁻¹ *
      ∑ e : Fin (r + 1) ↪ Fin n,
        iteratedFDeriv ℝ (r + 1) (fun x => MvPolynomial.eval x F) m (fun i => Y (e i))) R).symm

-- 2. Square-integrable multilinear kernels & centering contraction (`LiftL2`)

section ProbabilityL2
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem independent_finset_product_integrable [IsProbabilityMeasure μ]
    {ι : Type*} [DecidableEq ι] {Y : ι → Ω → ℝ}
    (hind : iIndepFun Y μ) (hmeas : ∀ i, Measurable (Y i))
    (hint : ∀ i, Integrable (Y i) μ) (s : Finset ι) :
    Integrable (fun ω => ∏ i ∈ s, Y i ω) μ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hpfun : (∏ j ∈ s, Y j) = fun ω => ∏ j ∈ s, Y j ω := funext fun _ => by simp
    have hprod := (hind.indepFun_finsetProd_of_notMem hmeas hi).symm.integrable_mul (hint i) (hpfun.symm ▸ ih)
    rw [hpfun] at hprod
    simpa only [Finset.prod_insert hi] using (show Integrable (fun ω => Y i ω * ∏ j ∈ s, Y j ω) μ from hprod)

theorem coordinate_monomial_memLp_two [IsProbabilityMeasure μ]
    {n p r : ℕ} (e : Fin r ↪ Fin n) (σ : Fin r → Fin p)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j)) (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (fun ω => ∏ i, X (e i) ω (σ i)) 2 μ := by
  have hm_prod : Measurable fun ω => ∏ i, X (e i) ω (σ i) :=
    Finset.measurable_prod Finset.univ fun i _ => (measurable_pi_apply (σ i)).comp (hmeas (e i))
  refine (memLp_two_iff_integrable_sq hm_prod.aestronglyMeasurable).mpr ?_
  have hsqind : iIndepFun (fun i ω => X (e i) ω (σ i) ^ 2) μ :=
    ((hind.precomp e.injective).comp (fun i (v : Fin p → ℝ) => v (σ i)) fun i => measurable_pi_apply (σ i)).comp
      (fun _ (y : ℝ) => y ^ 2) fun _ => measurable_id.pow_const 2
  simpa only [Finset.prod_pow] using independent_finset_product_integrable hsqind
    (fun i => ((measurable_pi_apply (σ i)).comp (hmeas (e i))).pow_const 2)
    (fun i => (hL2 (e i) (σ i)).integrable_sq) Finset.univ

private theorem coordinate_product_integral_eq_zero [IsProbabilityMeasure μ]
    {A : Type*} [Fintype A] {n p : ℕ}
    (s : A → Fin n) (σ : A → Fin p) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0)
    (k : A) (hk : ∀ i, s i = s k → i = k) :
    (∫ ω, ∏ i, X (s i) ω (σ i) ∂μ) = 0 := by
  let F (j : Fin n) (v : Fin p → ℝ) : ℝ := ∏ i : A with s i = j, v (σ i)
  have hF (j : Fin n) : Measurable (F j) := Finset.measurable_prod _ fun i _ => measurable_pi_apply (σ i)
  have hfun : (fun ω => ∏ i, X (s i) ω (σ i)) = fun ω => ∏ j, (F j ∘ X j) ω := funext fun ω => by
    rw [← Finset.prod_fiberwise (Finset.univ : Finset A) s (fun i => X (s i) ω (σ i))]
    exact Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
  rw [hfun, (hind.comp F hF).integral_fun_prod_eq_prod_integral fun j => ((hF j).comp (hmeas j)).aestronglyMeasurable]
  refine Finset.prod_eq_zero (Finset.mem_univ (s k)) ?_
  have hflt : (Finset.univ.filter fun i : A => s i = s k) = {k} := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hk i, fun h => by rw [h]⟩
  dsimp [F]; rw [hflt]; simpa using hmean (s k) (σ k)

theorem multilinear_coordinate_expansion {p r : ℕ}
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ) (v : Fin r → Fin p → ℝ) :
    H v = ∑ σ : Fin r → Fin p, H (fun i => Pi.single (σ i) 1) * ∏ i, v i (σ i) := by
  have hv : v = fun i => ∑ a : Fin p, v i a • (Pi.single a (1 : ℝ) : Fin p → ℝ) :=
    funext fun i => funext fun a => by simp [Pi.single_apply]
  calc H v = H (fun i => ∑ a : Fin p, v i a • (Pi.single a (1 : ℝ) : Fin p → ℝ)) := congrArg H hv
    _ = ∑ σ : Fin r → Fin p, H (fun i => v i (σ i) • (Pi.single (σ i) (1 : ℝ) : Fin p → ℝ)) := H.map_sum _
    _ = _ := Finset.sum_congr rfl fun σ _ => by rw [H.map_smul_univ]; simp [mul_comm]

theorem multilinear_kernel_memLp_two [IsProbabilityMeasure μ]
    {n p r : ℕ} (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (e : Fin r ↪ Fin n) (X : Fin n → Ω → Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (fun ω => H (fun i => X (e i) ω)) 2 μ := by
  rw [show (fun ω => H (fun i => X (e i) ω)) = fun ω => ∑ σ : Fin r → Fin p,
    H (fun i => Pi.single (σ i) 1) * ∏ i, X (e i) ω (σ i) from funext fun _ => multilinear_coordinate_expansion H _]
  exact memLp_finsetSum Finset.univ fun σ _ => (coordinate_monomial_memLp_two e σ X hind hmeas hL2).const_mul _

private theorem kernelSum_integral_eq_zero [IsProbabilityMeasure μ]
    {n p r : ℕ} (hr : 0 < r)
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    (∫ ω, kernelSum H X ω ∂μ) = 0 := by
  unfold kernelSum
  rw [integral_finsetSum _ fun e _ => (multilinear_kernel_memLp_two H e X hind hmeas hL2).integrable (by norm_num)]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [show (fun ω => H (fun i => X (e i) ω)) = fun ω => ∑ σ : Fin r → Fin p,
    H (fun i => Pi.single (σ i) 1) * ∏ i, X (e i) ω (σ i) from funext fun _ => multilinear_coordinate_expansion H _]
  rw [integral_finsetSum _ fun σ _ => ((coordinate_monomial_memLp_two e σ X hind hmeas hL2).integrable (by norm_num)).const_mul _]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [integral_const_mul, coordinate_product_integral_eq_zero e σ X hind hmeas hmean ⟨0, hr⟩ (fun _ hi => e.injective hi), mul_zero]

private theorem kernelSum_covariance_same_range [IsProbabilityMeasure μ]
    {n p r t : ℕ} (hr : 0 < r) (ht : 0 < t)
    (H : MultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (G : MultilinearMap ℝ (fun _ : Fin t => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    covariance (kernelSum H X) (kernelSum G X) μ =
      ∑ e : Fin r ↪ Fin n, ∑ f : Fin t ↪ Fin n with Set.range e.toFun = Set.range f.toFun,
        ∫ ω, H (fun i => X (e i) ω) * G (fun i => X (f i) ω) ∂μ := by
  have hpair_int (e : Fin r ↪ Fin n) (f : Fin t ↪ Fin n) :
      Integrable (fun ω => H (fun i => X (e i) ω) * G (fun i => X (f i) ω)) μ :=
    ((multilinear_kernel_memLp_two H e X hind hmeas hL2).integrable_mul
      (multilinear_kernel_memLp_two G f X hind hmeas hL2)).congr (Filter.Eventually.of_forall fun _ => rfl)
  have hzero_left {a b : ℕ} (Ha : MultilinearMap ℝ (fun _ : Fin a => Fin p → ℝ) ℝ)
      (Gb : MultilinearMap ℝ (fun _ : Fin b => Fin p → ℝ) ℝ) (ea : Fin a ↪ Fin n) (fb : Fin b ↪ Fin n)
      (k : Fin a) (hk : ea k ∉ Set.range fb) :
      (∫ ω, Ha (fun i => X (ea i) ω) * Gb (fun i => X (fb i) ω) ∂μ) = 0 := by
    have hexp (ω : Ω) : Ha (fun i => X (ea i) ω) * Gb (fun i => X (fb i) ω) =
        ∑ σ : Fin a → Fin p, ∑ τ : Fin b → Fin p,
          (Ha (fun i => Pi.single (σ i) 1) * Gb (fun i => Pi.single (τ i) 1)) *
            ((∏ i, X (ea i) ω (σ i)) * (∏ i, X (fb i) ω (τ i))) := by
      rw [multilinear_coordinate_expansion Ha, multilinear_coordinate_expansion Gb, Finset.sum_mul]
      exact Finset.sum_congr rfl fun σ _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    have hc_int (σ : Fin a → Fin p) (τ : Fin b → Fin p) :
        Integrable (fun ω => (∏ i, X (ea i) ω (σ i)) * (∏ i, X (fb i) ω (τ i))) μ :=
      ((coordinate_monomial_memLp_two ea σ X hind hmeas hL2).integrable_mul
        (coordinate_monomial_memLp_two fb τ X hind hmeas hL2)).congr (Filter.Eventually.of_forall fun _ => rfl)
    simp_rw [hexp]
    rw [integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun τ _ => (hc_int σ τ).const_mul _]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [integral_finsetSum _ fun τ _ => (hc_int σ τ).const_mul _]
    refine Finset.sum_eq_zero fun τ _ => ?_
    have hz0 := coordinate_product_integral_eq_zero (Sum.elim ea fb) (Sum.elim σ τ) X hind hmeas hmean (Sum.inl k)
      fun idx hidx => by cases idx with
        | inl idx => exact congrArg Sum.inl (ea.injective hidx)
        | inr idx => exact (hk ⟨idx, hidx⟩).elim
    rw [integral_const_mul, show (∫ ω, (∏ i, X (ea i) ω (σ i)) * (∏ i, X (fb i) ω (τ i)) ∂μ) = 0 by
      simpa [Fintype.prod_sum_type] using hz0, mul_zero]
  unfold covariance
  rw [kernelSum_integral_eq_zero hr H X hind hmeas hL2 hmean,
    kernelSum_integral_eq_zero ht G X hind hmeas hL2 hmean]
  simp only [sub_zero]; unfold kernelSum
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun e _ => integrable_finsetSum _ fun f _ => hpair_int e f]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_finsetSum _ fun f _ => hpair_int e f]
  symm; refine Finset.sum_subset (Finset.filter_subset _ _) fun f _ hf => ?_
  have hef : Set.range e ≠ Set.range f := by simpa using hf
  by_cases hsub : Set.range e ⊆ Set.range f
  · obtain ⟨_, ⟨k, rfl⟩, hje⟩ := Set.not_subset.mp (fun h => hef (Set.Subset.antisymm hsub h))
    simpa only [mul_comm] using hzero_left G H f e k hje
  · obtain ⟨_, ⟨k, rfl⟩, hjf⟩ := Set.not_subset.mp hsub
    exact hzero_left H G e f k hjf

theorem centeredKernelExpansion_memLp_two [IsProbabilityMeasure μ]
    {n p R : ℕ} (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j)) (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (centeredKernelExpansion c H X) 2 μ :=
  (memLp_const c).add <| memLp_finsetSum Finset.univ fun r _ =>
    (memLp_finsetSum Finset.univ fun e _ => multilinear_kernel_memLp_two (H r).toMultilinearMap e X hind hmeas hL2).const_mul _

theorem centeredKernelExpansion_expectation [IsProbabilityMeasure μ]
    {n p R : ℕ} (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j)) (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    (∫ ω, centeredKernelExpansion c H X ω ∂μ) = c := by
  have hk_L2 (r : Fin R) : MemLp (kernelStatistic (H r) X) 2 μ :=
    (memLp_finsetSum Finset.univ fun e _ => multilinear_kernel_memLp_two (H r).toMultilinearMap e X hind hmeas hL2).const_mul _
  unfold centeredKernelExpansion
  rw [integral_add (integrable_const c) ((memLp_finsetSum Finset.univ fun r _ => hk_L2 r).integrable (by norm_num)),
    integral_const, integral_finsetSum Finset.univ fun r _ => (hk_L2 r).integrable (by norm_num)]
  have hz : (∑ r : Fin R, ∫ ω, kernelStatistic (H r) X ω ∂μ) = 0 := Finset.sum_eq_zero fun r _ => by
    unfold kernelStatistic
    rw [integral_const_mul, kernelSum_integral_eq_zero (Nat.succ_pos r.val) (H r).toMultilinearMap X hind hmeas hL2 hmean, mul_zero]
  simp [hz]

theorem centeredKernelExpansion_variance [IsProbabilityMeasure μ]
    {n p R : ℕ} (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (hsym : ∀ r (σ : Equiv.Perm (Fin (r.val + 1))) v, H r (fun i => v (σ i)) = H r v)
    (X : Fin n → Ω → Fin p → ℝ) (hR : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = 0) :
    variance (centeredKernelExpansion c H X) μ =
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * (n.descFactorial (r.val + 1) : ℝ))⁻¹ *
        ∫ ω, H r (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ^ 2 ∂μ := by
  have hsum_L2 (r : Fin R) : MemLp (kernelSum (H r).toMultilinearMap X) 2 μ :=
    memLp_finsetSum Finset.univ fun e _ => multilinear_kernel_memLp_two (H r).toMultilinearMap e X hind hmeas hL2
  have hstats (r : Fin R) : MemLp (kernelStatistic (H r) X) 2 μ := (hsum_L2 r).const_mul _
  unfold centeredKernelExpansion
  rw [variance_const_add (memLp_finsetSum Finset.univ fun r _ => hstats r).aestronglyMeasurable c,
    variance_fun_sum hstats]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single r]
  · rw [covariance_self (hstats r).aemeasurable]
    let k := r.val + 1
    have hkn : k ≤ n := (Nat.succ_le_of_lt r.isLt).trans hR
    let e₀ := Fin.castLEEmb hkn
    unfold kernelStatistic
    rw [variance_const_mul, ← covariance_self (hsum_L2 r).aemeasurable,
      kernelSum_covariance_same_range (by omega) (by omega) (H r).toMultilinearMap (H r).toMultilinearMap X hind hmeas hL2 hmean]
    simp only [ContinuousMultilinearMap.coe_coe]
    have hsame_perm {e f : Fin k ↪ Fin n} (hef : Set.range f = Set.range e) :
        ∃ σ : Equiv.Perm (Fin k), ∀ i, e (σ i) = f i :=
      ⟨(Equiv.ofInjective f f.injective).trans ((Set.equivOfEq hef).trans (Equiv.ofInjective e e.injective).symm),
        fun i => Equiv.apply_ofInjective_symm e.injective _⟩
    let J_int := ∫ ω, H r (fun i => X (e₀ i) ω) ^ 2 ∂μ
    have hs_inner (e : Fin k ↪ Fin n) :
        (∑ f : Fin k ↪ Fin n with Set.range e.toFun = Set.range f.toFun,
          ∫ ω, H r (fun i => X (e i) ω) * H r (fun i => X (f i) ω) ∂μ) = (k.factorial : ℝ) * J_int := by
      have hflt : Finset.univ.filter (fun f : Fin k ↪ Fin n => Set.range e.toFun = Set.range f.toFun) =
          Finset.univ.filter (fun f : Fin k ↪ Fin n => Set.range f.toFun = Set.range e.toFun) := by
        ext f; simp [eq_comm]
      rw [hflt]
      have hterm (f : Fin k ↪ Fin n) (hf : f ∈ Finset.univ.filter fun f : Fin k ↪ Fin n => Set.range f.toFun = Set.range e.toFun) :
          (∫ ω, H r (fun i => X (e i) ω) * H r (fun i => X (f i) ω) ∂μ) = J_int := by
        obtain ⟨σ, hσ⟩ := hsame_perm (Finset.mem_filter.mp hf).2
        have hH_eq (ω : Ω) : H r (fun i => X (f i) ω) = H r (fun i => X (e i) ω) :=
          (congrArg (H r) (funext fun i => congrArg (fun j => X j ω) (hσ i).symm)).trans (hsym r σ (fun i => X (e i) ω))
        simp_rw [hH_eq, ← pow_two]
        have hid_pi := IdentDistrib.pi (fun i => hid (e i) (e₀ i)) (hind.precomp e.injective) (hind.precomp e₀.injective)
        exact (hid_pi.comp ((H r).cont.pow 2).measurable).integral_eq
      rw [Finset.sum_congr rfl hterm]
      simp only [Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype]
      let g_bij : Equiv.Perm (Fin k) → {f : Fin k ↪ Fin n // Set.range f.toFun = Set.range e.toFun} :=
        fun σ => ⟨σ.toEmbedding.trans e, by ext j; exact ⟨fun ⟨i, hi⟩ => ⟨σ i, hi⟩, fun ⟨i, hi⟩ => ⟨σ.symm i, by simpa using hi⟩⟩⟩
      have hbij : Function.Bijective g_bij := ⟨fun σ τ h => Equiv.ext fun i => e.injective (congrArg (fun f => f.val i) h),
        fun f => by obtain ⟨σ, hσ⟩ := hsame_perm f.property; exact ⟨σ, Subtype.ext (Function.Embedding.ext hσ)⟩⟩
      rw [← Fintype.card_congr (Equiv.ofBijective g_bij hbij), Fintype.card_perm, Fintype.card_fin]
    dsimp only [k] at hs_inner
    simp_rw [hs_inner]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_embedding_eq, Fintype.card_fin]
    have hfac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hdesc : (n.descFactorial k : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.mpr hkn).ne'
    dsimp [J_int, e₀, k]; field_simp
  · intro t _ htr
    unfold kernelStatistic
    rw [covariance_const_mul_left, covariance_const_mul_right,
      kernelSum_covariance_same_range (by omega) (by omega) (H r).toMultilinearMap (H t).toMultilinearMap X hind hmeas hL2 hmean]
    simp only [ContinuousMultilinearMap.coe_coe]
    have hz_sum : (∑ e : Fin (r.val + 1) ↪ Fin n,
        ∑ f : Fin (t.val + 1) ↪ Fin n with Set.range e.toFun = Set.range f.toFun,
          ∫ ω, H r (fun i => X (e i) ω) * H t (fun i => X (f i) ω) ∂μ) = 0 := by
      refine Finset.sum_eq_zero fun e _ => ?_
      have hempty : Finset.univ.filter (fun f : Fin (t.val + 1) ↪ Fin n => Set.range e.toFun = Set.range f.toFun) = ∅ := by
        refine Finset.eq_empty_iff_forall_notMem.mpr fun f hf => htr (Fin.ext ?_)
        have hc := Fintype.card_congr ((Equiv.ofInjective e e.injective).trans
          ((Set.equivOfEq (Finset.mem_filter.mp hf).2).trans (Equiv.ofInjective f f.injective).symm))
        simp only [Fintype.card_fin] at hc; omega
      rw [hempty, Finset.sum_empty]
    change _ * (_ * _) = 0; rw [hz_sum]; ring
  · exact fun h => (h (Finset.mem_univ r)).elim

theorem centerObservations_l2 [IsProbabilityMeasure μ]
    {n p : ℕ} (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    iIndepFun (fun j ω => X j ω - m) μ ∧
      (∀ j, Measurable (fun ω => X j ω - m)) ∧
      (∀ i j, IdentDistrib (fun ω => X i ω - m) (fun ω => X j ω - m) μ μ) ∧
      (∀ j a, MemLp (fun ω => X j ω a - m a) 2 μ) ∧
      (∀ j a, ∫ ω, X j ω a - m a ∂μ = 0) := by
  refine ⟨hind.comp (fun _ (v : Fin p → ℝ) => v - m) fun _ => measurable_id.sub_const m,
    fun j => (hmeas j).sub_const m,
    fun i j => (hid i j).comp (measurable_id.sub_const m),
    fun j a => (hL2 j a).sub (memLp_const (m a)), fun j a => ?_⟩
  rw [integral_sub ((hL2 j a).integrable (by norm_num)) (integrable_const (m a)), integral_const, hmean]; simp

private lemma product_kernel_square_integrable_l2 [IsProbabilityMeasure μ]
    {p r : ℕ} (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (A : Fin r → Ω → Fin p → ℝ) (hm : ∀ i, Measurable (A i))
    (hL2 : ∀ i a, MemLp (fun ω => A i ω a) 2 μ) :
    Integrable (fun ω : Fin r → Ω => H (fun i => A i (ω i)) ^ 2) (Measure.pi fun _ => μ) :=
  (multilinear_kernel_memLp_two H.toMultilinearMap (Function.Embedding.refl _)
    (fun i (ω : Fin r → Ω) => A i (ω i))
    (iIndepFun_pi fun i => (hm i).aemeasurable)
    (fun i => (hm i).comp (measurable_pi_apply i))
    fun i a => (hL2 i a).comp_measurePreserving (measurePreserving_eval (fun _ : Fin r => μ) i)).integrable_sq

theorem independent_centering_square_le_l2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p r : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin r => Fin p → ℝ) ℝ)
    (X : Fin r → Ω → Fin p → ℝ) (hm : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ i a, MemLp (fun ω => X i ω a) 2 μ)
    (m : Fin p → ℝ) (hmean : ∀ i a, ∫ ω, X i ω a ∂μ = m a) :
    (∫ ω, H (fun i => X i ω - m) ^ 2 ∂μ) ≤ ∫ ω, H (fun i => X i ω) ^ 2 ∂μ := by
  have hiid {q : ℕ} (Hq : ContinuousMultilinearMap ℝ (fun _ : Fin q => Fin p → ℝ) ℝ)
      (Z : Ω → Fin p → ℝ) (hmZ : Measurable Z) (hL2Z : ∀ a, MemLp (fun ω => Z ω a) 2 μ)
      (hmeanZ : ∀ a, ∫ ω, Z ω a ∂μ = m a) :
      (∫ ω, Hq (fun j => Z (ω j) - m) ^ 2 ∂Measure.pi fun _ : Fin q => μ) ≤
        ∫ ω, Hq (fun j => Z (ω j)) ^ 2 ∂Measure.pi fun _ : Fin q => μ := by
    induction q with
    | zero =>
      refine le_of_eq (integral_congr_ae <| Filter.Eventually.of_forall fun ω =>
        congrArg (· ^ 2) (congrArg Hq (funext fun j => Fin.elim0 j)))
    | succ q ih =>
      let Y (ω : Ω) := Z ω - m
      have hY : Measurable Y := hmZ.sub measurable_const
      have hYlp (a : Fin p) : MemLp (fun ω => Y ω a) 2 μ := (hL2Z a).sub (memLp_const (m a))
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q + 1) => Ω) 0
      have he := measurePreserving_piFinSuccAbove (fun _ : Fin (q + 1) => μ) 0
      have hpi_succ (fn : (Fin (q + 1) → Ω) → ℝ) (hfn : Integrable fn (Measure.pi fun _ => μ)) :
          (∫ x, fn x ∂Measure.pi fun _ : Fin (q + 1) => μ) =
            ∫ x, ∫ y, fn (Fin.cons x y) ∂Measure.pi (fun _ : Fin q => μ) ∂μ := by
        have hfn' : Integrable (fn ∘ e.symm) (μ.prod (Measure.pi fun _ : Fin q => μ)) :=
          (he.symm e).integrable_comp_of_integrable hfn
        rw [← (he.symm e).integral_comp' fn]
        change (∫ x, (fn ∘ e.symm) x ∂μ.prod (Measure.pi fun _ : Fin q => μ)) = _
        rw [integral_prod _ hfn']
        exact integral_congr_ae <| Filter.Eventually.of_forall fun x =>
          integral_congr_ae <| Filter.Eventually.of_forall fun y =>
            congrArg fn (funext fun i => by cases i using Fin.cases <;> simp [e])
      have hcons_int (A B : Ω → Fin p → ℝ) (hA : Measurable A) (hB : Measurable B)
          (hlA : ∀ a, MemLp (fun ω => A ω a) 2 μ) (hlB : ∀ a, MemLp (fun ω => B ω a) 2 μ) :
          Integrable (fun xy : Ω × (Fin q → Ω) => Hq (Fin.cons (A xy.1) fun j => B (xy.2 j)) ^ 2)
            (μ.prod (Measure.pi fun _ : Fin q => μ)) := by
        let C_fn : Fin (q + 1) → Ω → Fin p → ℝ := Fin.cons A fun _ => B
        have hf := product_kernel_square_integrable_l2 Hq C_fn
          (fun i => by cases i using Fin.cases <;> simp [C_fn, hA, hB])
          (fun i a => by
            cases i using Fin.cases
            · simpa [C_fn] using hlA a
            · simpa [C_fn] using hlB a)
        refine ((he.symm e).integrable_comp_of_integrable hf).congr (Filter.Eventually.of_forall fun xy => ?_)
        exact congrArg (· ^ 2) (congrArg Hq (funext fun i => by cases i using Fin.cases <;> simp [C_fn, e]))
      have hc := hcons_int Y Y hY hY hYlp hYlp
      have hmix := hcons_int Z Y hmZ hY hL2Z hYlp
      have hu := hcons_int Z Z hmZ hmZ hL2Z hL2Z
      have hiC := product_kernel_square_integrable_l2 Hq (fun _ => Y) (fun _ => hY) fun _ => hYlp
      have hiU := product_kernel_square_integrable_l2 Hq (fun _ => Z) (fun _ => hmZ) fun _ => hL2Z
      have hlin (L : (Fin p → ℝ) →L[ℝ] ℝ) : (∫ ω, L (Z ω - m) ^ 2 ∂μ) ≤ ∫ ω, L (Z ω) ^ 2 ∂μ := by
        have hiZ : Integrable Z μ := integrable_pi_iff.mpr fun a => (hL2Z a).integrable (by norm_num)
        have hvec : (∫ ω, Z ω ∂μ) = m := funext fun a =>
          ((ContinuousLinearMap.proj a : (Fin p → ℝ) →L[ℝ] ℝ).integral_comp_comm hiZ).symm.trans (hmeanZ a)
        have hLZ : Measurable fun ω => L (Z ω) := L.continuous.measurable.comp hmZ
        have hv := variance_le_expectation_sq (μ := μ) hLZ.aestronglyMeasurable
        rw [variance_eq_integral hLZ.aemeasurable, L.integral_comp_comm hiZ, hvec] at hv
        simpa only [map_sub, Pi.pow_apply] using hv
      calc (∫ ω, Hq (fun j => Y (ω j)) ^ 2 ∂Measure.pi fun _ : Fin (q + 1) => μ)
        _ = ∫ x, ∫ y, Hq (Fin.cons (Y x) fun j => Y (y j)) ^ 2 ∂Measure.pi (fun _ : Fin q => μ) ∂μ := by
            rw [hpi_succ _ hiC]
            exact integral_congr_ae <| Filter.Eventually.of_forall fun x =>
              integral_congr_ae <| Filter.Eventually.of_forall fun y =>
                congrArg (· ^ 2) (congrArg Hq (funext fun j => by cases j using Fin.cases <;> simp))
        _ = ∫ y, ∫ x, Hq (Fin.cons (Y x) fun j => Y (y j)) ^ 2 ∂μ ∂Measure.pi (fun _ : Fin q => μ) :=
            integral_integral_swap hc
        _ ≤ ∫ y, ∫ x, Hq (Fin.cons (Z x) fun j => Y (y j)) ^ 2 ∂μ ∂Measure.pi (fun _ : Fin q => μ) :=
            integral_mono_ae hc.integral_prod_right hmix.integral_prod_right <|
              Filter.Eventually.of_forall fun y => by
                simpa only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply,
                  ContinuousMultilinearMap.curryLeft_apply, Y] using
                  hlin ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Fin p → ℝ) ℝ (fun j => Y (y j))).comp Hq.curryLeft)
        _ = ∫ x, ∫ y, Hq (Fin.cons (Z x) fun j => Y (y j)) ^ 2 ∂Measure.pi (fun _ : Fin q => μ) ∂μ :=
            (integral_integral_swap hmix).symm
        _ ≤ ∫ x, ∫ y, Hq (Fin.cons (Z x) fun j => Z (y j)) ^ 2 ∂Measure.pi (fun _ : Fin q => μ) ∂μ :=
            integral_mono_ae hmix.integral_prod_left hu.integral_prod_left <|
              Filter.Eventually.of_forall fun x => by simpa only [ContinuousMultilinearMap.curryLeft_apply] using ih (Hq.curryLeft (Z x))
        _ = _ := by
            rw [hpi_succ _ hiU]
            exact integral_congr_ae <| Filter.Eventually.of_forall fun x =>
              integral_congr_ae <| Filter.Eventually.of_forall fun y =>
                congrArg (· ^ 2) (congrArg Hq (funext fun j => by cases j using Fin.cases <;> simp))
  by_cases hr : r = 0
  · subst r
    exact le_of_eq (integral_congr_ae <| Filter.Eventually.of_forall fun ω =>
      congrArg (· ^ 2) (congrArg H (funext fun i => Fin.elim0 i)))
  · let j : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    have hcopy : Measurable fun ω : Fin r → Ω => fun i => X j (ω i) :=
      measurable_pi_iff.mpr fun i => (hm j).comp (measurable_pi_apply i)
    have hjoint : Measurable fun ω => fun i => X i ω := measurable_pi_iff.mpr hm
    have hjointLaw : IdentDistrib (fun ω => fun i => X i ω) (fun ω : Fin r → Ω => fun i => X j (ω i)) μ (Measure.pi fun _ => μ) := by
      refine ⟨hjoint.aemeasurable, hcopy.aemeasurable, ?_⟩
      rw [hind.map_fun_eq_pi_map fun i => (hm i).aemeasurable, Measure.pi_map_pi fun _ => (hm j).aemeasurable]
      exact congrArg Measure.pi (funext fun i => (hid i j).map_eq)
    have hc : Measurable fun v : Fin r → Fin p → ℝ => H (fun i => v i - m) ^ 2 :=
      (H.coe_continuous.measurable.comp (measurable_pi_iff.mpr fun i => (measurable_pi_apply i).sub measurable_const)).pow_const 2
    have hu : Measurable fun v : Fin r → Fin p → ℝ => H v ^ 2 := H.coe_continuous.measurable.pow_const 2
    have hcEq : (∫ ω, H (fun i => X i ω - m) ^ 2 ∂μ) = ∫ ω, H (fun i => X j (ω i) - m) ^ 2 ∂Measure.pi fun _ : Fin r => μ := by
      simpa only [Function.comp_def] using (hjointLaw.comp hc).integral_eq
    have huEq : (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) = ∫ ω, H (fun i => X j (ω i)) ^ 2 ∂Measure.pi fun _ : Fin r => μ := by
      simpa only [Function.comp_def] using (hjointLaw.comp hu).integral_eq
    rw [hcEq, huEq]
    exact hiid H (X j) (hm j) (hL2 j) (hmean j)

theorem descFactorial_lower_bound {n R k : ℕ} (hRn : R ≤ n) (hkR : k ≤ R)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    Λ ^ k ≤ (n.descFactorial k : ℝ) := by
  have hcast : ((n + 1 - k : ℕ) : ℝ) = (n : ℝ) + 1 - k := by
    rw [Nat.cast_sub (by omega : k ≤ n + 1), Nat.cast_add, Nat.cast_one]
  have hRk : (k : ℝ) ≤ R := by exact_mod_cast hkR
  calc Λ ^ k ≤ ((n + 1 - k : ℕ) : ℝ) ^ k := pow_le_pow_left₀ hΛ (by rw [hcast]; linarith) k
    _ ≤ (n.descFactorial k : ℝ) := by exact_mod_cast Nat.pow_sub_le_descFactorial n k

theorem centered_expansion_variance_le_raw_power [IsProbabilityMeasure μ]
    {n p R : ℕ} (c : ℝ)
    (H : (r : Fin R) → ContinuousMultilinearMap ℝ (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (hsym : ∀ r (σ : Equiv.Perm (Fin (r.val + 1))) v, H r (fun i => v (σ i)) = H r v)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ) (hR : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1) :
    variance (centeredKernelExpansion c H (fun j ω => X j ω - m)) μ ≤
      ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
        ∫ ω, H r (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ^ 2 ∂μ := by
  obtain ⟨hi, hm, hid', hlp, hzero⟩ := centerObservations_l2 X m hind hmeas hid hL2 hmean
  rw [centeredKernelExpansion_variance c H hsym _ hR hi hm hid' hlp hzero]
  refine Finset.sum_le_sum fun r _ => ?_
  let e := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR)
  have hc := independent_centering_square_le_l2 μ (H r) (fun i => X (e i)) (fun i => hmeas (e i))
    (hind.precomp e.injective) (fun i j => hid (e i) (e j)) (fun i a => hL2 (e i) a) m fun i a => hmean (e i) a
  have hb := descFactorial_lower_bound hR (Nat.succ_le_of_lt r.isLt) hΛ.le hΛn
  have hfac : 0 < ((r.val + 1).factorial : ℝ) := by positivity
  have hpow : 0 < Λ ^ (r.val + 1) := pow_pos hΛ _
  have hd := (inv_le_inv₀ (mul_pos hfac (hpow.trans_le hb)) (mul_pos hfac hpow)).mpr
    (mul_le_mul_of_nonneg_left hb hfac.le)
  exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans
    (mul_le_mul_of_nonneg_right hd (integral_nonneg fun _ => sq_nonneg _))

theorem polynomialLift_memLp_two_l2 [IsProbabilityMeasure μ]
    {n p R : ℕ} (F : MvPolynomial (Fin p) ℝ)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hdeg : F.totalDegree ≤ R) (hRn : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) :
    MemLp (RoughRegime.Upper.polynomialLift F X) 2 μ := by
  rw [polynomialLift_centering_l2 F X m hdeg hRn]
  exact centeredKernelExpansion_memLp_two _ _ _
    (hind.comp (fun _ (v : Fin p → ℝ) => v - m) fun _ => measurable_id.sub_const m)
    (fun j => (hmeas j).sub_const m) fun j a => (hL2 j a).sub (memLp_const (m a))

theorem polynomialLift_expectation_l2 [IsProbabilityMeasure μ]
    {n p R : ℕ} (F : MvPolynomial (Fin p) ℝ)
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

theorem polynomialLift_variance_le_raw_power_l2 [IsProbabilityMeasure μ]
    {n p R : ℕ} (F : MvPolynomial (Fin p) ℝ)
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
  rw [polynomialLift_centering_l2 F X m hdeg hRn]
  exact centered_expansion_variance_le_raw_power _ _
    (fun _ σ v => (AnalyticOnNhd.eval_mvPolynomial F).analyticOn.iteratedFDeriv_comp_perm v σ)
    X m hRn hind hmeas hid hL2 hmean Λ hΛ hΛn

end ProbabilityL2
end NearlyMinimax.LiftL2

-- 3. Raw multilinear kernel moment bounds (`KernelMomentBounds`)

namespace NearlyMinimax.KernelMomentBounds

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem pi_norm_sq_le_sum_sq {p : ℕ} (v : Fin p → ℝ) : ‖v‖ ^ 2 ≤ ∑ a, (v a) ^ 2 := by
  have hS : 0 ≤ ∑ a : Fin p, (v a) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hn : ‖v‖ ≤ Real.sqrt (∑ a : Fin p, (v a) ^ 2) :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun a => by
      simpa only [Real.norm_eq_abs, Real.sqrt_sq_eq_abs] using
        Real.sqrt_le_sqrt (Finset.single_le_sum (fun b _ => sq_nonneg (v b)) (Finset.mem_univ a))
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hS)

theorem vector_memLp_two {p : ℕ} (X : Ω → Fin p → ℝ) (hm : Measurable X)
    (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 μ) : MemLp X 2 μ :=
  (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr <|
    (integrable_finsetSum Finset.univ fun a _ => (hL2 a).integrable_sq).mono' (hm.norm.pow_const 2).aestronglyMeasurable <|
      Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact pi_norm_sq_le_sum_sq (X ω)

theorem vector_second_le_sum_coordinates {p : ℕ} (X : Ω → Fin p → ℝ) (hm : Measurable X)
    (hL2 : ∀ a, MemLp (fun ω => X ω a) 2 μ) :
    (∫ ω, ‖X ω‖ ^ 2 ∂μ) ≤ ∑ a, ∫ ω, X ω a ^ 2 ∂μ := by
  have h := integral_mono (vector_memLp_two X hm hL2).norm.integrable_sq
    (integrable_finsetSum Finset.univ fun a _ => (hL2 a).integrable_sq) fun ω => pi_norm_sq_le_sum_sq (X ω)
  rwa [integral_finsetSum _ fun a _ => (hL2 a).integrable_sq] at h

theorem factorial_kernel_budget {p k : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ)
    (X : Fin k → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (hL2 : ∀ i a, MemLp (fun ω => X i ω a) 2 μ)
    (E a c Λ : ℝ) (hE : 0 ≤ E) (ha : 0 ≤ a) (hc : 0 ≤ c) (hΛ : 0 < Λ)
    (henergy : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂μ) ≤ E)
    (hderiv : ‖H‖ ≤ a * (k.factorial : ℝ) * c ^ k) :
    (((k.factorial : ℝ) * Λ ^ k)⁻¹) * (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) ≤
      a ^ 2 * (k.factorial : ℝ) * (c ^ 2 * E / Λ) ^ k := by
  have hind' : iIndepFun (fun i ω => ‖X i ω‖ ^ 2) μ :=
    hind.comp (fun _ (v : Fin p → ℝ) => ‖v‖ ^ 2) fun _ => measurable_norm.pow_const 2
  have hmeas' (i : Fin k) : Measurable fun ω => ‖X i ω‖ ^ 2 := (hm i).norm.pow_const 2
  have hd := LiftL2.independent_finset_product_integrable hind' hmeas'
    (fun i => (vector_memLp_two (X i) (hm i) (hL2 i)).norm.integrable_sq) Finset.univ
  have hraw := (LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap (Function.Embedding.refl (Fin k)) X hind hm hL2).integrable_sq
  have h2nd : (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) ≤ ‖H‖ ^ 2 * E ^ k := by
    have hcomp : (∫ ω, H (fun i => X i ω) ^ 2 ∂μ) ≤ ‖H‖ ^ 2 * ∫ ω, ∏ i : Fin k, ‖X i ω‖ ^ 2 ∂μ := by
      rw [← integral_const_mul]
      refine integral_mono hraw (hd.const_mul (‖H‖ ^ 2)) fun ω => ?_
      change H (fun i => X i ω) ^ 2 ≤ ‖H‖ ^ 2 * ∏ i : Fin k, ‖X i ω‖ ^ 2
      simpa only [Real.norm_eq_abs, sq_abs, mul_pow, Finset.prod_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (H.le_opNorm (fun i => X i ω)) 2
    rw [hind'.integral_fun_prod_eq_prod_integral fun i => (hmeas' i).aestronglyMeasurable] at hcomp
    refine hcomp.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    exact (Finset.prod_le_prod₀ (g := fun _ => E) (fun _ _ => integral_nonneg fun _ => sq_nonneg _) fun i _ => henergy i).trans_eq (by simp)
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hd_sq := pow_le_pow_left₀ (norm_nonneg _) hderiv 2
  refine (mul_le_mul_of_nonneg_left (h2nd.trans (mul_le_mul_of_nonneg_right hd_sq (pow_nonneg hE k)))
    (by positivity : 0 ≤ ((k.factorial : ℝ) * Λ ^ k)⁻¹)).trans_eq ?_
  simp only [div_pow, mul_pow, pow_mul, Nat.mul_comm]
  field_simp [hfac.ne', hΛ.ne']; ring

end NearlyMinimax.KernelMomentBounds

-- 4. Spatial field lift covariance & localization (`FieldLiftCovariance`)

namespace NearlyMinimax.FieldLiftCovariance

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {M : Measure W}

abbrev KernelMap (p k : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ

def rawKernelOperator {n p k : ℕ} (e : Fin k ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) : KernelMap p k →L[ℝ] Lp ℝ 2 μ :=
  ∑ σ : Fin k → Fin p,
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin p → ℝ) ℝ (fun i => Pi.single (σ i) 1)).smulRight
      ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp fun ω => ∏ i, X (e i) ω (σ i))

private theorem raw_kernel_operator_eq_toLp {n p k : ℕ} (e : Fin k ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) (H : KernelMap p k) :
    rawKernelOperator e X hind hmeas hL2 H =
      (LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap e X hind hmeas hL2).toLp
        fun ω => H (fun i => X (e i) ω) := by
  have heq : rawKernelOperator e X hind hmeas hL2 H =
      ∑ σ : Fin k → Fin p, H (fun i => Pi.single (σ i) 1) •
        ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp fun ω => ∏ i, X (e i) ω (σ i)) := by
    simp [rawKernelOperator]
  rw [heq]; apply Lp.ext
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ fun σ : Fin k → Fin p => H (fun i => Pi.single (σ i) 1) •
    ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp fun ω => ∏ i, X (e i) ω (σ i))
  have hterms : ∀ᵐ ω ∂μ, ∀ σ : Fin k → Fin p,
      (H (fun i => Pi.single (σ i) 1) •
        ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp fun ω => ∏ i, X (e i) ω (σ i))) ω =
        H (fun i => Pi.single (σ i) 1) * ∏ i, X (e i) ω (σ i) :=
    Filter.eventually_all.mpr fun σ => by
      filter_upwards [Lp.coeFn_smul (H (fun i => Pi.single (σ i) 1))
        ((LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).toLp fun ω => ∏ i, X (e i) ω (σ i)),
        (LiftL2.coordinate_monomial_memLp_two e σ X hind hmeas hL2).coeFn_toLp] with ω hs hp
      rw [hs, Pi.smul_apply, hp, smul_eq_mul]
  filter_upwards [hsum, hterms,
    (LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap e X hind hmeas hL2).coeFn_toLp] with ω hs ht hH
  change ((LiftL2.multilinear_kernel_memLp_two H.toMultilinearMap e X hind hmeas hL2).toLp
    fun ω => H (fun i => X (e i) ω)) ω = H (fun i => X (e i) ω) at hH
  rw [hs, hH]
  exact (Finset.sum_congr rfl fun σ _ => ht σ).trans (LiftL2.multilinear_coordinate_expansion H.toMultilinearMap _).symm

theorem raw_kernel_operator_norm_sq {n p k : ℕ} (e : Fin k ↪ Fin n)
    (X : Fin n → Ω → Fin p → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ j, Measurable (X j))
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ) (H : KernelMap p k) :
    ‖rawKernelOperator e X hind hmeas hL2 H‖ ^ 2 = ∫ ω, H (fun i => X (e i) ω) ^ 2 ∂μ := by
  rw [raw_kernel_operator_eq_toLp]
  exact LocalizationL2.toLp_norm_sq_eq_integral_sq _

theorem weighted_kernel_statistic_integrable {n p k : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (ν : W → ℝ) (H : W → KernelMap p k)
    (hH : Integrable (fun w => ν w • H w) M) (ω : Ω) :
    Integrable (fun w => ν w * LiftL2.kernelStatistic (H w) X ω) M := by
  let d := (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹)
  have hi (e : Fin k ↪ Fin n) : Integrable (fun w => ν w * H w (fun i => X (e i) ω)) M := by
    simpa only [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul] using
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin p → ℝ) ℝ (fun i => X (e i) ω)).integrable_comp hH
  convert integrable_finsetSum Finset.univ (fun e _ => (hi e).const_mul d) using 1
  funext w; simp only [LiftL2.kernelStatistic, LiftL2.kernelSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by dsimp [d]; ring

private theorem centered_expansion_integral_commute {n p R : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (ν : W → ℝ)
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (hH : ∀ r, Integrable (fun w => ν w • H w r) M) (ω : Ω) :
    (∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w) X ω ∂M) =
      LiftL2.centeredKernelExpansion 0 (fun r => ∫ w, ν w • H w r ∂M) X ω := by
  simp only [LiftL2.centeredKernelExpansion, zero_add, Finset.mul_sum]
  rw [integral_finsetSum _ fun r _ => weighted_kernel_statistic_integrable X ν (fun w => H w r) (hH r) ω]
  refine Finset.sum_congr rfl fun r _ => ?_
  let k := r.val + 1
  let d := (((k.factorial : ℝ) * (n.descFactorial k : ℝ))⁻¹)
  have hi (e : Fin k ↪ Fin n) : Integrable (fun w => ν w * H w r (fun i => X (e i) ω)) M := by
    simpa only [ContinuousMultilinearMap.apply_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul] using
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin p → ℝ) ℝ (fun i => X (e i) ω)).integrable_comp (hH r)
  have halg : (fun w => ν w * LiftL2.kernelStatistic (H w r) X ω) =
      fun w => d * ∑ e : Fin k ↪ Fin n, ν w * H w r (fun i => X (e i) ω) := funext fun w => by
    simp only [LiftL2.kernelStatistic, LiftL2.kernelSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by dsimp [d, k]; ring
  rw [halg, integral_const_mul, integral_finsetSum _ fun e _ => hi e]
  change d * ∑ e : Fin k ↪ Fin n, (∫ w, ν w * H w r (fun i => X (e i) ω) ∂M) =
    d * ∑ e : Fin k ↪ Fin n, (∫ w, ν w • H w r ∂M) (fun i => X (e i) ω)
  congr 1; refine Finset.sum_congr rfl fun e _ => ?_
  rw [ContinuousMultilinearMap.integral_apply (hH r)]; rfl

theorem integrated_centered_lift_moment_facts {n p R : ℕ}
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (ν : W → ℝ) (hH : ∀ r, Integrable (fun w => ν w • H w r) M)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a) :
    MemLp (fun ω => ∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) 2 μ ∧
      (∫ ω, ∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M ∂μ) = 0 := by
  rw [show (fun ω => ∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) =
    LiftL2.centeredKernelExpansion 0 (fun r => ∫ w, ν w • H w r ∂M) (fun j ω => X j ω - m) from
      funext fun ω => centered_expansion_integral_commute _ ν H hH ω]
  obtain ⟨hi, hm, _, hlp, hzero⟩ := LiftL2.centerObservations_l2 X m hind hmeas hid hL2 hmean
  exact ⟨LiftL2.centeredKernelExpansion_memLp_two _ _ _ hi hm hlp,
    LiftL2.centeredKernelExpansion_expectation _ _ _ hi hm hlp hzero⟩

theorem integrated_centered_lift_variance_localized [IsFiniteMeasure M] {n p R q : ℕ}
    (H : W → (r : Fin R) → KernelMap p (r.val + 1))
    (ν : W → ℝ) (hν : MemLp ν 2 M)
    (hH : ∀ r, Integrable (fun w => ν w • H w r) M)
    (hHmeas : ∀ r, AEStronglyMeasurable (fun w => H w r) M)
    (hsym : ∀ w r (σ : Equiv.Perm (Fin (r.val + 1))) v, H w r (fun i => v (σ i)) = H w r v)
    (X : Fin n → Ω → Fin p → ℝ) (m : Fin p → ℝ) (hR : R ≤ n)
    (hind : iIndepFun X μ) (hmeas : ∀ j, Measurable (X j))
    (hid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hL2 : ∀ j a, MemLp (fun ω => X j ω a) 2 μ)
    (hmean : ∀ j a, ∫ ω, X j ω a ∂μ = m a)
    (Λ : ℝ) (hΛ : 0 < Λ) (hΛn : Λ ≤ (n : ℝ) - R + 1)
    (b : W → Fin q) (hb : Measurable b)
    (C : Fin R → ℝ) (hC : ∀ r, 0 ≤ C r)
    (hbound : ∀ r, ∀ᵐ w ∂M,
      ‖rawKernelOperator (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR)) X hind hmeas hL2 (H w r)‖ ≤ C r)
    (hdisjoint : ∀ r w v, b w ≠ b v → ∀ᵐ ω ∂μ,
      H w r (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) *
      H v r (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) = 0)
    (L : ℝ) (hL : ∀ c, M.real {w | b w = c} ≤ L) :
    variance (fun ω => ∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) μ ≤
      L * ∫ w, ν w ^ 2 * ∑ r : Fin R, (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹ *
        ∫ ω, H w r (fun i => X (Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR) i) ω) ^ 2 ∂μ ∂M := by
  let e (r : Fin R) := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hR)
  let K (r : Fin R) (w : W) := rawKernelOperator (e r) X hind hmeas hL2 (H w r)
  let δ (r : Fin R) := (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹
  have hKmeas (r : Fin R) : AEStronglyMeasurable (K r) M :=
    (rawKernelOperator (e r) X hind hmeas hL2).continuous.comp_aestronglyMeasurable (hHmeas r)
  have horth (r : Fin R) (w v : W) (h : b w ≠ b v) : ⟪K r w, K r v⟫ = 0 := by
    dsimp [K]; rw [raw_kernel_operator_eq_toLp, raw_kernel_operator_eq_toLp]
    exact LocalizationL2.toLp_inner_eq_zero_of_disjoint _ _ (hdisjoint r w v h)
  have hl := LocalizationL2.weighted_kernel_series_localization_bound b hb ν hν K hKmeas
    C hC hbound horth δ (fun _ => by dsimp [δ]; positivity) L hL
  have hint_sym (r : Fin R) (σ : Equiv.Perm (Fin (r.val + 1))) (v) :
      (∫ w, ν w • H w r ∂M) (fun i => v (σ i)) = (∫ w, ν w • H w r ∂M) v := by
    rw [ContinuousMultilinearMap.integral_apply (hH r), ContinuousMultilinearMap.integral_apply (hH r)]
    exact integral_congr_ae <| Filter.Eventually.of_forall fun w => by simp only [smul_apply, hsym w r σ v]
  have hfirst : variance (fun ω => ∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) μ ≤
      ∑ r : Fin R, δ r * ‖∫ w, ν w • K r w ∂M‖ ^ 2 := by
    rw [show (fun ω => ∫ w, ν w * LiftL2.centeredKernelExpansion 0 (H w) (fun j ω => X j ω - m) ω ∂M) =
      LiftL2.centeredKernelExpansion 0 (fun r => ∫ w, ν w • H w r ∂M) (fun j ω => X j ω - m) from
        funext fun ω => centered_expansion_integral_commute _ ν H hH ω]
    refine (LiftL2.centered_expansion_variance_le_raw_power 0 _ hint_sym X m hR hind hmeas hid hL2 hmean Λ hΛ hΛn).trans_eq ?_
    refine Finset.sum_congr rfl fun r _ => congrArg (δ r * ·) ?_
    rw [← raw_kernel_operator_norm_sq (e r) X hind hmeas hL2,
      ← (rawKernelOperator (e r) X hind hmeas hL2).integral_comp_comm (hH r)]
    exact congrArg (‖·‖ ^ 2) (integral_congr_ae <| Filter.Eventually.of_forall fun _ => map_smul _ _ _)
  refine hfirst.trans (hl.trans_eq ?_)
  congr 1; refine integral_congr_ae <| Filter.Eventually.of_forall fun w => congrArg (ν w ^ 2 * ·) ?_
  exact Finset.sum_congr rfl fun r _ => congrArg (δ r * ·) (raw_kernel_operator_norm_sq (e r) X hind hmeas hL2 (H w r))

end NearlyMinimax.FieldLiftCovariance
