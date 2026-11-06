module
public import NearlyMinimax.HighObservationLaw
public import NearlyMinimax.HighUnionFieldScore
public import NearlyMinimax.SpatialPairProductIntegration
public import NearlyMinimax.SpatialSubsetEnergy
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem iid_selected_membership_integral  [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n A)
    (S : Finset (Fin n)) (H : (S → α) → ℝ) :
    (∫ x in designMembershipCell n A S, H (fun i : S => x i.val)
      ∂Measure.pi (fun _ : Fin n => μ)) =
      (μ.real Aᶜ) ^ (n - S.card) *
        ∫ z, H z ∂Measure.pi (fun _ : S => μ.restrict A) := by
  let μi : Fin n → Measure α := fun i => μ.restrict (if i ∈ S then A else Aᶜ)
  have hm : (Measure.pi (fun _ : Fin n => μ)).restrict (designMembershipCell n A S) = Measure.pi μi :=
    Measure.restrict_pi_pi (fun _ : Fin n => μ) (fun i => if i ∈ S then A else Aᶜ)
  have hs := measurePreserving_piEquivPiSubtypeProd μi (fun i : Fin n => i ∈ S)
  have hι : (Subtype.fintype (fun i : Fin n => i ∈ S) : Fintype S) = Finset.Subtype.fintype S := Subsingleton.elim _ _
  rw [hι] at hs
  have he := hs.integral_comp' (fun z => H z.1)
  change (∫ x, H (fun i : S => x i.val) ∂Measure.pi μi) = _ at he
  rw [hm, he]
  have hin : (fun i : S => μi i.val) = (fun _ : S => μ.restrict A) := by
    funext i
    simp only [μi, ite_eq_left i.property]
  have hout : (fun i : {i : Fin n // i ∉ S} => μi i.val) =
      (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ) := by
    funext i
    simp only [μi, ite_eq_right i.property]
  rw [hin, hout]
  have hint := integral_prod_mul (μ := Measure.pi (fun _ : S => μ.restrict A))
    (ν := Measure.pi (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ)) H (fun _ => ↑1)
  simp only [mul_one] at hint
  have hcard : Fintype.card {i : Fin n // i ∉ S} = n - S.card := by
    rw [Fintype.card_subtype_compl]
    simp
  calc
    _ = (∫ z, H z ∂Measure.pi (fun _ : S => μ.restrict A)) *
      (∫ z : {i : Fin n // i ∉ S} → α, ↑1 ∂Measure.pi (fun _ => μ.restrict Aᶜ)) := hint
    _ = _ := by
      rw [integral_const, smul_eq_mul, mul_one]
      simp only [Measure.real, Measure.pi_univ, Measure.restrict_apply_univ,
        Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow, hcard]
      ring
theorem iid_local_energy_le_selected_sum  [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n A) (hA : MeasurableSet A)
    (E ) (hE : Integrable E (Measure.pi (fun _ : Fin n => μ)))
    (H : (S : Finset (Fin n)) → (S → α) → ℝ)
    (hH : ∀ S, Integrable (H S) (Measure.pi (fun _ : S => μ.restrict A)))
    (hHn : ∀ S z, 0 ≤ H S z)
    (hdom : ∀ S x, x ∈ designMembershipCell n A S → E x ≤ H S (fun i : S => x i.val)) :
    (∫ x, E x ∂Measure.pi (fun _ : Fin n => μ)) ≤
      ∑ S : Finset (Fin n), ∫ z, H S z ∂Measure.pi (fun _ : S => μ.restrict A) := by
  have h_iid_integral_eq_membership_sum : (∫ x, E x ∂Measure.pi (fun _ => μ)) =
      ∑ S : Finset (Fin n), ∫ x in designMembershipCell n A S, E x
        ∂Measure.pi (fun _ => μ) := by
    have hcover : (⋃ S : Finset (Fin n), designMembershipCell n A S) = univ := by
      apply Set.eq_univ_of_forall
      intro x
      apply Set.mem_iUnion.mpr
      refine ⟨Finset.univ.filter (fun i => x i ∈ A), ?_⟩
      rw [design_membership_cell_iff]
      intro i
      simp
    rw [← setIntegral_univ, ← hcover]
    exact integral_iUnion_fintype (fun S => design_membership_cell_measurable n A hA S)
      (design_membership_cells_disjoint n A) (fun S => hE.integrableOn)
  rw [h_iid_integral_eq_membership_sum]
  apply Finset.sum_le_sum
  intro S hS
  have hm : (Measure.pi (fun _ => μ)).restrict (designMembershipCell n A S) =
      Measure.pi (fun i => μ.restrict (if i ∈ S then A else Aᶜ)) :=
    Measure.restrict_pi_pi _ _
  have hs := measurePreserving_piEquivPiSubtypeProd
    (fun i => μ.restrict (if i ∈ S then A else Aᶜ)) (fun i => i ∈ S)
  have hι : (Subtype.fintype (fun i => i ∈ S) : Fintype S) = Finset.Subtype.fintype S := Subsingleton.elim _ _
  rw [hι] at hs
  have hh := (hH S).mul_prod (integrable_const 1
    (μ := Measure.pi (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ)))
  have hselected : Integrable (fun x => H S (fun i => x i.val))
      ((Measure.pi (fun _ => μ)).restrict (designMembershipCell n A S)) := by
    rw [hm]
    have hin : (fun i : S => μ.restrict (if i.val ∈ S then A else Aᶜ)) =
        (fun _ : S => μ.restrict A) := by
      funext i
      rw [ite_eq_left i.property]
    have hout : (fun i : {i : Fin n // i ∉ S} => μ.restrict (if i.val ∈ S then A else Aᶜ)) =
        (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ) := by
      funext i
      rw [ite_eq_right i.property]
    rw [hin, hout] at hs
    have hh := (hs.integrable_comp_emb (MeasurableEquiv.piEquivPiSubtypeProd (fun _ => α)
      (fun i => i ∈ S)).measurableEmbedding).mpr (by simpa only [mul_one] using hh)
    change Integrable (fun x => H S (fun i => x i.val))
      (Measure.pi (fun i => μ.restrict (if i ∈ S then A else Aᶜ))) at hh
    exact hh
  calc
    _ ≤ ∫ x in designMembershipCell n A S, H S (fun i => x i.val) ∂Measure.pi (fun _ => μ) := by
      apply integral_mono_ae hE.integrableOn hselected
      filter_upwards [ae_restrict_mem (design_membership_cell_measurable n A hA S)] with x hx
      exact hdom S x hx
    _ = (μ.real Aᶜ) ^ (n - S.card) * ∫ z, H S z ∂Measure.pi (fun _ => μ.restrict A) :=
      iid_selected_membership_integral μ n A S (H S)
    _ ≤ _ := (mul_le_mul_of_nonneg_right (pow_le_one₀ measureReal_nonneg measureReal_le_one) (integral_nonneg (hHn S))).trans_eq (one_mul _)
def highNormalizedDesignLaw  (p : Covariate d → ℝ) : Measure (Covariate d) :=
  (cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity p x))
theorem high_normalized_design_probability  (p )
    (hp : Measurable p) (a b ) (ha : 0 < a)
    (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b) : IsProbabilityMeasure (highNormalizedDesignLaw p) :=
  normalizedDensityTernaryParameter_design_probability p hp a b ha hb
def highFixedScoreDenominator (pMinus cMass : ℝ) : ℝ := (pMinus ^ 2 * cMass)⁻¹
theorem high_fixed_score_denominator_pos {pMinus cMass : ℝ} (hp : 0 < pMinus) (hc : 0 < cMass) :
    0 < highFixedScoreDenominator pMinus cMass := by
  unfold highFixedScoreDenominator
  positivity
theorem iid_local_energy_le_factorial_spatial_series  [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A ) (hA : MeasurableSet A)
    (E : (Fin n → α) → ℝ) (hE : Integrable E (Measure.pi (fun _ : Fin n => μ)))
    (H : (S : Finset (Fin n)) → (S → α) → ℝ)
    (hH : ∀ S, Integrable (H S) (Measure.pi (fun _ : S => μ.restrict A)))
    (hHn : ∀ S z, 0 ≤ H S z)
    (hdom : ∀ S x, x ∈ designMembershipCell n A S → E x ≤ H S (fun i : S => x i.val))
    (ψ : ℝ) (hψ : 0 ≤ ψ) (J : ℕ → ℝ) (hJ : ∀ r, 0 ≤ J r)
    (hspatial : ∀ S : Finset (Fin n), (∫ z, H S z ∂Measure.pi (fun _ : S => μ.restrict A)) ≤ ψ ^ S.card * J S.card) :
    (∫ x, E x ∂Measure.pi (fun _ : Fin n => μ)) ≤
      ∑ r ∈ Finset.range (n + 1), (↑n * ψ) ^ r / ↑r.factorial * J r := by
  have h_iid_local_energy_le_binomial_spatial_series : (∫ x, E x ∂Measure.pi (fun _ : Fin n => μ)) ≤
      ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) * ψ ^ r * J r := by
    calc
      _ ≤ ∑ S : Finset (Fin n), ∫ z, H S z ∂Measure.pi (fun _ : S => μ.restrict A) :=
        iid_local_energy_le_selected_sum μ n A hA E hE H hH hHn hdom
      _ ≤ ∑ S : Finset (Fin n), ψ ^ S.card * J S.card :=
        Finset.sum_le_sum (fun S _ => hspatial S)
      _ = _ := by
        have h_finset_sum_cardinality (F : ℕ → ℝ) : (∑ S : Finset (Fin n), F S.card) =
            ∑ r ∈ Finset.range (n + 1), (n.choose r ) * F r := by
          have h := Finset.sum_powerset (Finset.univ : Finset (Fin n)) (fun S => F S.card)
          simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h
          rw [h]
          apply Finset.sum_congr rfl
          intro r hr
          simp only [Finset.sum_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
        rw [h_finset_sum_cardinality (fun r => ψ ^ r * J r)]
        apply Finset.sum_congr rfl
        intro r hr
        ring
  refine h_iid_local_energy_le_binomial_spatial_series.trans ?_
  apply Finset.sum_le_sum
  intro r hr
  calc
    _ ≤ (n ^ r / r.factorial) * ψ ^ r * J r := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div r n) (pow_nonneg hψ r)) (hJ r)
    _ = _ := by rw [mul_pow]; ring
def selectedRawLikelihood  [Fintype κ]
    (p : α → ℝ) (q : α → Fin 3 → ℝ) (x : κ → α) (y : κ → Fin 3) : ℝ :=
  (∏ i, p (x i)) * ∏ i, q (x i) (y i)
def selectedConditionalScoreEnergy  [Fintype κ]
    (p : α → ℝ) (q : α → Fin 3 → ℝ)
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α) : ℝ :=
  ∑ y : κ → Fin 3, (∏ i, q (x i) (y i)) * (R x y / selectedRawLikelihood p q x y) ^ 2
def selectedRawSquareEnergy  [Fintype κ]
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α) : ℝ :=
  ∑ y : κ → Fin 3, (R x y) ^ 2
theorem selected_conditional_score_energy_nonneg  [Fintype κ]
    (p q) (hq : ∀ x y, 0 ≤ q x y)
    (R : (κ → α) → (κ → Fin 3) → ℝ) (x : κ → α) :
    0 ≤ selectedConditionalScoreEnergy p q R x :=
  Finset.sum_nonneg (fun y _ => mul_nonneg (Finset.prod_nonneg (fun i _ => hq _ _)) (sq_nonneg _))
theorem normalized_selected_score_energy_integrable_bound  [Fintype κ]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (A ) (hA : MeasurableSet A) (m pMinus cMass )
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hm : pMinus ≤ m)
    (p ) (hpMeas : Measurable p) (q )
    (hqMeas : ∀ y, Measurable (fun x => q x y))
    (R ) (hR : ∀ y, Measurable (fun x => R x y))
    (hprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (p x / m))))
    (hp : ∀ x ∈ A, pMinus ≤ p x) (hq : ∀ x ∈ A, ∀ y, cMass ≤ q x y)
    (hRaw : Integrable (selectedRawSquareEnergy R) (Measure.pi (fun _ : κ => μ.restrict A))) :
    Integrable (selectedConditionalScoreEnergy p q R)
      (Measure.pi (fun _ => (μ.withDensity (fun z => ENNReal.ofReal (p z / m))).restrict A)) ∧
    (∫ x, selectedConditionalScoreEnergy p q R x
      ∂Measure.pi (fun _ => (μ.withDensity (fun z => ENNReal.ofReal (p z / m))).restrict A)) ≤
      highFixedScoreDenominator pMinus cMass ^ Fintype.card κ *
        ∫ x, selectedRawSquareEnergy R x ∂Measure.pi (fun _ : κ => μ.restrict A) := by
  have h_fintype_probability_pi_restrict_withDensity (f) (hf : Measurable f) (hprob : IsProbabilityMeasure (μ.withDensity f)) (A) (hA : MeasurableSet A) : Measure.pi (fun _ => (μ.withDensity f).restrict A) =
      (Measure.pi (fun _ : κ => μ.restrict A)).withDensity (fun x => ∏ i, f (x i)) := by
    have h_fintype_probability_pi_withDensity : Measure.pi (fun _ : κ => μ.withDensity f) =
        (Measure.pi (fun _ => μ)).withDensity (fun x => ∏ i, f (x i)) := by
      let _ := hprob
      apply Measure.pi_eq
      intro s hs
      rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator]
      · have he (x : κ → α) :
            (Set.pi Set.univ s).indicator (fun x => ∏ i, f (x i)) x =
              ∏ i, (s i).indicator f (x i) := by
          by_cases h : ∀ i, x i ∈ s i
          · simp [Set.indicator_of_mem, Set.mem_pi, h]
          · obtain ⟨i, hi⟩ := not_forall.mp h
            have hz : ∏ j, (s j).indicator f (x j) = 0 :=
              Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)
            rw [hz]
            apply Set.indicator_of_notMem
            simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
            exact not_forall.mpr ⟨i, hi⟩
        simp_rw [he]
        let G : κ → α → ℝ≥0∞ := fun i => (s i).indicator f
        have hG  := fun i => hf.indicator (hs i)
        change (∫⁻ x, ∏ i, G i (x i) ∂Measure.pi (fun _ => μ)) = _
        rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _
          (iIndepFun_pi (fun i => (hG i).aemeasurable))
          (fun i => (hG i).comp (measurable_pi_apply i))]
        apply Finset.prod_congr rfl
        intro i _
        rw [(measurePreserving_eval (fun _ => μ) i).lintegral_comp (hG i), lintegral_indicator (hs i), withDensity_apply f (hs i)]
      · exact MeasurableSet.univ_pi hs
    rw [← Measure.restrict_pi_pi (fun _ => μ.withDensity f) (fun _ => A),
      h_fintype_probability_pi_withDensity,
      restrict_withDensity (MeasurableSet.univ_pi (fun _ => hA)),
      Measure.restrict_pi_pi]
  have h_normalized_selected_score_density_cancel_ae (hm : 0 < m) (p) (q) (R) (hp : ∀ x ∈ A, 0 < p x) (hq : ∀ x ∈ A, ∀ y, 0 < q x y) : (fun x => (∏ i, ENNReal.ofReal (p (x i) / m)).toReal *
      selectedConditionalScoreEnergy p q R x) =ᵐ[Measure.pi (fun _ => μ.restrict A)]
      (fun x => ∑ y : κ → Fin 3,
        (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2) := by
    have hmem : ∀ᵐ x ∂Measure.pi (fun _ : κ => μ.restrict A), ∀ i, x i ∈ A :=
      ae_all_iff.mpr (fun i => Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem hA))
    filter_upwards [hmem] with x hx
    have he : (∏ i, ENNReal.ofReal (p (x i) / m)).toReal = ∏ i, p (x i) / m := by
      rw [ENNReal.toReal_prod]
      apply Finset.prod_congr rfl
      intro i hi
      exact ENNReal.toReal_ofReal (div_nonneg (hp _ (hx i)).le hm.le)
    rw [he]
    unfold selectedConditionalScoreEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ]
    unfold selectedRawLikelihood
    field_simp [ne_of_gt (Finset.prod_pos (fun i _ => (fun i => hp _ (hx i)) i)), ne_of_gt (Finset.prod_pos (fun i _ => (fun i y => hq _ (hx i) y) i (y i))), hm.ne']
    <;> ring
  have hm0 : 0 < m := hpMinus.trans_le hm
  have hpp (x : α) (hx : x ∈ A) : 0 < p x := hpMinus.trans_le (hp x hx)
  have hqp (x : α) (hx : x ∈ A) (y : Fin 3) : 0 < q x y := hcMass.trans_le (hq x hx y)
  let W : (κ → α) → ℝ := fun x => ∑ y : κ → Fin 3,
    (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2
  have hWMeas : Measurable W := by
    apply Finset.measurable_sum
    intro y hy
    have : Measurable (fun x : κ → α => ∏ i, q (x i) (y i)) :=
      Finset.measurable_prod _ (fun i _ => (hqMeas (y i)).comp (measurable_pi_apply i))
    have : Measurable (fun x : κ → α => ∏ i, p (x i)) :=
      Finset.measurable_prod _ (fun i _ => hpMeas.comp (measurable_pi_apply i))
    unfold selectedRawLikelihood
    fun_prop
  have hmem : ∀ᵐ x ∂Measure.pi (fun _ : κ => μ.restrict A), ∀ i, x i ∈ A :=
    ae_all_iff.mpr (fun i => Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem hA))
  have hWbound : ∀ᵐ x ∂Measure.pi (fun _ : κ => μ.restrict A),
      0 ≤ W x ∧ W x ≤ highFixedScoreDenominator pMinus cMass ^ Fintype.card κ * selectedRawSquareEnergy R x := by
    filter_upwards [hmem] with x hx
    constructor
    · apply Finset.sum_nonneg
      intro y hy
      have h_selected_raw_likelihood_positive (hp : ∀ i, 0 < p (x i)) (hq : ∀ i, 0 < q (x i) (y i)) : 0 < selectedRawLikelihood p q x y := mul_pos (Finset.prod_pos (fun i _ => hp i)) (Finset.prod_pos (fun i _ => hq i))
      have hL := h_selected_raw_likelihood_positive (fun i => hpp _ (hx i)) (fun i => hqp _ (hx i) (y i))
      exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (pow_nonneg hm0.le _) hL.le)) (sq_nonneg _)
    · unfold W selectedRawSquareEnergy
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y hy
      have h_selected_raw_inverse_floor : (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ ≤
      highFixedScoreDenominator pMinus cMass ^ Fintype.card κ := by
        have hp : ∀ i, pMinus ≤ p (x i) := fun i => hp _ (hx i)
        have hq : ∀ i, cMass ≤ q (x i) (y i) := fun i => hq _ (hx i) (y i)
        have hfac (i : κ) : pMinus ^ 2 * cMass ≤ m * (p (x i) * q (x i) (y i)) := by
          have : 0 ≤ q (x i) (y i) := hcMass.le.trans (hq i)
          have hp0 : 0 ≤ p (x i) := hpMinus.le.trans (hp i)
          have hpq := mul_le_mul (hp i) (hq i) hcMass.le hp0
          have := mul_le_mul hm hpq (mul_nonneg hpMinus.le hcMass.le) (hpMinus.le.trans hm)
          nlinarith
        have hprod : (pMinus ^ 2 * cMass) ^ Fintype.card κ ≤
            m ^ Fintype.card κ * selectedRawLikelihood p q x y := by
          calc
            _ = ∏ _i : κ, pMinus ^ 2 * cMass := by simp
            _ ≤ ∏ i, m * (p (x i) * q (x i) (y i)) :=
              Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hfac i)
            _ = _ := by unfold selectedRawLikelihood; rw [Finset.prod_mul_distrib]; simp [Finset.prod_mul_distrib]
        have hleft : 0 < (pMinus ^ 2 * cMass) ^ Fintype.card κ := by positivity
        have hright : 0 < m ^ Fintype.card κ * selectedRawLikelihood p q x y := hleft.trans_le hprod
        unfold highFixedScoreDenominator
        rw [inv_pow]
        exact (inv_le_inv₀ hright hleft).mpr hprod
      exact mul_le_mul_of_nonneg_right
        h_selected_raw_inverse_floor (sq_nonneg _)
  have hJ := hRaw.const_mul (highFixedScoreDenominator pMinus cMass ^ Fintype.card κ)
  have hWI : Integrable W (Measure.pi (fun _ : κ => μ.restrict A)) := by
    apply hJ.mono' hWMeas.aestronglyMeasurable
    filter_upwards [hWbound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  constructor
  · have hf : Measurable (fun x => ENNReal.ofReal (p x / m)) :=
      ENNReal.measurable_ofReal.comp (hpMeas.div_const m)
    have hfP : Measurable (fun x : κ → α => ∏ i, ENNReal.ofReal (p (x i) / m)) :=
      Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))
    rw [h_fintype_probability_pi_restrict_withDensity _ hf hprob A hA]
    apply (integrable_withDensity_iff_integrable_smul' hfP
      (Filter.Eventually.of_forall (fun _ => ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)))).mpr
    have he := h_normalized_selected_score_density_cancel_ae hm0 p q R hpp hqp
    exact hWI.congr he.symm
  have h_normalized_selected_score_energy_integral_eq_raw : (∫ x, selectedConditionalScoreEnergy p q R x
      ∂Measure.pi (fun _ : κ => (μ.withDensity (fun z => ENNReal.ofReal (p z / m))).restrict A)) =
      ∫ x, ∑ y : κ → Fin 3,
        (m ^ Fintype.card κ * selectedRawLikelihood p q x y)⁻¹ * (R x y) ^ 2
          ∂Measure.pi (fun _ : κ => μ.restrict A) := by
    have hf : Measurable (fun x => ENNReal.ofReal (p x / m)) :=
      ENNReal.measurable_ofReal.comp (hpMeas.div_const m)
    rw [h_fintype_probability_pi_restrict_withDensity _ hf hprob A hA]
    have hfP : Measurable (fun x : κ → α => ∏ i, ENNReal.ofReal (p (x i) / m)) :=
      Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))
    have he := integral_withDensity_eq_integral_toReal_smul
      (μ := Measure.pi (fun _ : κ => μ.restrict A)) hfP
      (Filter.Eventually.of_forall (fun _ => ENNReal.prod_lt_top (fun _ _ => ENNReal.ofReal_lt_top)))
      (selectedConditionalScoreEnergy p q R)
    change (∫ x, selectedConditionalScoreEnergy p q R x
      ∂(Measure.pi (fun _ : κ => μ.restrict A)).withDensity (fun x => ∏ i, ENNReal.ofReal (p (x i) / m))) =
        ∫ x, (∏ i, ENNReal.ofReal (p (x i) / m)).toReal * selectedConditionalScoreEnergy p q R x
          ∂Measure.pi (fun _ : κ => μ.restrict A) at he
    rw [he]
    apply integral_congr_ae
    exact h_normalized_selected_score_density_cancel_ae hm0 p q R hpp hqp
  rw [h_normalized_selected_score_energy_integral_eq_raw]
  calc
    _ ≤ ∫ x, highFixedScoreDenominator pMinus cMass ^ Fintype.card κ * selectedRawSquareEnergy R x
        ∂Measure.pi (fun _ : κ => μ.restrict A) :=
      integral_mono_ae hWI hJ (hWbound.mono (fun x hx => hx.2))
    _ = _ := integral_const_mul _ _
variable {n : ℕ}
section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
theorem high_marked_local_score_ratio  (π activation a V η p pReset)
    (cReset : E → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (y : Fin n → Fin 3) (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      (∫ z, activation z * (∏ i, pReset z i / p i) *
        ∏ i, ternaryMass a (coefficientRegression η g w φ (cReset z) i) V (y i) /
          ternaryMass a (coefficientRegression η g w φ c i) V (y i) ∂π) -
      η ^ 2 * ∑ i, (w i) ^ 2 * (ternaryVarianceDerivative a (y i) /
        ternaryMass a (coefficientRegression η g w φ c i) V (y i)) := by
  have hpP : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hpd i)
  have hqP : highResponseProduct a V η g w φ c y ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => hp i (y i)))
  unfold highMarkedLocalScore highMarkedResponseAction
  rw [sub_div, ← integral_div]
  have hfirst : (fun z => activation z * (∏ i, pReset z i) *
      highResponseProduct a V η g w φ (cReset z) y /
        ((∏ i, p i) * highResponseProduct a V η g w φ c y)) =
      (fun z => activation z * (∏ i, pReset z i / p i) *
        ∏ i, ternaryMass a (coefficientRegression η g w φ (cReset z) i) V (y i) /
          ternaryMass a (coefficientRegression η g w φ c i) V (y i)) := by
    funext z
    simp only [Finset.prod_div_distrib]
    unfold highResponseProduct
    field_simp [hpP, hqP]
  rw [hfirst]
  congr 1
  calc
    _ = η ^ 2 * ((∑ i, (w i) ^ 2 * highResponseVarianceTerm a V η g w φ c y i) /
        highResponseProduct a V η g w φ c y) := by field_simp [hpP, hqP]
    _ = _ := by
      simp_rw [Finset.sum_div, mul_div_assoc,
        high_response_variance_ratio a V η g w φ c y _ (fun i => hp i (y i))]
end
theorem finite_probability_pi_embedding_preserving {I J α : Type*}
    [Fintype I] [Fintype J] [MeasurableSpace α]
    (μ : J → Measure α) [∀ j, IsProbabilityMeasure (μ j)] (e : I ↪ J) :
    MeasurePreserving (fun y : J → α => fun l => y (e l))
      (Measure.pi μ) (Measure.pi (fun l => μ (e l))) := by
  have hc : iIndepFun (fun j (y : J → α) => y j) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ : J => (id : α → α)) (fun _ => aemeasurable_id)
  have hs := iIndepFun.precomp e.injective hc
  refine ⟨measurable_pi_iff.mpr (fun l => measurable_pi_apply (e l)), ?_⟩
  have he := (iIndepFun_iff_map_fun_eq_pi_map
    (fun l => (measurable_pi_apply (e l)).aemeasurable)).mp hs
  simpa only [(measurePreserving_eval μ _).map_eq] using he
theorem high_marked_selected_response_energy {ι E : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace E] {n r : ℕ} (e : Fin r ↪ Fin n)
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ) (ha : a ≠ 0)
    (p : Fin n → ℝ) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b)
    (hw : ∀ i, i ∉ Finset.univ.map e → w i = 0)
    (hReset : ∀ z i, i ∉ Finset.univ.map e → pReset z i = p i) :
    (∫ y, highMarkedLocalScore π activation a V η p pReset cReset g w φ c y ^ 2
      ∂Measure.pi (fun i => ternaryIndexMeasure a (coefficientRegression η g w φ c i) V ha
        (fun b => (hp i b).le))) =
    ∫ y, highMarkedLocalScore π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
      cReset (g ∘ e) (w ∘ e) (φ ∘ e) c y ^ 2
      ∂Measure.pi (fun l => ternaryIndexMeasure a
        (coefficientRegression η (g ∘ e) (w ∘ e) (φ ∘ e) c l) V ha (fun b => (hp (e l) b).le)) := by
  let μ (i : Fin n) := ternaryIndexMeasure a (coefficientRegression η g w φ c i) V ha
    (fun b => (hp i b).le)
  have hpres := finite_probability_pi_embedding_preserving μ e
  let H : (Fin r → Fin 3) → ℝ := fun y =>
    highMarkedLocalScore π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
      cReset (g ∘ e) (w ∘ e) (φ ∘ e) c y ^ 2
  calc
    _ = ∫ y, H (fun l => y (e l)) ∂Measure.pi μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      have h_high_marked_local_score_selected : highMarkedLocalScore π activation a V η p pReset cReset g w φ c y =
      highMarkedLocalScore π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
        cReset (g ∘ e) (w ∘ e) (φ ∘ e) c (y ∘ e) := by
        rw [high_marked_local_score_ratio π activation a V η p pReset cReset g w φ c y hpd hp,
          high_marked_local_score_ratio π activation a V η (p ∘ e) (fun z => pReset z ∘ e)
            cReset (g ∘ e) (w ∘ e) (φ ∘ e) c (y ∘ e) (fun l => hpd (e l))
            (fun l b => hp (e l) b)]
        have hprod (z : E) :
            (∏ i, pReset z i / p i) *
                ∏ i, ternaryMass a (coefficientRegression η g w φ (cReset z) i) V (y i) /
                  ternaryMass a (coefficientRegression η g w φ c i) V (y i) =
            (∏ l : Fin r, pReset z (e l) / p (e l)) *
                ∏ l : Fin r, ternaryMass a (coefficientRegression η g w φ (cReset z) (e l)) V (y (e l)) /
                  ternaryMass a (coefficientRegression η g w φ c (e l)) V (y (e l)) := by
          have h_finite_product_split_embedding (F : Fin n → ℝ) : (∏ i : Fin n, F i) =
            (∏ i ∈ (Finset.univ : Finset (Fin n)) \ Finset.univ.map e, F i) * ∏ l : Fin r, F (e l) := by
            rw [← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.map e)), Finset.prod_map]
          rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
            h_finite_product_split_embedding]
          have ho : (∏ i ∈ (Finset.univ : Finset (Fin n)) \ Finset.univ.map e,
              (pReset z i / p i) *
                (ternaryMass a (coefficientRegression η g w φ (cReset z) i) V (y i) /
                  ternaryMass a (coefficientRegression η g w φ c i) V (y i))) = 1 := by
            apply Finset.prod_eq_one
            intro i hi
            have hiS := (Finset.mem_sdiff.mp hi).2
            rw [hReset z i hiS, div_self (hpd i)]
            have hv : coefficientRegression η g w φ (cReset z) i = coefficientRegression η g w φ c i := by
              simp [coefficientRegression, hw i hiS]
            rw [hv, div_self (hp i (y i)).ne', one_mul]
          rw [ho, one_mul]
        have hsum : (∑ i, (w i) ^ 2 * (ternaryVarianceDerivative a (y i) /
            ternaryMass a (coefficientRegression η g w φ c i) V (y i))) =
            ∑ l : Fin r, (w (e l)) ^ 2 * (ternaryVarianceDerivative a (y (e l)) /
              ternaryMass a (coefficientRegression η g w φ c (e l)) V (y (e l))) := by
          have h_finite_sum_split_embedding (F : Fin n → ℝ) : (∑ i : Fin n, F i) =
            (∑ i ∈ (Finset.univ : Finset (Fin n)) \ Finset.univ.map e, F i) + ∑ l : Fin r, F (e l) := by
            rw [← Finset.sum_sdiff (Finset.subset_univ (Finset.univ.map e)), Finset.sum_map]
          rw [h_finite_sum_split_embedding]
          have ho : (∑ i ∈ (Finset.univ : Finset (Fin n)) \ Finset.univ.map e,
              (w i) ^ 2 * (ternaryVarianceDerivative a (y i) /
                ternaryMass a (coefficientRegression η g w φ c i) V (y i))) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            simp [hw i (Finset.mem_sdiff.mp hi).2]
          rw [ho, zero_add]
        simp_rw [mul_assoc, hprod, hsum]
        rfl
      exact congrArg (fun z : ℝ => z ^ 2)
        h_high_marked_local_score_selected
    _ = ∫ y, H y ∂Measure.pi (fun l => μ (e l)) :=
      (integral_map hpres.measurable.aemeasurable (measurable_of_countable H).aestronglyMeasurable).symm.trans
        (congrArg (fun M => ∫ y, H y ∂M) hpres.map_eq)
    _ = _ := rfl
section
variable {α ι E : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
def highMarkedResponseMass (a V η : ℝ) (g w : α → ℝ) (φ : α → ι → ℝ)
    (c : ι → ℝ) (x : α) (y : Fin 3) : ℝ :=
  ternaryMass a (g x + η * w x * ∑ γ, φ x γ * c γ) V y
def highMarkedSampleNumerator (r : ℕ) (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ)
    (x : Fin r → α) (y : Fin r → Fin 3) : ℝ :=
  highMarkedResponseAction π activation a V η (fun z => pReset z ∘ x) cReset
    (g ∘ x) (w ∘ x) (φ ∘ x) y - η ^ 2 * (∏ i, p (x i)) *
      ∑ i, (w (x i)) ^ 2 * highResponseVarianceTerm a V η (g ∘ x) (w ∘ x) (φ ∘ x) c y i
def highMarkedSampleConditionalEnergy (r : ℕ) (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ) (x : Fin r → α) : ℝ :=
  selectedConditionalScoreEnergy p (highMarkedResponseMass a V η g w φ c)
    (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x
theorem high_marked_sample_energy_integral (r : ℕ) (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (ha : a ≠ 0) (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ) (x : Fin r → α)
    (hp : ∀ z y, 0 < highMarkedResponseMass a V η g w φ c z y) :
    (∫ y, highMarkedLocalScore π activation a V η (p ∘ x) (fun z => pReset z ∘ x) cReset
      (g ∘ x) (w ∘ x) (φ ∘ x) c y ^ 2
      ∂Measure.pi (fun i => ternaryIndexMeasure a
        (coefficientRegression η (g ∘ x) (w ∘ x) (φ ∘ x) c i) V ha (fun y => (hp (x i) y).le))) =
    highMarkedSampleConditionalEnergy r π activation a V η p pReset cReset g w φ c x := by
  rw [ternary_index_product_integral]
  unfold highMarkedSampleConditionalEnergy selectedConditionalScoreEnergy
  apply Finset.sum_congr (by ext y; simp)
  intro y hy
  rfl
def selectedDesignEnumeration  (S : Finset (Fin n)) : Fin S.card ≃ S :=
  (S.orderIsoOfFin rfl).toEquiv
def selectedDesignEmbedding  (S : Finset (Fin n)) : Fin S.card ↪ Fin n :=
  (S.orderEmbOfFin rfl).toEmbedding
theorem selected_design_embedding_map  (S : Finset (Fin n)) :
    Finset.univ.map (selectedDesignEmbedding S) = S := Finset.map_orderEmbOfFin_univ S rfl
theorem high_marked_sample_energy_cell_selected  (A : Set α)
    (S : Finset (Fin n)) (x : Fin n → α) (hx : x ∈ designMembershipCell n A S)
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ) (ha : a ≠ 0)
    (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ)
    (hpd : ∀ z, p z ≠ 0) (hp : ∀ z y, 0 < highMarkedResponseMass a V η g w φ c z y)
    (hw : ∀ z, z ∉ A → w z = 0) (hReset : ∀ e z, z ∉ A → pReset e z = p z) :
    highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c x =
      highMarkedSampleConditionalEnergy S.card π activation a V η p pReset cReset g w φ c
        (x ∘ selectedDesignEmbedding S) := by
  have hmem := design_membership_cell_iff n A S x |>.mp hx
  have hwo (i : Fin n) (hi : i ∉ Finset.univ.map (selectedDesignEmbedding S)) : w (x i) = 0 := by
    rw [selected_design_embedding_map] at hi
    exact hw _ (fun h => hi ((hmem i).mp h))
  have hro (e : E) (i : Fin n) (hi : i ∉ Finset.univ.map (selectedDesignEmbedding S)) :
      pReset e (x i) = p (x i) := by
    rw [selected_design_embedding_map] at hi
    exact hReset e _ (fun h => hi ((hmem i).mp h))
  have he := high_marked_selected_response_energy (selectedDesignEmbedding S) π activation a V η ha
    (p ∘ x) (fun z => pReset z ∘ x) cReset (g ∘ x) (w ∘ x) (φ ∘ x) c
    (fun i => hpd (x i)) (fun i y => hp (x i) y) hwo hro
  rw [high_marked_sample_energy_integral n π activation a V η ha p pReset cReset g w φ c x hp] at he
  have hs := high_marked_sample_energy_integral S.card π activation a V η ha p pReset cReset
    g w φ c (x ∘ selectedDesignEmbedding S) hp
  change _ = (∫ y, highMarkedLocalScore π activation a V η (p ∘ (x ∘ selectedDesignEmbedding S))
    (fun z => pReset z ∘ (x ∘ selectedDesignEmbedding S)) cReset
    (g ∘ (x ∘ selectedDesignEmbedding S)) (w ∘ (x ∘ selectedDesignEmbedding S))
    (φ ∘ (x ∘ selectedDesignEmbedding S)) c y ^ 2 ∂_) at he
  exact he.trans hs
theorem high_marked_design_raw_factorial_series (ν : Measure α) [IsProbabilityMeasure ν]
    (n : ℕ) (A : Set α) (hA : MeasurableSet A) (m pMinus cMass : ℝ)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass) (hm : pMinus ≤ m)
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ) (ha : a ≠ 0)
    (p : α → ℝ) (hpMeas : Measurable p) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ)
    (hqMeas : ∀ y, Measurable (fun x => highMarkedResponseMass a V η g w φ c x y))
    (hprob : IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (p x / m))))
    (hpd : ∀ x, pMinus ≤ p x)
    (hp : ∀ x y, cMass ≤ highMarkedResponseMass a V η g w φ c x y)
    (hw : ∀ x, x ∉ A → w x = 0) (hReset : ∀ e x, x ∉ A → pReset e x = p x)
    (hRMeas : ∀ r y, Measurable (fun x => highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c x y))
    (hRaw : ∀ r, Integrable (selectedRawSquareEnergy
      (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c))
        (Measure.pi (fun _ : Fin r => ν.restrict A))) :
    Integrable (highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c)
      (Measure.pi (fun _ : Fin n => ν.withDensity (fun x => ENNReal.ofReal (p x / m)))) ∧
    (∫ x, highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c x
      ∂Measure.pi (fun _ : Fin n => ν.withDensity (fun x => ENNReal.ofReal (p x / m)))) ≤
      ∑ r ∈ Finset.range (n + 1),
        (↑n * highFixedScoreDenominator pMinus cMass) ^ r / ↑r.factorial *
          ∫ x, selectedRawSquareEnergy
            (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x
              ∂Measure.pi (fun _ : Fin r => ν.restrict A) := by
  let μ := ν.withDensity (fun x => ENNReal.ofReal (p x / m))
  let _ : IsProbabilityMeasure μ := hprob
  let F (r : ℕ) := highMarkedSampleConditionalEnergy r π activation a V η p pReset cReset g w φ c
  let H (S : Finset (Fin n)) (z : S → α) : ℝ := F S.card (z ∘ selectedDesignEnumeration S)
  let J (r : ℕ) := ∫ x, selectedRawSquareEnergy
    (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x
      ∂Measure.pi (fun _ : Fin r => ν.restrict A)
  have hp0 (x : α) : p x ≠ 0 := (hpMinus.trans_le (hpd x)).ne'
  have hq0 (x : α) (y : Fin 3) : 0 < highMarkedResponseMass a V η g w φ c x y := hcMass.trans_le (hp x y)
  have hFI (r : ℕ) := normalized_selected_score_energy_integrable_bound ν A hA m pMinus cMass
    hpMinus hcMass hm p hpMeas (highMarkedResponseMass a V η g w φ c) hqMeas
    (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) (hRMeas r) hprob
    (fun x _ => hpd x) (fun x _ y => hp x y) (hRaw r)
  have hHI (S : Finset (Fin n)) : Integrable (H S) (Measure.pi (fun _ : S => μ.restrict A)) :=
    finite_pi_reindex_integrable (μ.restrict A) (selectedDesignEnumeration S).symm (F S.card) (hFI S.card).1
  have hEq (S : Finset (Fin n)) (x : Fin n → α) (hx : x ∈ designMembershipCell n A S) :
      F n x = H S (fun i : S => x i.val) :=
    high_marked_sample_energy_cell_selected A S x hx π activation a V η ha p pReset cReset
      g w φ c hp0 hq0 hw hReset
  have hcover : (⋃ S : Finset (Fin n), designMembershipCell n A S) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    apply Set.mem_iUnion.mpr
    refine ⟨Finset.univ.filter (fun i => x i ∈ A), ?_⟩
    rw [design_membership_cell_iff]
    intro i
    simp
  have hi : IntegrableOn (F n) (⋃ S : Finset (Fin n), designMembershipCell n A S)
      (Measure.pi (fun _ : Fin n => μ)) := by
    apply integrableOn_finite_iUnion.mpr
    intro S
    have h_iid_cell_selected_integrable : IntegrableOn (fun x : Fin n → α => (H S) (fun i : S => x i.val))
      (designMembershipCell n A S) (Measure.pi (fun _ : Fin n => μ)) := by
      have hHI  := hHI S
      rw [IntegrableOn, designMembershipCell, Measure.restrict_pi_pi]
      have hs := measurePreserving_piEquivPiSubtypeProd
        (fun i : Fin n => μ.restrict (if i ∈ S then A else Aᶜ)) (fun i => i ∈ S)
      have hι : (Subtype.fintype (fun i : Fin n => i ∈ S) : Fintype S) = Finset.Subtype.fintype S := Subsingleton.elim _ _
      rw [hι] at hs
      have hin : (fun i : S => μ.restrict (if i.val ∈ S then A else Aᶜ)) =
          (fun _ : S => μ.restrict A) := by
        funext i
        rw [ite_eq_left i.property]
      have hout : (fun i : {i : Fin n // i ∉ S} => μ.restrict (if i.val ∈ S then A else Aᶜ)) =
          (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ) := by
        funext i
        rw [ite_eq_right i.property]
      rw [hin, hout] at hs
      have hp : Integrable (fun z : (S → α) × ({i : Fin n // i ∉ S} → α) => (H S) z.1)
          ((Measure.pi (fun _ : S => μ.restrict A)).prod
            (Measure.pi (fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ))) := hHI.comp_fst _
      have hh := hs.integrable_comp_of_integrable hp
      exact hh
    have hsel := h_iid_cell_selected_integrable
    apply hsel.congr
    filter_upwards [ae_restrict_mem (design_membership_cell_measurable n A hA S)] with x hx
    exact (hEq S x hx).symm
  have hFn  :=
    by simpa only [hcover, integrableOn_univ] using hi
  refine ⟨hFn, ?_⟩
  apply iid_local_energy_le_factorial_spatial_series μ n A hA (F n) hFn H hHI
    (fun S z => selected_conditional_score_energy_nonneg p (highMarkedResponseMass a V η g w φ c)
      (fun x y => (hq0 x y).le) _ _) (fun S x hx => (hEq S x hx).le)
    (highFixedScoreDenominator pMinus cMass) (high_fixed_score_denominator_pos hpMinus hcMass).le J
    (fun r => integral_nonneg (fun x => Finset.sum_nonneg (fun y _ => sq_nonneg _)))
  intro S
  change (∫ z, F S.card (z ∘ selectedDesignEnumeration S) ∂Measure.pi (fun _ : S => μ.restrict A)) ≤ _
  have he : (∫ z, F S.card (z ∘ selectedDesignEnumeration S) ∂Measure.pi (fun _ : S => μ.restrict A)) =
      ∫ z, F S.card z ∂Measure.pi (fun _ : Fin S.card => μ.restrict A) :=
    finite_pi_reindex_integral (μ.restrict A) (selectedDesignEnumeration S).symm (F S.card)
  rw [he]
  have hs := (hFI S.card).2
  simp only [Fintype.card_fin] at hs
  change (∫ z, F S.card z ∂Measure.pi (fun _ : Fin S.card => μ.restrict A)) ≤
    highFixedScoreDenominator pMinus cMass ^ S.card * J S.card at hs
  exact hs
end
section
variable {α ι E : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
theorem highMarkedResponseMass_measurable (a V η : ℝ) (g w : α → ℝ)
    (hg : Measurable g) (hw : Measurable w) (φ : α → ι → ℝ)
    (hφ : ∀ γ, Measurable (fun x => φ x γ)) (c : ι → ℝ) (y : Fin 3) :
    Measurable (fun x => highMarkedResponseMass a V η g w φ c x y) := by
  apply ternaryMass_measurable_comp
  exact hg.add ((measurable_const.mul hw).mul
    (Finset.measurable_sum _ (fun γ _ => (hφ γ).mul_const (c γ))))
theorem highMarkedSampleNumerator_measurable (r π) [SFinite π]
    (activation : E → ℝ) (hAct : Measurable activation) (a V η : ℝ)
    (p : α → ℝ) (hp : Measurable p) (pReset : E → α → ℝ)
    (hpReset : Measurable (Function.uncurry pReset)) (cReset : E → ι → ℝ)
    (hcReset : ∀ γ, Measurable (fun e => cReset e γ))
    (g w ) (hg : Measurable g) (hw : Measurable w)
    (φ ) (hφ : ∀ γ, Measurable (fun x => φ x γ))
    (c : ι → ℝ) (y : Fin r → Fin 3) :
    Measurable (fun x => highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c x y) := by
  have hReset (i : Fin r) : Measurable (fun z : E × (Fin r → α) => pReset z.1 (z.2 i)) :=
    hpReset.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hreg (i : Fin r) : Measurable (fun z : E × (Fin r → α) =>
      coefficientRegression η (g ∘ z.2) (w ∘ z.2) (φ ∘ z.2) (cReset z.1) i) := by
    unfold coefficientRegression
    exact (hg.comp ((measurable_pi_apply i).comp measurable_snd)).add
      ((measurable_const.mul (hw.comp ((measurable_pi_apply i).comp measurable_snd))).mul
        (Finset.measurable_sum _ (fun γ _ =>
          ((hφ γ).comp ((measurable_pi_apply i).comp measurable_snd)).mul
            ((hcReset γ).comp measurable_fst))))
  have hproduct : Measurable (fun z : E × (Fin r → α) =>
      highResponseProduct a V η (g ∘ z.2) (w ∘ z.2) (φ ∘ z.2) (cReset z.1) y) :=
    Finset.measurable_prod _ (fun i _ => ternaryMass_measurable_comp a V _ (hreg i) (y i))
  have hMarked : Measurable (fun z : E × (Fin r → α) =>
      activation z.1 * (∏ i, pReset z.1 (z.2 i)) *
        highResponseProduct a V η (g ∘ z.2) (w ∘ z.2) (φ ∘ z.2) (cReset z.1) y) :=
    ((hAct.comp measurable_fst).mul (Finset.measurable_prod _ (fun i _ => hReset i))).mul hproduct
  have hq (i : Fin r) : Measurable (fun x : Fin r → α =>
      ternaryMass a (coefficientRegression η (g ∘ x) (w ∘ x) (φ ∘ x) c i) V (y i)) :=
    (highMarkedResponseMass_measurable a V η g w hg hw φ hφ c (y i)).comp (measurable_pi_apply i)
  have hvar (i : Fin r) : Measurable (fun x : Fin r → α =>
      highResponseVarianceTerm a V η (g ∘ x) (w ∘ x) (φ ∘ x) c y i) := by
    unfold highResponseVarianceTerm
    exact measurable_const.mul (Finset.measurable_prod _ (fun l _ => hq l))
  exact (hMarked.stronglyMeasurable.integral_prod_left'.measurable).sub ((measurable_const.mul
    (Finset.measurable_prod _ (fun i _ => hp.comp (measurable_pi_apply i)))).mul
      (Finset.measurable_sum _ (fun i _ =>
        ((hw.comp (measurable_pi_apply i)).pow_const 2).mul (hvar i))))
end
end NearlyMinimax
