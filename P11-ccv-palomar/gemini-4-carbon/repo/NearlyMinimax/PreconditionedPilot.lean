module

public import NearlyMinimax.AnchoredFeatures
public import NearlyMinimax.AnchoredGeometry
public import NearlyMinimax.BoundedPairMeanOperators
public import NearlyMinimax.FieldLiftCovariance
public import NearlyMinimax.SimilarInverseDerivatives

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators Classical ENNReal MatrixOrder Matrix.Norms.L2Operator
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private lemma cube_continuous_bound {d : ℕ} {g : Covariate d → ℝ} (hg : Continuous g) :
    ∃ M : ℝ, 0 < M ∧ ∀ u ∈ unitCube d, g u ≤ M := by
  obtain ⟨M, hM⟩ := (unitCube_isCompact d).bddAbove_image hg.continuousOn
  exact ⟨max 1 M, zero_lt_one.trans_le (le_max_left _ _),
    fun u hu => (hM (mem_image_of_mem _ hu)).trans (le_max_right _ _)⟩

-- 1. Anchored monomial expansions, basis & cardinality (`AnchoredExpansion`, `AnchoredBasis`, `AnchoredCard`)

section AnchoredPoly
open MvPolynomial

def dyadicFeaturePolynomial {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (γ : AnchoredIndex d ℓ) : MvPolynomial (Fin d) ℝ :=
  ∏ i, (C ((2 : ℝ) ^ j) * (X i - C (x i))) ^ (γ.val i).val

theorem dyadicFeaturePolynomial_eval {d ℓ : ℕ} (j : ℕ) (x z : Covariate d)
    (γ : AnchoredIndex d ℓ) :
    eval z (dyadicFeaturePolynomial j x γ) = dyadicAnchoredFeature j x z γ := by
  simp only [dyadicFeaturePolynomial, map_prod, map_pow, map_mul, map_sub, eval_C, eval_X,
    dyadicAnchoredFeature, anchoredMonomial]

theorem dyadicFeaturePolynomial_degree {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (γ : AnchoredIndex d ℓ) : (dyadicFeaturePolynomial j x γ).totalDegree ≤ ℓ := by
  refine (totalDegree_finsetProd Finset.univ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans γ.property.2)
  have hlin : (C ((2 : ℝ) ^ j) * (X i - C (x i))).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simp only [totalDegree_C, zero_add]; exact (totalDegree_sub _ _).trans (by simp))
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left _ hlin)

private lemma poly_coeff_mul_continuous {Y σ : Type*} [TopologicalSpace Y] [DecidableEq σ]
    {P Q : Y → MvPolynomial σ ℝ} (hP : ∀ e, Continuous fun x => (P x).coeff e)
    (hQ : ∀ e, Continuous fun x => (Q x).coeff e) (e : σ →₀ ℕ) :
    Continuous fun x => (P x * Q x).coeff e := by
  simp only [coeff_mul]
  exact continuous_finset_sum _ fun v _ => (hP v.1).mul (hQ v.2)

theorem dyadicFeaturePolynomial_coeff_continuous {d ℓ : ℕ} (j : ℕ)
    (γ : AnchoredIndex d ℓ) (e : Fin d →₀ ℕ) :
    Continuous fun x : Covariate d => (dyadicFeaturePolynomial j x γ).coeff e := by
  have hpow {P : Covariate d → MvPolynomial (Fin d) ℝ} (hP : ∀ e, Continuous fun x => (P x).coeff e)
      (n : ℕ) : ∀ e, Continuous fun x => (P x ^ n).coeff e := by
    induction n with
    | zero => exact fun _ => continuous_const
    | succ n ih => intro e; simp_rw [pow_succ]; exact poly_coeff_mul_continuous ih hP e
  have hprod : ∀ (s : Finset (Fin d)) (e : Fin d →₀ ℕ),
      Continuous fun x : Covariate d => (∏ i ∈ s, (C ((2 : ℝ) ^ j) * (X i - C (x i))) ^ (γ.val i).val).coeff e := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro e; simpa using (continuous_const : Continuous fun _ : Covariate d => (1 : MvPolynomial (Fin d) ℝ).coeff e)
    | @insert i s hi ih =>
      intro e; simp_rw [Finset.prod_insert hi]
      refine poly_coeff_mul_continuous (hpow (fun e' => ?_) (γ.val i).val) ih e
      refine poly_coeff_mul_continuous (fun _ => continuous_const) (fun e'' => ?_) e'
      simp only [coeff_sub, coeff_C]
      refine continuous_const.sub ?_
      by_cases h0 : 0 = e'' <;> simp [h0, continuous_apply, continuous_const]
  exact hprod Finset.univ e

private theorem polynomial_as_anchored_sum {d ℓ : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (hP : P.totalDegree ≤ ℓ) (hzero : P.coeff 0 = 0) :
    P = anchoredPolynomial fun γ : AnchoredIndex d ℓ => P.coeff (anchoredExponent γ) := by
  let pred (γ : PolynomialBox d ℓ) : Prop := 0 < ∑ i, (γ i).val ∧ (∑ i, (γ i).val) ≤ ℓ
  let f (γ : PolynomialBox d ℓ) : MvPolynomial (Fin d) ℝ :=
    monomial (polynomialBoxExponent γ) (P.coeff (polynomialBoxExponent γ))
  have hz (γ : PolynomialBox d ℓ) (hγ : ¬ pred γ) : f γ = 0 := by
    have hn : P.coeff (polynomialBoxExponent γ) = 0 := by
      by_contra hc
      have hs := (le_totalDegree (mem_support_iff.mpr hc)).trans hP
      rw [Finsupp.sum_fintype _ _ fun _ => rfl] at hs
      simp only [polynomial_box_exponent_apply] at hs
      refine hγ ⟨?_, hs⟩
      by_contra hnot
      have hs0 : (∑ i, (γ i).val) = 0 := by omega
      have he : polynomialBoxExponent γ = 0 := by
        ext i
        have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (γ j).val) (Finset.mem_univ i)
        simp only [hs0, polynomial_box_exponent_apply, Finsupp.zero_apply] at hi ⊢; omega
      exact hc (he ▸ hzero)
    simp only [f, hn, map_zero]
  have hsum := Fintype.sum_subtype_add_sum_subtype pred f
  have hc0 : (∑ γ : {γ : PolynomialBox d ℓ // ¬ pred γ}, f γ.val) = 0 :=
    Finset.sum_eq_zero fun γ _ => hz γ.val γ.property
  rw [hc0, add_zero] at hsum
  exact (polynomial_as_box_sum P hP).trans hsum.symm

theorem polynomial_centered_representation {d ℓ : ℕ} (u : Covariate d)
    (P : MvPolynomial (Fin d) ℝ) (hP : P.totalDegree ≤ ℓ) (hu : eval u P = 0) :
    ∃ c : AnchoredIndex d ℓ → ℝ, ∀ z : Covariate d,
      eval z P = ∑ γ, c γ * anchoredFeature u z γ := by
  let Q : MvPolynomial (Fin d) ℝ :=
    ∑ γ : PolynomialBox d ℓ, C (P.coeff (polynomialBoxExponent γ)) * ∏ i, (C (u i) + X i) ^ (γ i).val
  have hQeval (v : Covariate d) : eval v Q = eval (fun i => u i + v i) P := by
    rw [polynomial_box_evaluation P hP]
    simp only [Q, map_sum, map_mul, map_prod, map_pow, map_add, eval_C, eval_X]
  have hQ : Q.totalDegree ≤ ℓ := by
    refine totalDegree_finsetSum_le fun γ _ => ?_
    by_cases hc : P.coeff (polynomialBoxExponent γ) = 0
    · simp [hc]
    have hs := (le_totalDegree (mem_support_iff.mpr hc)).trans hP
    rw [Finsupp.sum_fintype _ _ fun _ => rfl] at hs
    simp only [polynomial_box_exponent_apply] at hs
    refine (totalDegree_mul _ _).trans ?_
    simp only [totalDegree_C, zero_add]
    refine (totalDegree_finsetProd Finset.univ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans hs)
    have hl : (C (u i) + X i).totalDegree ≤ 1 := (totalDegree_add _ _).trans (max_le (by simp) (by simp))
    exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left _ hl)
  have hQ0 : Q.coeff 0 = 0 := by
    rw [← constantCoeff_eq, ← eval_zero, hQeval 0]
    simpa only [Pi.zero_apply, add_zero] using hu
  refine ⟨fun γ => Q.coeff (anchoredExponent γ), fun z => ?_⟩
  have he := hQeval (z - u)
  rw [show (fun i => u i + (z - u) i) = z from funext fun _ => by simp] at he
  exact he.symm.trans ((congrArg (eval (z - u)) (polynomial_as_anchored_sum Q hQ hQ0)).trans (anchoredPolynomial_eval _ _))

end AnchoredPoly

private abbrev TotalDegreeIndex (d ℓ : ℕ) := {γ : PolynomialBox d ℓ // (∑ i, (γ i).val) ≤ ℓ}

theorem anchoredIndex_card (d ℓ : ℕ) :
    Fintype.card (AnchoredIndex d ℓ) = (d + ℓ).choose d - 1 := by
  let eSlack : TotalDegreeIndex d ℓ ≃ {v : Option (Fin d) → ℕ // ∑ i, v i = ℓ} :=
    { toFun := fun γ => ⟨fun i => i.casesOn (ℓ - ∑ j, (γ.val j).val) fun j => (γ.val j).val, by
        rw [Fintype.sum_option]; exact Nat.sub_add_cancel γ.property⟩
      invFun := fun v => ⟨fun i => ⟨v.val (some i), by
        have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (v.val j)) (Finset.mem_univ (some i))
        rw [v.property] at hi; omega⟩, by
        have h := v.property; rw [Fintype.sum_option] at h
        exact Nat.le.intro (by simpa [Nat.add_comm] using h)⟩
      left_inv := fun _ => Subtype.ext <| funext fun _ => Fin.ext rfl
      right_inv := fun v => Subtype.ext <| funext fun i => by
        cases i with
        | none => change ℓ - ∑ j, v.val (some j) = v.val none
                  have h := v.property; rw [Fintype.sum_option] at h; omega
        | some _ => rfl }
  have hcard_tot : Fintype.card (TotalDegreeIndex d ℓ) = (d + ℓ).choose d := by
    rw [Fintype.card_congr (eSlack.trans (Sym.equivNatSumOfFintype (Option (Fin d)) ℓ).symm),
      Sym.card_sym_eq_choose]
    simp only [Fintype.card_option, Fintype.card_fin, show d + 1 + ℓ - 1 = d + ℓ by omega]
    simpa only [Nat.add_sub_cancel] using (Nat.choose_symm (show ℓ ≤ d + ℓ by omega)).symm
  let eNz : AnchoredIndex d ℓ ≃ {γ : TotalDegreeIndex d ℓ // ¬ (∑ i, (γ.val i).val) = 0} :=
    ⟨fun γ => ⟨⟨γ.val, γ.property.2⟩, ne_of_gt γ.property.1⟩,
     fun γ => ⟨γ.val.val, Nat.pos_of_ne_zero γ.property, γ.val.property⟩, fun _ => rfl, fun _ => rfl⟩
  letI : Unique {γ : TotalDegreeIndex d ℓ // (∑ i, (γ.val i).val) = 0} :=
    { default := ⟨⟨fun _ => 0, by simp⟩, by simp⟩
      uniq := fun γ => Subtype.ext <| Subtype.ext <| funext fun i => Fin.ext <| by
        have hi := Finset.single_le_sum (f := fun j => (γ.val.val j).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        rw [γ.property] at hi; exact Nat.eq_zero_of_le_zero hi }
  rw [Fintype.card_congr eNz, Fintype.card_subtype_compl, hcard_tot, Fintype.card_unique]

-- 2. Anchored Gram bounds, spectrum & population moments (`AnchoredGramBounds`, `AnchoredSpectrum`, `AnchoredMoments`)

abbrev AnchoredCoefficientSpace (d ℓ : ℕ) := EuclideanSpace ℝ (AnchoredIndex d ℓ)

def anchoredQuadratic {d ℓ : ℕ} (u : Covariate d) (c : AnchoredCoefficientSpace d ℓ) : ℝ :=
  c.ofLp ⬝ᵥ (anchoredGram u *ᵥ c.ofLp)

private theorem anchoredGram_entry_continuous {d ℓ : ℕ} (γ δ : AnchoredIndex d ℓ) :
    Continuous fun u => anchoredGram u γ δ :=
  continuous_parametric_integral_of_continuous
    ((anchoredFeature_continuous γ).mul (anchoredFeature_continuous δ)) (unitCube_isCompact d)

private theorem anchoredQuadratic_continuous {d ℓ : ℕ} :
    Continuous fun z : Covariate d × AnchoredCoefficientSpace d ℓ => anchoredQuadratic z.1 z.2 := by
  change Continuous fun z : Covariate d × AnchoredCoefficientSpace d ℓ =>
    ∑ γ, z.2 γ * ∑ δ, anchoredGram z.1 γ δ * z.2 δ
  exact continuous_finset_sum _ fun γ _ => ((PiLp.continuous_apply 2 _ γ).comp continuous_snd).mul
    (continuous_finset_sum _ fun δ _ => ((anchoredGram_entry_continuous γ δ).comp continuous_fst).mul
      ((PiLp.continuous_apply 2 _ δ).comp continuous_snd))

theorem anchoredGram_uniform_bounds {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)] :
    ∃ cB CB : ℝ, 0 < cB ∧ 0 < CB ∧
      ∀ u ∈ unitCube d, ∀ c : AnchoredCoefficientSpace d ℓ,
        cB * ‖c‖ ^ 2 ≤ anchoredQuadratic u c ∧ anchoredQuadratic u c ≤ CB * ‖c‖ ^ 2 := by
  let S : Set (Covariate d × AnchoredCoefficientSpace d ℓ) := unitCube d ×ˢ Metric.sphere 0 1
  have hS : IsCompact S := (unitCube_isCompact d).prod (isCompact_sphere 0 1)
  have hSne : S.Nonempty := ⟨(0, EuclideanSpace.single (Classical.arbitrary _) 1),
    fun _ => by simp, by simp [Metric.mem_sphere, dist_eq_norm, EuclideanSpace.norm_single]⟩
  obtain ⟨zmin, hzmin, hmin⟩ := hS.exists_isMinOn hSne anchoredQuadratic_continuous.continuousOn
  obtain ⟨zmax, _, hmax⟩ := hS.exists_isMaxOn hSne anchoredQuadratic_continuous.continuousOn
  have hcB : 0 < anchoredQuadratic zmin.1 zmin.2 := by
    have hne : zmin.2.ofLp ≠ 0 := fun h => by
      have hh := hzmin.2; simp [Metric.mem_sphere, show zmin.2 = 0 from PiLp.ext (congrFun h)] at hh
    simpa only [star_trivial, anchoredQuadratic] using (anchoredGram_posDef (ℓ := ℓ) zmin.1).dotProduct_mulVec_pos hne
  refine ⟨anchoredQuadratic zmin.1 zmin.2, max 1 (anchoredQuadratic zmax.1 zmax.2),
    hcB, zero_lt_one.trans_le (le_max_left _ _), fun u hu c => ?_⟩
  by_cases hc : c = 0
  · subst c; simp [anchoredQuadratic]
  have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  let c' : AnchoredCoefficientSpace d ℓ := ‖c‖⁻¹ • c
  have huc : (u, c') ∈ S := ⟨hu, by simp [c', Metric.mem_sphere, dist_eq_norm, norm_smul,
    Real.norm_eq_abs, abs_of_pos hn, hn.ne', inv_mul_cancel₀]⟩
  have hscale : anchoredQuadratic u c = ‖c‖ ^ 2 * anchoredQuadratic u c' := by
    have hr : ‖c‖ • c' = c := by dsimp [c']; rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    conv_lhs => rw [← hr]
    change (∑ γ, (‖c‖ * c' γ) * ∑ δ, anchoredGram u γ δ * (‖c‖ * c' δ)) =
      ‖c‖ ^ 2 * ∑ γ, c' γ * ∑ δ, anchoredGram u γ δ * c' δ
    simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hscale]
  exact ⟨by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hmin huc) (sq_nonneg ‖c‖),
    by simpa only [mul_comm] using mul_le_mul_of_nonneg_left ((hmax huc).trans (le_max_right 1 _)) (sq_nonneg ‖c‖)⟩

theorem anchoredIndex_nonempty {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) :
    Nonempty (AnchoredIndex d ℓ) := by
  let i0 : Fin d := ⟨0, hd⟩
  let γ : PolynomialBox d ℓ := fun i => if i = i0 then ⟨1, by omega⟩ else 0
  have hs : (∑ i, (γ i).val) = 1 := by simp only [γ, apply_ite]; change (∑ i, if i = i0 then 1 else 0) = 1; simp
  exact ⟨⟨γ, by rw [hs]; exact ⟨by norm_num, hℓ⟩⟩⟩

def anchoredDensityGram {d ℓ : ℕ} (u : Covariate d) (p : Covariate d → ℝ) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  fun γ δ => ∫ w, p w * (anchoredFeature u w γ * anchoredFeature u w δ) ∂cubeVolume d

theorem anchoredDensityGram_isHermitian {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) : (anchoredDensityGram (ℓ := ℓ) u p).IsHermitian := by
  ext γ δ; simp only [conjTranspose_apply, star_trivial, anchoredDensityGram]
  exact congrArg _ (funext fun w => by rw [mul_comm (anchoredFeature u w δ)])

theorem anchoredDensityGram_product_integrable {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) (hpmeas : Measurable p) (b : ℝ)
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) (γ δ : AnchoredIndex d ℓ) :
    Integrable (fun w => p w * (anchoredFeature u w γ * anchoredFeature u w δ)) (cubeVolume d) :=
  (anchoredFeature_product_integrable u γ δ).bdd_mul hpmeas.aestronglyMeasurable
    (hp.mono fun _ hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2)

theorem anchoredDensityGram_quadratic_bounds {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) (hpmeas : Measurable p) (a b : ℝ) (ha : 0 ≤ a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) (c : AnchoredIndex d ℓ → ℝ) :
    a * (c ⬝ᵥ (anchoredGram u *ᵥ c)) ≤ c ⬝ᵥ (anchoredDensityGram u p *ᵥ c) ∧
      c ⬝ᵥ (anchoredDensityGram u p *ᵥ c) ≤ b * (c ⬝ᵥ (anchoredGram u *ᵥ c)) := by
  have hp0 : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b := hp.mono fun _ hw => ⟨ha.trans hw.1, hw.2⟩
  have hquad : c ⬝ᵥ (anchoredDensityGram u p *ᵥ c) =
      ∫ w, p w * (∑ γ, c γ * anchoredFeature u w γ) ^ 2 ∂cubeVolume d := by
    have heq : (fun w => p w * (∑ γ, c γ * anchoredFeature u w γ) ^ 2) =
        fun w => ∑ γ, ∑ δ, c γ * (p w * (anchoredFeature u w γ * anchoredFeature u w δ)) * c δ :=
      funext fun _ => by
        rw [pow_two, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [heq, integral_finset_sum _ fun γ _ => integrable_finset_sum _ fun δ _ =>
      ((anchoredDensityGram_product_integrable u p hpmeas b hp0 γ δ).const_mul (c γ)).mul_const (c δ)]
    change (∑ γ, c γ * ∑ δ, anchoredDensityGram u p γ δ * c δ) = _
    simp only [Finset.mul_sum, anchoredDensityGram]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [integral_finset_sum _ fun δ _ =>
      ((anchoredDensityGram_product_integrable u p hpmeas b hp0 γ δ).const_mul (c γ)).mul_const (c δ)]
    simp_rw [integral_mul_const, integral_const_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  let f (w : Covariate d) := (∑ γ, c γ * anchoredFeature u w γ) ^ 2
  have hf : Continuous f := (continuous_finset_sum _ fun γ _ =>
    ((anchoredMonomial_continuous γ).comp (continuous_id.sub continuous_const)).const_mul (c γ)).pow 2
  have hi : Integrable f (cubeVolume d) := ContinuousOn.integrableOn_compact (unitCube_isCompact d) hf.continuousOn
  have hpi : Integrable (fun w => p w * f w) (cubeVolume d) :=
    hi.bdd_mul hpmeas.aestronglyMeasurable (hp0.mono fun _ hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2)
  rw [anchoredGram_quadratic, hquad, ← integral_const_mul, ← integral_const_mul]
  exact ⟨integral_mono_ae (hi.const_mul a) hpi (hp.mono fun _ hw => mul_le_mul_of_nonneg_right hw.1 (sq_nonneg _)),
    integral_mono_ae hpi (hi.const_mul b) (hp.mono fun _ hw => mul_le_mul_of_nonneg_right hw.2 (sq_nonneg _))⟩

theorem anchoredDensityGram_posDef {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) (hpmeas : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) :
    (anchoredDensityGram (ℓ := ℓ) u p).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (anchoredDensityGram_isHermitian u p) fun c hc => ?_
  simp only [star_trivial]
  have hB : 0 < c ⬝ᵥ (anchoredGram u *ᵥ c) := by simpa only [star_trivial] using (anchoredGram_posDef u).dotProduct_mulVec_pos hc
  exact (mul_pos ha hB).trans_le (anchoredDensityGram_quadratic_bounds u p hpmeas a b ha.le hp c).1

def anchoredWhitening {d ℓ : ℕ} (u : Covariate d) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ := (CFC.sqrt (anchoredGram u))⁻¹

theorem anchoredGram_sqrt_isUnit {d ℓ : ℕ} (u : Covariate d) :
    IsUnit (CFC.sqrt (anchoredGram (ℓ := ℓ) u)) :=
  (CFC.isUnit_sqrt_iff _ (anchoredGram_posDef u).posSemidef.nonneg).mpr (anchoredGram_posDef u).isUnit

private theorem anchoredWhitening_isHermitian {d ℓ : ℕ} (u : Covariate d) :
    (anchoredWhitening (ℓ := ℓ) u).IsHermitian :=
  (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg (anchoredGram u))).isHermitian.inv

private theorem anchoredWhitening_gram_identity {d ℓ : ℕ} (u : Covariate d) :
    anchoredWhitening (ℓ := ℓ) u * anchoredGram u * anchoredWhitening u = 1 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_sqrt_isUnit (ℓ := ℓ) u)
  calc _ = anchoredWhitening u * (CFC.sqrt (anchoredGram u) * CFC.sqrt (anchoredGram u)) * anchoredWhitening u :=
          congrArg (anchoredWhitening u * · * anchoredWhitening u)
            (CFC.sqrt_mul_sqrt_self (anchoredGram u) (anchoredGram_posDef u).posSemidef.nonneg).symm
    _ = 1 := by
          unfold anchoredWhitening
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul, Matrix.mul_nonsing_inv _ hdet]

def anchoredWhitenedGram {d ℓ : ℕ} (u : Covariate d) (p : Covariate d → ℝ) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  anchoredWhitening u * anchoredDensityGram u p * anchoredWhitening u

theorem anchoredWhitenedGram_isHermitian {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) : (anchoredWhitenedGram (ℓ := ℓ) u p).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_mul (anchoredWhitening (ℓ := ℓ) u) (anchoredDensityGram_isHermitian u p)
  rwa [(anchoredWhitening_isHermitian u).eq] at h

theorem anchoredWhitenedGram_spectrum {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) (hpmeas : Measurable p) (a b : ℝ) (ha : 0 ≤ a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) :
    spectrum ℝ (anchoredWhitenedGram (ℓ := ℓ) u p) ⊆ Set.Icc a b := by
  have hlo_psd : (anchoredDensityGram (ℓ := ℓ) u p - a • anchoredGram u).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((anchoredDensityGram_isHermitian u p).sub ((anchoredGram_isHermitian u).smul (by simp [IsSelfAdjoint]))) fun c => ?_
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact sub_nonneg.mpr (anchoredDensityGram_quadratic_bounds u p hpmeas a b ha hp c).1
  have hup_psd : (b • anchoredGram u - anchoredDensityGram (ℓ := ℓ) u p).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (((anchoredGram_isHermitian u).smul (by simp [IsSelfAdjoint])).sub (anchoredDensityGram_isHermitian u p)) fun c => ?_
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact sub_nonneg.mpr (anchoredDensityGram_quadratic_bounds u p hpmeas a b ha hp c).2
  have hlo := hlo_psd.conjTranspose_mul_mul_same (anchoredWhitening u)
  have hup := hup_psd.conjTranspose_mul_mul_same (anchoredWhitening u)
  rw [(anchoredWhitening_isHermitian u).eq] at hlo hup
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, anchoredWhitening_gram_identity] at hlo hup
  have hlo1 : a • (1 : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) ≤ anchoredWhitenedGram u p := hlo
  have hup1 : anchoredWhitenedGram u p ≤ b • (1 : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) := hup
  have hlo' : algebraMap ℝ (Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) a ≤ anchoredWhitenedGram u p := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hlo1
  have hup' : anchoredWhitenedGram u p ≤ algebraMap ℝ (Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) b := by
    simpa only [Algebra.algebraMap_eq_smul_one] using hup1
  exact fun t ht => ⟨(algebraMap_le_iff_le_spectrum (anchoredWhitenedGram_isHermitian u p)).mp hlo' t ht,
    (le_algebraMap_iff_spectrum_le (anchoredWhitenedGram_isHermitian u p)).mp hup' t ht⟩

def anchoredSimilarityUnit {d ℓ : ℕ} (u : Covariate d) :
    (Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ)ˣ :=
  (anchoredGram_sqrt_isUnit (ℓ := ℓ) u).unit⁻¹

@[simp] theorem anchoredSimilarityUnit_val {d ℓ : ℕ} (u : Covariate d) :
    (anchoredSimilarityUnit (ℓ := ℓ) u).val = anchoredWhitening u := by
  rw [anchoredSimilarityUnit, Matrix.coe_units_inv, IsUnit.unit_spec]; rfl

@[simp] theorem anchoredSimilarityUnit_inv_val {d ℓ : ℕ} (u : Covariate d) :
    ((anchoredSimilarityUnit (ℓ := ℓ) u)⁻¹).val = CFC.sqrt (anchoredGram u) := by
  simp only [anchoredSimilarityUnit, inv_inv, IsUnit.unit_spec]

private theorem anchoredWhitening_square {d ℓ : ℕ} (u : Covariate d) :
    (anchoredGram (ℓ := ℓ) u)⁻¹ = anchoredWhitening u * anchoredWhitening u :=
  (congrArg Inv.inv (CFC.sqrt_mul_sqrt_self (anchoredGram u) (anchoredGram_posDef u).posSemidef.nonneg).symm).trans
    (Matrix.mul_inv_rev _ _)

theorem anchored_preconditioned_similarity {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) :
    ((anchoredSimilarityUnit (ℓ := ℓ) u)⁻¹).val * ((anchoredGram u)⁻¹ * anchoredDensityGram u p) *
      (anchoredSimilarityUnit (ℓ := ℓ) u).val = anchoredWhitenedGram u p := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_sqrt_isUnit (ℓ := ℓ) u)
  rw [anchoredSimilarityUnit_val, anchoredSimilarityUnit_inv_val, anchoredWhitening_square]
  simp only [← Matrix.mul_assoc, anchoredWhitenedGram]
  rw [show CFC.sqrt (anchoredGram u) * anchoredWhitening u = 1 from Matrix.mul_nonsing_inv _ hdet, one_mul]

theorem anchoredGram_continuous {d ℓ : ℕ} : Continuous (anchoredGram (d := d) (ℓ := ℓ)) :=
  continuous_matrix anchoredGram_entry_continuous

private theorem anchoredGram_sqrt_continuous {d ℓ : ℕ} :
    Continuous fun u : Covariate d => CFC.sqrt (anchoredGram (ℓ := ℓ) u) :=
  CFC.continuousOn_sqrt.comp_continuous anchoredGram_continuous fun u => (anchoredGram_posDef u).posSemidef.nonneg

private theorem anchoredWhitening_continuous {d ℓ : ℕ} : Continuous (anchoredWhitening (d := d) (ℓ := ℓ)) := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_sqrt_isUnit (ℓ := ℓ) u)
  have hinv : ContinuousAt Ring.inverse (CFC.sqrt (anchoredGram (ℓ := ℓ) u)).det := by
    rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]
    exact continuousAt_inv₀ hdet.ne_zero
  exact (continuousAt_matrix_inv _ hinv).comp (f := fun v : Covariate d => CFC.sqrt (anchoredGram (ℓ := ℓ) v))
    (anchoredGram_sqrt_continuous.continuousAt (x := u))

theorem anchoredSimilarityUnit_uniform_condition {d ℓ : ℕ} :
    ∃ χ : ℝ, 0 < χ ∧ ∀ u ∈ unitCube d,
      ‖(anchoredSimilarityUnit (ℓ := ℓ) u).val‖ * ‖((anchoredSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ := by
  obtain ⟨χ, hχ, hb⟩ := cube_continuous_bound
    ((anchoredWhitening_continuous (d := d) (ℓ := ℓ)).norm.mul (anchoredGram_sqrt_continuous (d := d) (ℓ := ℓ)).norm)
  exact ⟨χ, hχ, fun u hu => by
    simpa only [anchoredSimilarityUnit_val, anchoredSimilarityUnit_inv_val, Pi.mul_apply] using hb u hu⟩

def anchoredVectorMoment {d ℓ : ℕ} (u : Covariate d) (p g : Covariate d → ℝ) : AnchoredIndex d ℓ → ℝ :=
  fun γ => ∫ w, p w * anchoredFeature u w γ * g w ∂cubeVolume d

def anchoredPreconditionedMoment {d ℓ : ℕ} (u : Covariate d) (p g : Covariate d → ℝ) : AnchoredIndex d ℓ → ℝ :=
  (anchoredGram u)⁻¹ *ᵥ anchoredVectorMoment u p g

theorem anchoredVectorMoment_norm_bound {d ℓ : ℕ} (u : Covariate d)
    (hu : u ∈ unitCube d) (p g : Covariate d → ℝ) (b F : ℝ) (hb : 0 ≤ b) (hF : 0 ≤ F)
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) (hg : ∀ w ∈ unitCube d, |g w| ≤ F) :
    ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredVectorMoment u p g)‖ ≤
      Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (b * F) := by
  let := cubeVolume_isProbability d
  have hcoord (γ : AnchoredIndex d ℓ) : |anchoredVectorMoment u p g γ| ≤ b * F := by
    have hbound : ∀ᵐ w ∂cubeVolume d, ‖p w * anchoredFeature u w γ * g w‖ ≤ b * F := by
      filter_upwards [hp, ae_restrict_mem (unitCube_isCompact d).isClosed.measurableSet] with w hw hcube
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw.1]
      exact (mul_le_mul (mul_le_mul hw.2 (anchoredFeature_abs_le_one u w hu hcube γ) (abs_nonneg _) hb)
        (hg w hcube) (abs_nonneg _) (mul_nonneg hb (by norm_num))).trans_eq (by ring)
    simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, anchoredVectorMoment]
      using norm_integral_le_of_norm_le_const hbound
  let v := (EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredVectorMoment u p g)
  change ‖v‖ ≤ _
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hb hF), ?_⟩
  refine (Finset.sum_le_sum fun γ _ => pow_le_pow_left₀ (norm_nonneg _) (hcoord γ) 2).trans_eq ?_
  simp [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem anchoredGram_inverse_uniform_bound {d ℓ : ℕ} :
    ∃ N : ℝ, 0 < N ∧ ∀ u ∈ unitCube d, ‖(anchoredGram (ℓ := ℓ) u)⁻¹‖ ≤ N := by
  have hc : Continuous fun u : Covariate d => (anchoredGram (ℓ := ℓ) u)⁻¹ := by
    rw [show (fun u : Covariate d => (anchoredGram (ℓ := ℓ) u)⁻¹) = fun u => anchoredWhitening u * anchoredWhitening u
      from funext anchoredWhitening_square]
    exact (anchoredWhitening_continuous (d := d) (ℓ := ℓ)).mul anchoredWhitening_continuous
  exact cube_continuous_bound hc.norm

theorem anchoredPreconditionedMoment_uniform_bound {d ℓ : ℕ}
    (b F : ℝ) (hb : 0 ≤ b) (hF : 0 ≤ F) :
    ∃ W : ℝ, 0 < W ∧ ∀ u ∈ unitCube d, ∀ p g : Covariate d → ℝ,
      (∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) → (∀ w ∈ unitCube d, |g w| ≤ F) →
      ‖anchoredPreconditionedMoment (ℓ := ℓ) u p g‖ ≤ W := by
  obtain ⟨N, hN, hNu⟩ := anchoredGram_inverse_uniform_bound (d := d) (ℓ := ℓ)
  let W := max 1 (N * (Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (b * F)))
  refine ⟨W, zero_lt_one.trans_le (le_max_left _ _), fun u hu p g hp hg => ?_⟩
  have hM := anchoredVectorMoment_norm_bound (ℓ := ℓ) u hu p g b F hb hF hp hg
  have hA := Matrix.l2_opNorm_mulVec ((anchoredGram (ℓ := ℓ) u)⁻¹)
    ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredVectorMoment u p g))
  have hpre : ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredPreconditionedMoment u p g)‖ ≤ W :=
    (hA.trans (mul_le_mul (hNu u hu) hM (norm_nonneg _) hN.le)).trans (le_max_right _ _)
  exact (pi_norm_le_iff_of_nonneg (by dsimp [W]; positivity)).mpr fun γ => (PiLp.norm_apply_le _ γ).trans hpre

-- 3. Population matrix inverse derivative bounds (`PopulationInverseDerivatives`)

private theorem reindex_matrix_norm {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    [Nonempty n] [Nonempty m] (e : n ≃ m) (A : Matrix n n ℝ) : ‖A.reindex e e‖ = ‖A‖ := by
  let φ := Matrix.reindexAlgEquiv ℝ ℝ e
  change ‖φ A‖ = ‖A‖
  have hs : IsSelfAdjoint (star A * A) := .star_mul_self A
  have hs' : IsSelfAdjoint (φ (star A * A)) := Matrix.isHermitian_iff_isSelfAdjoint.mp
    ((Matrix.isHermitian_iff_isSelfAdjoint.mpr hs).reindex e)
  have hgR := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (star A * A) hs
  have hgS := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (φ (star A * A)) hs'
  rw [AlgEquiv.spectrum_eq φ] at hgS
  have he : ‖φ (star A * A)‖ = ‖star A * A‖ := hgS.unique hgR
  rw [show φ (star A * A) = star (φ A) * φ A by rw [map_mul]; rfl,
    CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at he
  exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp he

abbrev anchoredDimension (d ℓ : ℕ) := Fintype.card (AnchoredIndex d ℓ)

instance anchoredDimension_neZero {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)] :
    NeZero (anchoredDimension d ℓ) := ⟨Fintype.card_ne_zero⟩

def anchoredFinReindex (d ℓ : ℕ) : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ ≃ₐ[ℝ]
    Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ (Fintype.equivFin (AnchoredIndex d ℓ))

def anchoredFinNormalizedGram {d ℓ : ℕ} (u : Covariate d) (p : Covariate d → ℝ) :
    Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ :=
  anchoredFinReindex d ℓ ((anchoredGram u)⁻¹ * anchoredDensityGram u p)

def anchoredFinSimilarityUnit {d ℓ : ℕ} (u : Covariate d) :
    (Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ)ˣ :=
  Units.map (anchoredFinReindex d ℓ).toMonoidHom (anchoredSimilarityUnit u)

@[simp] theorem anchoredFinSimilarityUnit_val {d ℓ : ℕ} (u : Covariate d) :
    (anchoredFinSimilarityUnit (ℓ := ℓ) u).val = anchoredFinReindex d ℓ (anchoredSimilarityUnit u).val := rfl

@[simp] theorem anchoredFinSimilarityUnit_inv_val {d ℓ : ℕ} (u : Covariate d) :
    ((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val = anchoredFinReindex d ℓ ((anchoredSimilarityUnit u)⁻¹).val := rfl

private theorem anchoredFin_similarity {d ℓ : ℕ} (u : Covariate d) (p : Covariate d → ℝ) :
    matrixSimilarity (anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹ (anchoredFinNormalizedGram u p) =
      anchoredFinReindex d ℓ (anchoredWhitenedGram u p) := by
  change anchoredFinReindex d ℓ _ * anchoredFinReindex d ℓ _ * anchoredFinReindex d ℓ _ = _
  rw [← map_mul, ← map_mul]; exact congrArg (anchoredFinReindex d ℓ) (anchored_preconditioned_similarity u p)

theorem anchoredFin_similarity_isHermitian {d ℓ : ℕ} (u : Covariate d) (p : Covariate d → ℝ) :
    (matrixSimilarity (anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹ (anchoredFinNormalizedGram u p)).IsHermitian := by
  rw [anchoredFin_similarity]
  exact (anchoredWhitenedGram_isHermitian u p).reindex (Fintype.equivFin (AnchoredIndex d ℓ))

theorem anchoredFin_similarity_spectrum {d ℓ : ℕ} (u : Covariate d)
    (p : Covariate d → ℝ) (hpmeas : Measurable p) (a b : ℝ) (ha : 0 ≤ a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) :
    spectrum ℝ (matrixSimilarity (anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹ (anchoredFinNormalizedGram u p)) ⊆ Set.Icc a b := by
  rw [anchoredFin_similarity, AlgEquiv.spectrum_eq]
  exact anchoredWhitenedGram_spectrum u p hpmeas a b ha hp

theorem anchoredFinSimilarityUnit_uniform_condition {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)] :
    ∃ χ : ℝ, 0 < χ ∧ ∀ u ∈ unitCube d,
      ‖(anchoredFinSimilarityUnit (ℓ := ℓ) u).val‖ * ‖((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ := by
  obtain ⟨χ, hχ, hQ⟩ := anchoredSimilarityUnit_uniform_condition (d := d) (ℓ := ℓ)
  refine ⟨χ, hχ, fun u hu => ?_⟩
  rw [anchoredFinSimilarityUnit_val, anchoredFinSimilarityUnit_inv_val]
  change ‖((anchoredSimilarityUnit u).val).reindex _ _‖ * ‖(((anchoredSimilarityUnit u)⁻¹).val).reindex _ _‖ ≤ χ
  rw [reindex_matrix_norm, reindex_matrix_norm]; exact hQ u hu

theorem matrix_real_entry_norm_le {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  rw [← complexify_matrix_norm A, ← Complex.norm_real (A i j)]
  exact matrix_entry_norm_le_l2 (A.map Complex.ofReal) i j

private theorem anchoredFinNormalizedGram_norm_le {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)]
    (u : Covariate d) (p : Covariate d → ℝ) (hpmeas : Measurable p)
    (a b χ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hχ : 0 ≤ χ)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)
    (hQ : ‖(anchoredFinSimilarityUnit (ℓ := ℓ) u).val‖ * ‖((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ) :
    ‖anchoredFinNormalizedGram (ℓ := ℓ) u p‖ ≤ χ * b := by
  let Q := anchoredFinSimilarityUnit (ℓ := ℓ) u
  let A := anchoredFinNormalizedGram (ℓ := ℓ) u p
  have he : matrixSimilarity Q (matrixSimilarity Q⁻¹ A) = A := by simp [matrixSimilarity, Matrix.mul_assoc]
  have hspec_norm : ‖matrixSimilarity Q⁻¹ A‖ ≤ b := by
    have hs : IsSelfAdjoint (matrixSimilarity Q⁻¹ A) :=
      Matrix.isHermitian_iff_isSelfAdjoint.mp (anchoredFin_similarity_isHermitian u p)
    rw [← cfc_id ℝ _ hs]
    refine norm_cfc_le hb fun t ht => ?_
    have hsp := anchoredFin_similarity_spectrum u p hpmeas a b ha hp ht
    rw [id_eq, Real.norm_eq_abs, abs_of_nonneg (ha.trans hsp.1)]; exact hsp.2
  change ‖A‖ ≤ χ * b; rw [← he]
  exact (matrixSimilarity_norm_le Q _).trans (mul_le_mul hQ hspec_norm (norm_nonneg _) hχ)

def anchoredFinTransport (d ℓ : ℕ) :
    Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ :=
  anchoredFinReindex d ℓ (anchoredTransport d ℓ)

theorem anchored_population_inverse_derivatives {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)]
    (a b W Y : ℝ) (ha : 0 < a) (hab : a < b) (hW : 0 ≤ W) (hY : 0 ≤ Y) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (u v : Covariate d), u ∈ unitCube d → v ∈ unitCube d →
      ∀ (p q : Covariate d → ℝ), Measurable p → Measurable q →
      (∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) →
      (∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b) →
      ∀ (U V : Bool → Fin (anchoredDimension d ℓ) → ℝ),
      (∀ t, ‖U t‖ ≤ W) → (∀ t, ‖V t‖ ≤ W) →
      ∀ y : ℝ, |y| ≤ Y → ∀ m k : ℕ,
      ∀ directions : Fin k → Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ,
        ‖iteratedFDeriv ℝ k (incrementFinVector (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) y m)
          (fun j => incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q) U V
            ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm j)) directions‖ ≤
            C * (k.factorial : ℝ) * A ^ k * ∏ j, ‖directions j‖ := by
  obtain ⟨χ, hχ, hQ⟩ := anchoredFinSimilarityUnit_uniform_condition (d := d) (ℓ := ℓ)
  let η := (1 + RoughRegime.Upper.intervalRho a b) / 2
  have hρ := RoughRegime.Upper.intervalRho_pos a b ha hab
  have hρ1 := RoughRegime.Upper.intervalRho_lt_one a b ha hab
  have hρη : RoughRegime.Upper.intervalRho a b < η := by dsimp [η]; linarith
  have hη1 : η < 1 := by dsimp [η]; linarith
  have hη : 0 < η := hρ.trans hρη
  let L := max (χ * b) W
  have hb : 0 < b := ha.trans hab
  have hL : 0 ≤ L := (mul_nonneg hχ.le hb.le).trans (le_max_left _ _)
  let M := similarIncrementEnvelope (anchoredDimension d ℓ) a b
    (RoughRegime.Upper.intervalRho a b / η) χ L Y (anchoredFinTransport d ℓ)
  have hRate := inverseDerivativeRate_pos (anchoredDimension d ℓ) a b η χ hη hη1 hχ
  refine ⟨max 1 M, inverseDerivativeRate (anchoredDimension d ℓ) a b η χ,
    zero_lt_one.trans_le (le_max_left _ _), hRate, ?_⟩
  intro u v hu hv p q hpmeas hqmeas hp hq U V hU hV y hy m k directions
  have hAu := anchoredFinNormalizedGram_norm_le u p hpmeas a b χ ha.le hb.le hχ.le hp (hQ u hu)
  have hAv := anchoredFinNormalizedGram_norm_le v q hqmeas a b χ ha.le hb.le hχ.le hq (hQ v hv)
  let c : InverseDerivativeCenter (anchoredDimension d ℓ) a b χ L :=
    { moments := incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q) U V
      normBound := (pi_norm_le_iff_of_nonneg hL).mpr fun z => by
        cases z with
        | inl z => cases z with
          | inl ij => exact ((matrix_real_entry_norm_le _ ij.1 ij.2).trans hAu).trans (le_max_left _ _)
          | inr z => exact ((matrix_real_entry_norm_le _ z.2.1 z.2.2).trans hAv).trans (le_max_left _ _)
        | inr z =>
          rcases z with ⟨parent, response, i⟩
          cases parent with
          | false => exact ((norm_le_pi_norm (U response) i).trans (hU response)).trans (le_max_right _ _)
          | true => exact ((norm_le_pi_norm (V response) i).trans (hV response)).trans (le_max_right _ _)
      currentChart := anchoredFinSimilarityUnit u
      parentChart := anchoredFinSimilarityUnit v
      currentCondition := hQ u hu
      parentCondition := hQ v hv
      currentHermitian := anchoredFin_similarity_isHermitian u p
      parentHermitian := anchoredFin_similarity_isHermitian v q
      currentSpectrum := anchoredFin_similarity_spectrum u p hpmeas a b ha.le hp
      parentSpectrum := anchoredFin_similarity_spectrum v q hqmeas a b ha.le hq }
  refine (paper_inverse_vector_derivative_bound (anchoredDimension d ℓ) a b ha hab η hρη hη1 χ hχ
    L Y hL hY (anchoredFinTransport d ℓ) y hy c m k directions).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun j _ => norm_nonneg (directions j))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 M) (Nat.cast_nonneg _))
    (pow_nonneg hRate.le k)

-- 4. Pilot basis, dyadic raw features, coordinate expansion & nesting
--    (`PilotFeatures`, `DyadicPilotFeatures`, `PilotCoordinateExpansion`, `AnchoredCoefficientBounds`, `DyadicNesting`)

abbrev PilotBasisIndex (q d ℓ : ℕ) := (Fin q × PolynomialBox d ℓ) × Bool

def pilotGlobalMonomial {d ℓ : ℕ} (γ : PolynomialBox d ℓ) (x : Covariate d) : ℝ :=
  ∏ i, (x i) ^ (γ i).val

def pilotBasisFeature {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (a : PilotBasisIndex q d ℓ) (z : Observation d) : ℝ :=
  if cell z.1 = a.1.1 then pilotGlobalMonomial a.1.2 z.1 * (if a.2 then z.2 else 1) else 0

theorem pilotBasisFeature_measurable {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (hc : Measurable cell) (a : PilotBasisIndex q d ℓ) : Measurable (pilotBasisFeature cell a) := by
  refine Measurable.ite (measurableSet_eq_fun (hc.comp measurable_fst) measurable_const) ?_ measurable_const
  exact ((continuous_finset_prod Finset.univ fun i _ => (continuous_apply i).pow _).measurable.comp measurable_fst).mul
    (by cases a.2
        · exact measurable_const
        · exact measurable_snd)

theorem observationLaw_cube_ae {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    ∀ᵐ z ∂observationLaw θ, z.1 ∈ unitCube d :=
  (observationLaw_fst_measurePreserving C θ hθ).quasiMeasurePreserving.ae (designLaw_cube_ae θ)

theorem pilotBasisFeature_memLp_two {q d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (cell : Covariate d → Fin q) (hc : Measurable cell) (a : PilotBasisIndex q d ℓ) :
    MemLp (pilotBasisFeature cell a) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  have hy : MemLp (fun z : Observation d => |z.2|) 2 (observationLaw θ) := by
    simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm
  refine ((memLp_const (1 : ℝ)).add hy).mono' (pilotBasisFeature_measurable cell hc a).aestronglyMeasurable ?_
  filter_upwards [observationLaw_cube_ae C θ hθ] with z hz
  simp only [Real.norm_eq_abs, Pi.add_apply]
  have hmono : |pilotGlobalMonomial a.1.2 z.1| ≤ 1 := by
    unfold pilotGlobalMonomial; rw [Finset.abs_prod]; simp only [abs_pow]
    exact (Finset.prod_le_prod₀ (g := fun i => (1 : ℝ) ^ (a.1.2 i).val)
      (fun _ _ => pow_nonneg (abs_nonneg _) _) fun i _ =>
        pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_of_nonneg (hz i).1]; exact (hz i).2) _).trans_eq (by simp)
  by_cases h : cell z.1 = a.1.1
  · rw [pilotBasisFeature, if_pos h, abs_mul]
    cases a.2
    · simpa using hmono.trans (le_add_of_nonneg_right (abs_nonneg z.2))
    · simp only [↓reduceIte]
      exact (mul_le_mul_of_nonneg_right hmono (abs_nonneg z.2)).trans (by linarith)
  · simp only [pilotBasisFeature, if_neg h, abs_zero]; positivity

def pilotRawVector {q d ℓ : ℕ} (cell : Covariate d → Fin q) (z : Observation d) :
    Fin (Fintype.card (PilotBasisIndex q d ℓ)) → ℝ :=
  fun a => pilotBasisFeature cell ((Fintype.equivFin (PilotBasisIndex q d ℓ)).symm a) z

abbrev LocalPilotIndex (d ℓ : ℕ) :=
  Sum (AnchoredIndex d ℓ × AnchoredIndex d ℓ) (Sum (AnchoredIndex d ℓ) (AnchoredIndex d ℓ))

def dyadicPilotScale (d j : ℕ) : ℝ := ((2 : ℝ) ^ j) ^ d

theorem dyadicPilotScale_pos (d j : ℕ) : 0 < dyadicPilotScale d j := by unfold dyadicPilotScale; positivity

def dyadicPilotCell {d : ℕ} (j : ℕ) (x : Covariate d) : Set (Covariate d) :=
  {z | regularGridCell ((2 : ℕ) ^ j) (by positivity) z = regularGridCell ((2 : ℕ) ^ j) (by positivity) x}

theorem dyadicPilotCell_measurable {d : ℕ} (j : ℕ) (x : Covariate d) :
    MeasurableSet (dyadicPilotCell j x) :=
  measurableSet_eq_fun (regular_grid_cell_measurable _ _) measurable_const

theorem dyadicAnchoredFeature_measurable {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (γ : AnchoredIndex d ℓ) : Measurable fun z => dyadicAnchoredFeature j x z γ :=
  ((anchoredMonomial_continuous γ).comp (continuous_pi fun i =>
    continuous_const.mul ((continuous_apply i).sub continuous_const))).measurable

theorem dyadicAnchoredFeature_abs_le_one {d ℓ : ℕ} (j : ℕ) (x z : Covariate d)
    (hx : x ∈ unitCube d) (hz : z ∈ unitCube d) (hc : z ∈ dyadicPilotCell j x)
    (γ : AnchoredIndex d ℓ) : |dyadicAnchoredFeature j x z γ| ≤ 1 := by
  refine anchoredMonomial_abs_le_one _ _ fun i => ?_
  have hr := regular_grid_same_cell_radius ((2 : ℕ) ^ j) (by positivity) z x hz hx hc i
  have hk : 0 < (2 : ℝ) ^ j := by positivity
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hr
  rw [abs_mul, abs_of_pos hk]
  exact (mul_le_mul_of_nonneg_left hr hk.le).trans_eq (by field_simp)

def dyadicPilotScalar {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) : ℝ :=
  match a with
  | Sum.inl (γ, δ) => dyadicAnchoredFeature j x z.1 γ * dyadicAnchoredFeature j x z.1 δ
  | Sum.inr (Sum.inl γ) => z.2 * dyadicAnchoredFeature j x z.1 γ
  | Sum.inr (Sum.inr γ) => dyadicAnchoredFeature j x z.1 γ

def dyadicPilotFeature {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) : ℝ :=
  dyadicPilotScale d j * (Prod.fst ⁻¹' dyadicPilotCell j x).indicator (dyadicPilotScalar j x a) z

theorem dyadicPilotFeature_measurable {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) : Measurable (dyadicPilotFeature j x a) := by
  have hs : Measurable (dyadicPilotScalar j x a) := by
    cases a with
    | inl a =>
      exact ((dyadicAnchoredFeature_measurable j x a.1).comp measurable_fst).mul
        ((dyadicAnchoredFeature_measurable j x a.2).comp measurable_fst)
    | inr a =>
      cases a with
      | inl γ => exact measurable_snd.mul ((dyadicAnchoredFeature_measurable j x γ).comp measurable_fst)
      | inr γ => exact (dyadicAnchoredFeature_measurable j x γ).comp measurable_fst
  exact measurable_const.mul (hs.indicator (measurable_fst (dyadicPilotCell_measurable j x)))

private theorem dyadicPilotFeature_abs_bound {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) (hx : x ∈ unitCube d) (hz : z.1 ∈ unitCube d) :
    |dyadicPilotFeature j x a z| ≤ dyadicPilotScale d j *
      (Prod.fst ⁻¹' dyadicPilotCell j x).indicator (fun z : Observation d => 1 + |z.2|) z := by
  by_cases hc : z.1 ∈ dyadicPilotCell j x
  · have hc' : z ∈ Prod.fst ⁻¹' dyadicPilotCell j x := hc
    simp only [dyadicPilotFeature, indicator_of_mem hc', abs_mul, abs_of_pos (dyadicPilotScale_pos d j)]
    refine mul_le_mul_of_nonneg_left ?_ (dyadicPilotScale_pos d j).le
    have hb := dyadicAnchoredFeature_abs_le_one (ℓ := ℓ) j x z.1 hx hz hc
    cases a with
    | inl a =>
      change |dyadicAnchoredFeature j x z.1 a.1 * dyadicAnchoredFeature j x z.1 a.2| ≤ _
      rw [abs_mul]
      exact (mul_le_mul (hb a.1) (hb a.2) (abs_nonneg _) (by norm_num)).trans (by linarith [abs_nonneg z.2])
    | inr a => cases a with
      | inl γ => change |z.2 * dyadicAnchoredFeature j x z.1 γ| ≤ _; rw [abs_mul]
                 exact (mul_le_mul_of_nonneg_left (hb γ) (abs_nonneg z.2)).trans (by linarith)
      | inr γ => exact (hb γ).trans (le_add_of_nonneg_right (abs_nonneg z.2))
  · simp [dyadicPilotFeature, hc]

theorem dyadicPilotFeature_memLp_two {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ) :
    MemLp (dyadicPilotFeature j x a) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  have hy : MemLp (fun z : Observation d => |z.2|) 2 (observationLaw θ) := by
    simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm
  refine (((memLp_const (1 : ℝ)).add hy).const_mul (dyadicPilotScale d j)).mono'
    (dyadicPilotFeature_measurable j x a).aestronglyMeasurable ?_
  filter_upwards [observationLaw_cube_ae C θ hθ] with z hz
  rw [Real.norm_eq_abs]
  refine (dyadicPilotFeature_abs_bound j x a z hx hz).trans ?_
  by_cases hc : z.1 ∈ dyadicPilotCell j x <;> simp [hc]
  exact mul_nonneg (dyadicPilotScale_pos d j).le (by positivity)

def dyadicPilotMomentConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  (2 * (1 + responseSecondBound C)) * C.densityUpper

theorem dyadicPilotMomentConstant_pos {d : ℕ} (C : ModelConstants d) :
    0 < dyadicPilotMomentConstant C := by
  have := C.one_lt_densityUpper; have := responseSecondBound_pos C
  unfold dyadicPilotMomentConstant; positivity

theorem dyadicPilotFeature_second_le {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ) :
    (∫ z, dyadicPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      dyadicPilotMomentConstant C * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  have hy : MemLp (fun z : Observation d => |z.2|) 2 (observationLaw θ) := by
    simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm
  have hd : Integrable (fun z : Observation d => dyadicPilotScale d j ^ 2 *
      (Prod.fst ⁻¹' dyadicPilotCell j x).indicator (fun z : Observation d => (1 + |z.2|) ^ 2) z)
      (observationLaw θ) :=
    (((memLp_const (1 : ℝ)).add hy).integrable_sq.indicator (measurable_fst (dyadicPilotCell_measurable j x))).const_mul _
  have hfirst : (∫ z, dyadicPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      dyadicPilotScale d j ^ 2 * ((2 * (1 + responseSecondBound C)) * (designLaw θ).real (dyadicPilotCell j x)) := by
    refine (integral_mono_ae (dyadicPilotFeature_memLp_two C θ hθ j x hx a).integrable_sq hd ?_).trans ?_
    · filter_upwards [observationLaw_cube_ae C θ hθ] with z hz
      have hb := dyadicPilotFeature_abs_bound j x a z hx hz
      by_cases hc : z.1 ∈ dyadicPilotCell j x
      · have hc' : z ∈ Prod.fst ⁻¹' dyadicPilotCell j x := hc
        simp only [indicator_of_mem hc'] at hb ⊢
        change dyadicPilotFeature j x a z ^ 2 ≤ dyadicPilotScale d j ^ 2 * (1 + |z.2|) ^ 2
        simpa only [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hb 2
      · simp [dyadicPilotFeature, hc]
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        (observationLaw_localized_response_energy_le C θ hθ _ (dyadicPilotCell_measurable j x)) (sq_nonneg _)
  have hmass : (designLaw θ).real (dyadicPilotCell j x) ≤ C.densityUpper / dyadicPilotScale d j := by
    convert regularGridProbability_cap C θ hθ ((2 : ℕ) ^ j) (by positivity)
      (regularGridCell ((2 : ℕ) ^ j) (by positivity) x) using 1 <;>
      simp only [dyadicPilotCell, regularGridProbability, preimage, mem_singleton_iff,
        dyadicPilotScale, Nat.cast_pow, Nat.cast_ofNat]
  have hfactor : 0 ≤ dyadicPilotScale d j ^ 2 * (2 * (1 + responseSecondBound C)) := by
    have := responseSecondBound_pos C; positivity
  have hm := mul_le_mul_of_nonneg_left hmass hfactor
  have heq : dyadicPilotScale d j ^ 2 * (2 * (1 + responseSecondBound C)) * (C.densityUpper / dyadicPilotScale d j) =
      dyadicPilotMomentConstant C * dyadicPilotScale d j := by
    unfold dyadicPilotMomentConstant; field_simp [(dyadicPilotScale_pos d j).ne']
  rw [heq] at hm
  exact hfirst.trans (by simpa only [mul_assoc] using hm)

def dyadicPilotPopulation {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    LocalPilotIndex d ℓ → ℝ := fun a => ∫ z, dyadicPilotFeature j x a z ∂observationLaw θ

def pilotPolynomialLinear {q d ℓ : ℕ} (c : Fin q) (P : MvPolynomial (Fin d) ℝ)
    (response : Bool) : (Fin (Fintype.card (PilotBasisIndex q d ℓ)) → ℝ) →L[ℝ] ℝ :=
  ∑ β : PolynomialBox d ℓ, P.coeff (polynomialBoxExponent β) •
    ContinuousLinearMap.proj ((Fintype.equivFin (PilotBasisIndex q d ℓ)) ((c, β), response))

theorem pilotPolynomialLinear_raw_apply {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (c : Fin q) (P : MvPolynomial (Fin d) ℝ) (hP : P.totalDegree ≤ ℓ)
    (response : Bool) (z : Observation d) :
    pilotPolynomialLinear (ℓ := ℓ) c P response (pilotRawVector cell z) =
      if cell z.1 = c then MvPolynomial.eval z.1 P * (if response then z.2 else 1) else 0 := by
  simp only [pilotPolynomialLinear, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, pilotRawVector, Equiv.symm_apply_apply, smul_eq_mul, pilotBasisFeature]
  by_cases h : cell z.1 = c
  · simp only [h, ite_true, ← mul_assoc, ← Finset.sum_mul]
    rw [polynomial_box_evaluation P hP]; rfl
  · simp [h]

abbrev DyadicPilotLabelIndex (d j : ℕ) := Fin d → Fin ((2 : ℕ) ^ j)

def dyadicPilotLabel {d : ℕ} (j : ℕ) (x : Covariate d) :
    Fin (Fintype.card (DyadicPilotLabelIndex d j)) :=
  Fintype.equivFin (DyadicPilotLabelIndex d j) (regularGridCell ((2 : ℕ) ^ j) (by positivity) x)

theorem dyadicPilotLabel_measurable {d : ℕ} (j : ℕ) : Measurable (dyadicPilotLabel (d := d) j) :=
  (measurable_of_countable _).comp (regular_grid_cell_measurable _ _)

theorem dyadicPilotLabel_eq_iff {d : ℕ} (j : ℕ) (x z : Covariate d) :
    dyadicPilotLabel j z = dyadicPilotLabel j x ↔ z ∈ dyadicPilotCell j x :=
  (Fintype.equivFin (DyadicPilotLabelIndex d j)).injective.eq_iff

def dyadicPilotPolynomial {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) : MvPolynomial (Fin d) ℝ :=
  match a with
  | Sum.inl (γ, δ) => dyadicFeaturePolynomial j x γ * dyadicFeaturePolynomial j x δ
  | Sum.inr (Sum.inl γ) => dyadicFeaturePolynomial j x γ
  | Sum.inr (Sum.inr γ) => dyadicFeaturePolynomial j x γ

def dyadicPilotResponse {d ℓ : ℕ} (a : LocalPilotIndex d ℓ) : Bool :=
  match a with
  | Sum.inl _ => false
  | Sum.inr (Sum.inl _) => true
  | Sum.inr (Sum.inr _) => false

private theorem dyadicPilotPolynomial_degree {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) : (dyadicPilotPolynomial j x a).totalDegree ≤ 2 * ℓ := by
  cases a with
  | inl a =>
    exact (MvPolynomial.totalDegree_mul _ _).trans
      ((Nat.add_le_add (dyadicFeaturePolynomial_degree j x a.1) (dyadicFeaturePolynomial_degree j x a.2)).trans_eq (by omega))
  | inr a => cases a <;> exact (dyadicFeaturePolynomial_degree j x _).trans (by omega)

def dyadicPilotCoordinate {d ℓ : ℕ} (j : ℕ) (x : Covariate d) (a : LocalPilotIndex d ℓ) :
    (Fin (Fintype.card (PilotBasisIndex (Fintype.card (DyadicPilotLabelIndex d j)) d (2 * ℓ))) → ℝ) →L[ℝ] ℝ :=
  dyadicPilotScale d j • pilotPolynomialLinear (dyadicPilotLabel j x)
    (dyadicPilotPolynomial j x a) (dyadicPilotResponse a)

theorem dyadicPilotCoordinate_raw_apply {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) :
    dyadicPilotCoordinate j x a (pilotRawVector (dyadicPilotLabel j) z) = dyadicPilotFeature j x a z := by
  have hscalar : MvPolynomial.eval z.1 (dyadicPilotPolynomial j x a) * (if dyadicPilotResponse a then z.2 else 1) =
      dyadicPilotScalar j x a z := by
    cases a with
    | inl a => simp [dyadicPilotPolynomial, dyadicPilotResponse, dyadicPilotScalar, dyadicFeaturePolynomial_eval]
    | inr a => cases a <;> simp [dyadicPilotPolynomial, dyadicPilotResponse, dyadicPilotScalar,
        dyadicFeaturePolynomial_eval, mul_comm]
  rw [dyadicPilotCoordinate, ContinuousLinearMap.smul_apply,
    pilotPolynomialLinear_raw_apply _ _ _ (dyadicPilotPolynomial_degree j x a)]
  simp only [smul_eq_mul, dyadicPilotLabel_eq_iff, hscalar, dyadicPilotFeature]
  by_cases h : z.1 ∈ dyadicPilotCell j x
  · have he := (dyadicPilotLabel_eq_iff j x z.1).mpr h
    simp [h, he]
  · have he : dyadicPilotLabel j z.1 ≠ dyadicPilotLabel j x := fun he => h ((dyadicPilotLabel_eq_iff j x z.1).mp he)
    simp [h, he]

theorem dyadicPilotPolynomial_coeff_continuous {d ℓ : ℕ} (j : ℕ)
    (a : LocalPilotIndex d ℓ) (e : Fin d →₀ ℕ) :
    Continuous fun x : Covariate d => (dyadicPilotPolynomial j x a).coeff e := by
  cases a with
  | inl a =>
    exact poly_coeff_mul_continuous (dyadicFeaturePolynomial_coeff_continuous j a.1)
      (dyadicFeaturePolynomial_coeff_continuous j a.2) e
  | inr a => cases a <;> exact dyadicFeaturePolynomial_coeff_continuous j _ e

theorem dyadicPilotPolynomial_coeff_uniform_bound {d ℓ : ℕ} (j : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ a : LocalPilotIndex d ℓ,
      ∀ β : PolynomialBox d (2 * ℓ),
        |(dyadicPilotPolynomial j x a).coeff (polynomialBoxExponent β)| ≤ M := by
  let f (x : Covariate d) (i : LocalPilotIndex d ℓ × PolynomialBox d (2 * ℓ)) :=
    (dyadicPilotPolynomial j x i.1).coeff (polynomialBoxExponent i.2)
  have hf : Continuous f := continuous_pi fun i => dyadicPilotPolynomial_coeff_continuous j i.1 _
  obtain ⟨M, hM, hb⟩ := cube_continuous_bound hf.norm
  refine ⟨M, hM, fun x hx a β => ?_⟩
  have hi : |f x (a, β)| ≤ ‖f x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (f x) (a, β)
  exact hi.trans (hb x hx)

private lemma regular_grid_same_cell_congr {d k l : ℕ} (h : k = l) (hk : 0 < k) (hl : 0 < l)
    (x z : Covariate d) : (regularGridCell k hk z = regularGridCell k hk x) ↔
      (regularGridCell l hl z = regularGridCell l hl x) := by subst l; rfl

theorem dyadicPilotCell_subset_parent {d : ℕ} (j : ℕ) (x : Covariate d) :
    dyadicPilotCell j x ⊆ dyadicPilotCell (j - 1) x := by
  cases j with
  | zero => simp
  | succ j =>
    intro z hz
    have hparent (k : ℕ) (hk : 0 < k) (u : ℝ) :
        (regularGridIndex (2 * k) (by omega) u).val / 2 = (regularGridIndex k hk u).val := by
      have hf : ⌊((2 * k : ℕ) : ℝ) * u⌋₊ / 2 = ⌊(k : ℝ) * u⌋₊ := by
        rw [show ((2 * k : ℕ) : ℝ) * u = ((k : ℝ) * u) * (2 : ℕ) by push_cast; ring,
          Nat.mul_cast_floor_div_cancel (by decide : (2 : ℕ) ≠ 0)]
      simp only [regularGridIndex, Fin.val_mk]; omega
    have hsize : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; omega
    have hz' := (regular_grid_same_cell_congr hsize (by positivity) (by positivity) x z).mp hz
    funext i; apply Fin.ext
    have hi := congrArg (fun c => (c i).val / 2) hz'
    change (regularGridIndex (2 * 2 ^ j) (by positivity) (z i)).val / 2 =
      (regularGridIndex (2 * 2 ^ j) (by positivity) (x i)).val / 2 at hi
    rwa [hparent ((2 : ℕ) ^ j) (by positivity), hparent ((2 : ℕ) ^ j) (by positivity)] at hi

-- 5. Affine cells, dyadic Grams & population moments (`AffineCells`, `DyadicGram`, `DyadicPilotPopulation`)

def gridAffine {d : ℕ} (k : ℕ) (c : Fin d → Fin k) (w : Covariate d) : Covariate d :=
  regularGridCorner k c + (k : ℝ)⁻¹ • w

def gridClosedBox {d : ℕ} (k : ℕ) (c : Fin d → Fin k) : Set (Covariate d) :=
  Icc (regularGridCorner k c) (regularGridCorner k c + fun _ => (k : ℝ)⁻¹)

def gridAffineEquiv {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    Covariate d ≃ᵐ Covariate d :=
  ((Homeomorph.smul (Units.mk0 ((k : ℝ)⁻¹) (by positivity))).trans
    (Homeomorph.addLeft (regularGridCorner k c))).toMeasurableEquiv

@[simp] theorem gridAffineEquiv_apply {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) (w : Covariate d) : gridAffineEquiv k hk c w = gridAffine k c w := rfl

theorem gridAffine_preimage_box {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    gridAffine k c ⁻¹' gridClosedBox k c = unitCube d := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  ext w
  change ((∀ i, regularGridCorner k c i ≤ regularGridCorner k c i + (k : ℝ)⁻¹ * w i) ∧
    (∀ i, regularGridCorner k c i + (k : ℝ)⁻¹ * w i ≤ regularGridCorner k c i + (k : ℝ)⁻¹)) ↔
    ∀ i, 0 ≤ w i ∧ w i ≤ 1
  refine ⟨fun hw i => ⟨(mul_nonneg_iff_of_pos_left (inv_pos.mpr hkr)).mp (by linarith [hw.1 i]),
    (mul_le_mul_iff_of_pos_left (inv_pos.mpr hkr)).mp (by simpa using show (k : ℝ)⁻¹ * w i ≤ (k : ℝ)⁻¹ by linarith [hw.2 i])⟩,
    fun hw => ⟨fun i => by linarith [mul_nonneg (inv_nonneg.mpr hkr.le) (hw i).1],
      fun i => by linarith [mul_le_mul_of_nonneg_left (hw i).2 (inv_nonneg.mpr hkr.le)]⟩⟩

theorem gridClosedBox_subset_cube {d : ℕ} (k : ℕ) (hk : 0 < k)
    (c : Fin d → Fin k) : gridClosedBox k c ⊆ unitCube d := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  intro z hz i
  refine ⟨(regular_grid_corner_mem_cube k hk c i).1.trans (hz.1 i), (hz.2 i).trans ?_⟩
  change (c i : ℝ) / k + (k : ℝ)⁻¹ ≤ 1
  rw [show (c i : ℝ) / k + (k : ℝ)⁻¹ = ((c i : ℝ) + 1) / k by ring]
  exact (div_le_one hkr).2 (by exact_mod_cast (c i).isLt)

private theorem gridAffine_map_cubeVolume {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k) :
    (cubeVolume d).map (gridAffine k c) =
      ENNReal.ofReal ((k : ℝ) ^ d) • volume.restrict (gridClosedBox k c) := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hvol : (volume : Measure (Covariate d)).map (gridAffine k c) = ENNReal.ofReal ((k : ℝ) ^ d) • volume := by
    rw [show gridAffine k c = (fun z => regularGridCorner k c + z) ∘ (fun w => (k : ℝ)⁻¹ • w) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), Measure.map_addHaar_smul volume (inv_ne_zero hkr.ne'),
      Measure.map_smul _ (by fun_prop), map_add_left_eq_self]
    simp [Module.finrank_pi, abs_of_nonneg (pow_nonneg hkr.le d)]
  let e := gridAffineEquiv k hk c
  have h := e.restrict_map (volume : Measure (Covariate d)) (gridClosedBox k c)
  rw [show e ⁻¹' gridClosedBox k c = unitCube d from gridAffine_preimage_box k hk c] at h
  change ((volume.restrict (unitCube d)).map e) = _; rw [← h]
  change ((volume : Measure (Covariate d)).map (gridAffine k c)).restrict _ = _
  rw [hvol, Measure.restrict_smul]

private theorem gridAffine_ae_pullback {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k)
    {P : Covariate d → Prop} (hP : ∀ᵐ z ∂cubeVolume d, P z) :
    ∀ᵐ w ∂cubeVolume d, P (gridAffine k c w) := by
  refine ae_of_ae_map (gridAffineEquiv k hk c).measurable.aemeasurable ?_
  change ∀ᵐ z ∂(cubeVolume d).map (gridAffine k c), P z
  rw [gridAffine_map_cubeVolume k hk c]
  exact Measure.ae_smul_measure (ae_restrict_of_ae_restrict_of_subset (gridClosedBox_subset_cube k hk c) hP) _

def gridNormalizedAnchor {d : ℕ} (k : ℕ) (hk : 0 < k) (x : Covariate d) : Covariate d :=
  fun i => (k : ℝ) * (x i - regularGridCorner k (regularGridCell k hk x) i)

theorem gridNormalizedAnchor_mem_cube {d : ℕ} (k : ℕ) (hk : 0 < k)
    (x : Covariate d) (hx : x ∈ unitCube d) : gridNormalizedAnchor k hk x ∈ unitCube d := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  intro i
  exact ⟨mul_nonneg hkr.le (sub_nonneg.mpr (regular_grid_cell_corner_le k hk x hx i)),
    (mul_le_mul_of_nonneg_left (abs_le.mp (regular_grid_cell_radius k hk x hx i)).2 hkr.le).trans_eq (by field_simp)⟩

theorem dyadicAnchoredFeature_affine {d ℓ : ℕ} (j : ℕ) (x w : Covariate d)
    (γ : AnchoredIndex d ℓ) :
    dyadicAnchoredFeature j x (gridAffine ((2 : ℕ) ^ j) (regularGridCell _ (by positivity) x) w) γ =
      anchoredFeature (gridNormalizedAnchor ((2 : ℕ) ^ j) (by positivity) x) w γ := by
  unfold dyadicAnchoredFeature anchoredFeature; congr 1; funext i
  simp only [gridAffine, gridNormalizedAnchor, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, Nat.cast_pow, Nat.cast_ofNat]
  have hn : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp; ring

private theorem regular_grid_cell_integral {d : ℕ} (k : ℕ) (hk : 0 < k) (c : Fin d → Fin k)
    (f : Covariate d → ℝ) :
    (k : ℝ) ^ d * (∫ z in (regularGridCell k hk) ⁻¹' {c}, f z ∂cubeVolume d) =
      ∫ w, f (gridAffine k c w) ∂cubeVolume d := by
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have hae : ((regularGridCell k hk) ⁻¹' {c} ∩ unitCube d) =ᵐ[volume] gridClosedBox k c := by
    have hfaces : ∀ᵐ z : Covariate d ∂volume, ∀ i, z i ≠ regularGridCorner k c i + (k : ℝ)⁻¹ := by
      rw [ae_all_iff]; intro i; apply ae_iff.mpr; simp only [not_not]
      change (volume : Measure (Covariate d)) ((fun z : Covariate d => z i) ⁻¹' {regularGridCorner k c i + (k : ℝ)⁻¹}) = 0
      rw [volume_pi]; exact Measure.pi_eval_preimage_null (fun _ : Fin d => (volume : Measure ℝ)) (measure_singleton _)
    filter_upwards [hfaces] with z hz
    refine propext ⟨fun hzcell => ?_, fun hzbox => ⟨funext fun i => ?_, gridClosedBox_subset_cube k hk c hzbox⟩⟩
    · have hc : regularGridCell k hk z = c := hzcell.1
      refine ⟨fun i => by simpa only [hc] using regular_grid_cell_corner_le k hk z hzcell.2 i, fun i => ?_⟩
      have h := (abs_le.mp (regular_grid_cell_radius k hk z hzcell.2 i)).2
      simp only [hc, one_div] at h
      change z i ≤ regularGridCorner k c i + (k : ℝ)⁻¹; linarith
    · have hhi : z i < (c i : ℝ) / k + (k : ℝ)⁻¹ := lt_of_le_of_ne (hzbox.2 i) (hz i)
      have hz0 : 0 ≤ z i := (div_nonneg (Nat.cast_nonneg _) hkr.le).trans (hzbox.1 i)
      have hf : ⌊(k : ℝ) * z i⌋₊ = (c i).val := (Nat.floor_eq_iff (mul_nonneg hkr.le hz0)).2
        ⟨by nlinarith [(div_le_iff₀ hkr).mp (hzbox.1 i)],
         by have h := mul_lt_mul_of_pos_left hhi hkr
            rwa [show (k : ℝ) * ((c i : ℝ) / k + (k : ℝ)⁻¹) = (c i : ℝ) + 1 by field_simp] at h⟩
      apply Fin.ext; change min ⌊(k : ℝ) * z i⌋₊ (k - 1) = (c i).val
      rw [hf, min_eq_left (by have := (c i).isLt; omega)]
  have hrest : (cubeVolume d).restrict ((regularGridCell k hk) ⁻¹' {c}) = volume.restrict (gridClosedBox k c) := by
    rw [cubeVolume, Measure.restrict_restrict ((measurableSet_singleton c).preimage (regular_grid_cell_measurable k hk))]
    exact Measure.restrict_congr_set hae
  rw [hrest]
  have h := integral_map_equiv (μ := cubeVolume d) (gridAffineEquiv k hk c) f
  simp only [gridAffineEquiv_apply] at h; rw [← h]
  change _ = ∫ z, f z ∂(cubeVolume d).map (gridAffine k c)
  rw [gridAffine_map_cubeVolume k hk c, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]; rfl

def dyadicNormalizedAnchor {d : ℕ} (j : ℕ) (x : Covariate d) : Covariate d :=
  gridNormalizedAnchor ((2 : ℕ) ^ j) (by positivity) x

def dyadicCellAffine {d : ℕ} (j : ℕ) (x w : Covariate d) : Covariate d :=
  gridAffine ((2 : ℕ) ^ j) (regularGridCell _ (by positivity) x) w

def dyadicNormalizedDensity {d : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : Covariate d → ℝ := θ.density ∘ dyadicCellAffine j x

def dyadicKnownGram {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ := fun γ δ =>
  dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂cubeVolume d

def dyadicPopulationGram {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ := fun γ δ =>
  dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ ∂designLaw θ

def dyadicPreconditionedGram {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  (dyadicKnownGram j x)⁻¹ * dyadicPopulationGram θ j x

private lemma dyadic_designLaw_cell_integral {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (f : Covariate d → ℝ) :
    dyadicPilotScale d j * (∫ z in dyadicPilotCell j x, f z ∂designLaw θ) =
      ∫ w, dyadicNormalizedDensity θ j x w * f (dyadicCellAffine j x w) ∂cubeVolume d := by
  unfold designLaw
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    hθ.1.ennreal_ofReal.aemeasurable (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f
    (dyadicPilotCell_measurable j x)]
  have hcongr : (∫ z in dyadicPilotCell j x, (ENNReal.ofReal (θ.density z)).toReal • f z ∂cubeVolume d) =
      ∫ z in dyadicPilotCell j x, θ.density z * f z ∂cubeVolume d := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hθ.2.2.1] with z hz
    rw [ENNReal.toReal_ofReal (C.densityLower_pos.le.trans hz.1)]; rfl
  rw [hcongr, show dyadicPilotScale d j = ((((2 : ℕ) ^ j : ℕ) : ℝ)) ^ d by simp [dyadicPilotScale]]
  exact regular_grid_cell_integral ((2 : ℕ) ^ j) (by positivity) (regularGridCell _ (by positivity) x)
    (fun z => θ.density z * f z)

theorem dyadicKnownGram_eq_normalized {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    dyadicKnownGram (ℓ := ℓ) j x = anchoredGram (dyadicNormalizedAnchor j x) := by
  ext γ δ
  simpa only [Nat.cast_pow, Nat.cast_ofNat, dyadicKnownGram, dyadicPilotScale,
    dyadicPilotCell, preimage, mem_singleton_iff, dyadicAnchoredFeature_affine,
    anchoredGram, dyadicNormalizedAnchor] using
    regular_grid_cell_integral ((2 : ℕ) ^ j) (by positivity) (regularGridCell _ (by positivity) x)
      (fun z => dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ)

theorem dyadicPopulationGram_eq_normalized {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    dyadicPopulationGram (ℓ := ℓ) θ j x =
      anchoredDensityGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) := by
  ext γ δ
  simpa only [dyadicPopulationGram, dyadicCellAffine, dyadicAnchoredFeature_affine,
    anchoredDensityGram, dyadicNormalizedAnchor] using
    dyadic_designLaw_cell_integral C θ hθ j x
      (fun z => dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ)

theorem dyadicNormalizedDensity_measurable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    Measurable (dyadicNormalizedDensity θ j x) :=
  hθ.1.comp (gridAffineEquiv _ (by positivity) _).measurable

theorem dyadicNormalizedDensity_bounds {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ dyadicNormalizedDensity θ j x w ∧
      dyadicNormalizedDensity θ j x w ≤ C.densityUpper :=
  gridAffine_ae_pullback _ (by positivity) _ hθ.2.2.1

theorem dyadicKnownGram_posDef {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    (dyadicKnownGram (ℓ := ℓ) j x).PosDef := by
  rw [dyadicKnownGram_eq_normalized]; exact anchoredGram_posDef _

def dyadicResponseMoment {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : AnchoredIndex d ℓ → ℝ :=
  fun γ => dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ * θ.regression z ∂designLaw θ

def dyadicConstantMoment {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : AnchoredIndex d ℓ → ℝ :=
  fun γ => dyadicPilotScale d j * ∫ z in dyadicPilotCell j x,
    dyadicAnchoredFeature j x z γ ∂designLaw θ

private lemma observationLaw_integral_design {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (g : Covariate d → ℝ)
    (hg : Measurable g) : (∫ z, g z.1 ∂observationLaw θ) = ∫ x, g x ∂designLaw θ := by
  have hp := observationLaw_fst_measurePreserving C θ hθ
  rw [← hp.map_eq]; exact (integral_map hp.aemeasurable hg.aestronglyMeasurable).symm

theorem dyadicPilotPopulation_gram {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (γ δ : AnchoredIndex d ℓ) :
    dyadicPilotPopulation θ j x (Sum.inl (γ, δ)) = dyadicPopulationGram θ j x γ δ := by
  unfold dyadicPilotPopulation dyadicPilotFeature; rw [integral_const_mul]
  change dyadicPilotScale d j * (∫ z, (dyadicPilotCell j x).indicator
    (fun z => dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ) z.1 ∂observationLaw θ) = _
  have hg : Measurable fun z => dyadicAnchoredFeature j x z γ * dyadicAnchoredFeature j x z δ :=
    (dyadicAnchoredFeature_measurable j x γ).mul (dyadicAnchoredFeature_measurable j x δ)
  rw [observationLaw_integral_design C θ hθ _ (hg.indicator (dyadicPilotCell_measurable j x)),
    integral_indicator (dyadicPilotCell_measurable j x)]; rfl

theorem dyadicPilotPopulation_constant {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (γ : AnchoredIndex d ℓ) :
    dyadicPilotPopulation θ j x (Sum.inr (Sum.inr γ)) = dyadicConstantMoment θ j x γ := by
  unfold dyadicPilotPopulation dyadicPilotFeature; rw [integral_const_mul]
  change dyadicPilotScale d j * (∫ z, (dyadicPilotCell j x).indicator
    (fun z => dyadicAnchoredFeature j x z γ) z.1 ∂observationLaw θ) = _
  rw [observationLaw_integral_design C θ hθ _
    ((dyadicAnchoredFeature_measurable j x γ).indicator (dyadicPilotCell_measurable j x)),
    integral_indicator (dyadicPilotCell_measurable j x)]; rfl

theorem dyadicPilotPopulation_response {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (γ : AnchoredIndex d ℓ) :
    dyadicPilotPopulation θ j x (Sum.inr (Sum.inl γ)) = dyadicResponseMoment θ j x γ := by
  let := observationLaw_isProbability C θ hθ
  unfold dyadicPilotPopulation
  rw [observationLaw_integral_conditioning C θ hθ _
    ((dyadicPilotFeature_memLp_two C θ hθ j x hx (Sum.inr (Sum.inl γ))).integrable (by norm_num))]
  have heq : (fun z => ∫ u, dyadicPilotFeature j x (Sum.inr (Sum.inl γ)) (z, θ.regression z + u) ∂θ.errors z) =ᵐ[designLaw θ]
      fun z => dyadicPilotScale d j * (dyadicPilotCell j x).indicator
        (fun z => dyadicAnchoredFeature j x z γ * θ.regression z) z := by
    filter_upwards [hθ.2.2.2.2.2.2.2] with z hz
    by_cases hcell : z ∈ dyadicPilotCell j x
    · rw [show (fun u => dyadicPilotFeature j x (Sum.inr (Sum.inl γ)) (z, θ.regression z + u)) =
        fun u => dyadicPilotScale d j * ((θ.regression z + u) * dyadicAnchoredFeature j x z γ)
        from funext fun _ => by simp [dyadicPilotFeature, dyadicPilotScalar, hcell],
        integral_const_mul, integral_mul_const, indicator_of_mem hcell,
        integral_add (integrable_const _) hz.1, integral_const, hz.2.2.2.1]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, add_zero]; ring
    · simp [dyadicPilotFeature, hcell]
  rw [integral_congr_ae heq, integral_const_mul, integral_indicator (dyadicPilotCell_measurable j x)]; rfl

theorem dyadicResponseMoment_eq_normalized {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    dyadicResponseMoment (ℓ := ℓ) θ j x =
      anchoredVectorMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
        (θ.regression ∘ dyadicCellAffine j x) := by
  funext γ
  refine (dyadic_designLaw_cell_integral C θ hθ j x _).trans ?_
  refine integral_congr_ae <| Filter.Eventually.of_forall fun w => ?_
  dsimp only [Function.comp_apply, dyadicCellAffine, dyadicNormalizedAnchor]
  rw [dyadicAnchoredFeature_affine]; ring

theorem dyadicConstantMoment_eq_normalized {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    dyadicConstantMoment (ℓ := ℓ) θ j x =
      anchoredVectorMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) (fun _ => 1) := by
  funext γ
  refine (dyadic_designLaw_cell_integral C θ hθ j x _).trans ?_
  refine integral_congr_ae <| Filter.Eventually.of_forall fun w => ?_
  dsimp only [dyadicCellAffine, dyadicNormalizedAnchor]
  rw [dyadicAnchoredFeature_affine]; ring

-- 6. Local polynomial fits, error bounds & Taylor family (`AnchoredFit`, `AnchoredFitError`, `DyadicFit`, `DyadicTaylor`)

def anchoredPopulationFit {d ℓ : ℕ} (u : Covariate d) (p g : Covariate d → ℝ) :
    AnchoredIndex d ℓ → ℝ := (anchoredDensityGram u p)⁻¹ *ᵥ anchoredVectorMoment u p g

def anchoredFitPolynomial {d ℓ : ℕ} (u : Covariate d) (c : AnchoredIndex d ℓ → ℝ) :
    Covariate d → ℝ := fun w => ∑ γ, c γ * anchoredFeature u w γ

private theorem anchoredFitPolynomial_continuous {d ℓ : ℕ} (u : Covariate d)
    (c : AnchoredIndex d ℓ → ℝ) : Continuous (anchoredFitPolynomial u c) :=
  continuous_finsetSum _ fun γ _ =>
    ((anchoredMonomial_continuous γ).comp (continuous_id.sub continuous_const)).const_mul _

theorem dyadicAnchoredFeature_transport_dot {d ℓ : ℕ} (j : ℕ) (x z : Covariate d)
    (c : AnchoredIndex d ℓ → ℝ) :
    dyadicAnchoredFeature (j + 1) x z ⬝ᵥ (anchoredTransport d ℓ *ᵥ c) =
      dyadicAnchoredFeature j x z ⬝ᵥ c := by
  have hT : (anchoredTransport d ℓ)ᵀ = anchoredTransport d ℓ := Matrix.diagonal_transpose _
  rw [Matrix.dotProduct_mulVec, ← hT, Matrix.vecMul_transpose, dyadicAnchoredFeature_transport]

def anchoredIncrement {d ℓ : ℕ} (a : ℕ → AnchoredIndex d ℓ → ℝ) : ℕ → AnchoredIndex d ℓ → ℝ
  | 0 => a 0
  | j + 1 => a (j + 1) - anchoredTransport d ℓ *ᵥ a j

theorem anchored_increment_telescope {d ℓ : ℕ} (a : ℕ → AnchoredIndex d ℓ → ℝ)
    (x z : Covariate d) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), dyadicAnchoredFeature j x z ⬝ᵥ anchoredIncrement a j) =
      dyadicAnchoredFeature J x z ⬝ᵥ a J := by
  induction J with
  | zero => simp [anchoredIncrement]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    change dyadicAnchoredFeature J x z ⬝ᵥ a J +
      dyadicAnchoredFeature (J + 1) x z ⬝ᵥ (a (J + 1) - anchoredTransport d ℓ *ᵥ a J) = _
    rw [dotProduct_sub, dyadicAnchoredFeature_transport_dot]; ring

private theorem anchoredVectorMoment_sub {d ℓ : ℕ} (u : Covariate d)
    (p g h : Covariate d → ℝ) (hpmeas : Measurable p) (b : ℝ)
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b)
    (hg : ContinuousOn g (unitCube d)) (hh : ContinuousOn h (unitCube d)) :
    anchoredVectorMoment (ℓ := ℓ) u p (g - h) =
      anchoredVectorMoment u p g - anchoredVectorMoment u p h := by
  have hint (fn : Covariate d → ℝ) (hfn : ContinuousOn fn (unitCube d)) (γ : AnchoredIndex d ℓ) :
      Integrable (fun w => p w * anchoredFeature u w γ * fn w) (cubeVolume d) := by
    have hc : ContinuousOn (fun w => anchoredFeature u w γ * fn w) (unitCube d) :=
      (((anchoredMonomial_continuous γ).comp (continuous_id.sub continuous_const)).continuousOn).mul hfn
    have hi : Integrable (fun w => anchoredFeature u w γ * fn w) (cubeVolume d) :=
      ContinuousOn.integrableOn_compact (μ := volume) (unitCube_isCompact d) hc
    convert hi.bdd_mul hpmeas.aestronglyMeasurable
      (hp.mono fun _ hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2) using 1
    funext w; ring
  ext γ
  change (∫ w, p w * anchoredFeature u w γ * (g w - h w) ∂cubeVolume d) = _
  simp only [mul_sub]; exact integral_sub (hint g hg γ) (hint h hh γ)

theorem anchoredPopulationFit_coefficient_error {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)]
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ D : ℝ, 0 < D ∧ ∀ u ∈ unitCube d, ∀ p g : Covariate d → ℝ,
      Measurable p → (∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) →
      ContinuousOn g (unitCube d) → ∀ c : AnchoredIndex d ℓ → ℝ,
      ∀ R : ℝ, 0 ≤ R → (∀ w ∈ unitCube d, |g w - anchoredFitPolynomial u c w| ≤ R) →
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredPopulationFit u p g - c)‖ ≤ D * R := by
  obtain ⟨cB, _, hcB, _, hGram⟩ := anchoredGram_uniform_bounds (d := d) (ℓ := ℓ)
  let D := max 1 (Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * b / (a * cB))
  refine ⟨D, zero_lt_one.trans_le (le_max_left _ _), fun u hu p g hpmeas hp hg c R hR hres => ?_⟩
  have hp0 : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b := hp.mono fun _ hw => ⟨ha.le.trans hw.1, hw.2⟩
  have hnorm_eq : anchoredDensityGram (ℓ := ℓ) u p *ᵥ anchoredPopulationFit u p g = anchoredVectorMoment u p g := by
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (anchoredDensityGram_posDef (ℓ := ℓ) u p hpmeas a b ha hp).isUnit
    rw [anchoredPopulationFit, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hpoly_mom : anchoredVectorMoment u p (anchoredFitPolynomial u c) = anchoredDensityGram u p *ᵥ c := by
    ext γ; unfold anchoredVectorMoment anchoredFitPolynomial; simp only [Finset.mul_sum]
    have hi (δ : AnchoredIndex d ℓ) : Integrable (fun w => p w * anchoredFeature u w γ * (c δ * anchoredFeature u w δ)) (cubeVolume d) := by
      rw [show (fun w => p w * anchoredFeature u w γ * (c δ * anchoredFeature u w δ)) =
        fun w => (p w * (anchoredFeature u w γ * anchoredFeature u w δ)) * c δ from funext fun _ => by ring]
      exact (anchoredDensityGram_product_integrable u p hpmeas b hp0 γ δ).mul_const _
    rw [integral_finsetSum _ fun δ _ => hi δ]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [show (fun w => p w * anchoredFeature u w γ * (c δ * anchoredFeature u w δ)) =
      fun w => (p w * (anchoredFeature u w γ * anchoredFeature u w δ)) * c δ from funext fun _ => by ring,
      integral_mul_const]; rfl
  let e := anchoredPopulationFit u p g - c
  let r : AnchoredIndex d ℓ → ℝ := anchoredVectorMoment u p (g - anchoredFitPolynomial u c)
  have her : anchoredDensityGram u p *ᵥ e = r := by
    dsimp [e, r]
    rw [Matrix.mulVec_sub, hnorm_eq, anchoredVectorMoment_sub u p g _ hpmeas b hp0 hg
      (anchoredFitPolynomial_continuous u c).continuousOn, hpoly_mom]
  let E := (EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm e
  let Rv := (EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm r
  have hcoer : a * cB * ‖E‖ ^ 2 ≤ e ⬝ᵥ r := by
    calc a * cB * ‖E‖ ^ 2 = a * (cB * ‖E‖ ^ 2) := by ring
      _ ≤ a * anchoredQuadratic u E := mul_le_mul_of_nonneg_left (hGram u hu E).1 ha.le
      _ ≤ e ⬝ᵥ r := by simpa [anchoredQuadratic, her, E, EuclideanSpace.equiv] using
          (anchoredDensityGram_quadratic_bounds u p hpmeas a b ha.le hp e).1
  have hinner : e ⬝ᵥ r ≤ ‖E‖ * ‖Rv‖ := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm, E, Rv, EuclideanSpace.equiv]
      using real_inner_le_norm E Rv
  have hE_le : ‖E‖ ≤ ‖Rv‖ / (a * cB) := by
    by_cases hE0 : ‖E‖ = 0
    · rw [hE0]; positivity
    · have : 0 < ‖E‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hE0)
      exact (le_div_iff₀ (mul_pos ha hcB)).2 (by nlinarith)
  have hr := anchoredVectorMoment_norm_bound (ℓ := ℓ) u hu p (g - anchoredFitPolynomial u c) b R hb hR hp0 hres
  refine hE_le.trans ((div_le_div_of_nonneg_right hr (mul_pos ha hcB).le).trans ?_)
  rw [show Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (b * R) / (a * cB) =
    (Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * b / (a * cB)) * R by ring]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) hR

theorem anchoredPopulationFit_pointwise_error {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)]
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ D : ℝ, 0 < D ∧ ∀ u ∈ unitCube d, ∀ p g : Covariate d → ℝ,
      Measurable p → (∀ᵐ v ∂cubeVolume d, a ≤ p v ∧ p v ≤ b) →
      ContinuousOn g (unitCube d) → ∀ c : AnchoredIndex d ℓ → ℝ,
      ∀ R : ℝ, 0 ≤ R → (∀ v ∈ unitCube d, |g v - anchoredFitPolynomial u c v| ≤ R) →
      ∀ w ∈ unitCube d,
      |g w - anchoredFitPolynomial u (anchoredPopulationFit (ℓ := ℓ) u p g) w| ≤
        |g w - anchoredFitPolynomial u c w| + D * R * euclideanNorm (w - u) := by
  obtain ⟨D, _, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := ℓ) a b ha hb
  let E := max 1 ((Fintype.card (AnchoredIndex d ℓ) : ℝ) * D)
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), fun u hu p g hpmeas hp hg c R hR hres w hw => ?_⟩
  have hcoeff := hfit u hu p g hpmeas hp hg c R hR hres
  let diff := anchoredPopulationFit u p g - c
  have hpoly : |anchoredFitPolynomial u diff w| ≤
      (Fintype.card (AnchoredIndex d ℓ) : ℝ) * ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm diff‖ *
        euclideanNorm (w - u) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (g := fun _ : AnchoredIndex d ℓ =>
        ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm diff‖ * euclideanNorm (w - u)) fun γ _ => ?_).trans_eq
        (by simp; ring))
    rw [abs_mul]
    refine mul_le_mul ?_ (anchoredFeature_abs_le_euclideanNorm u w hu hw γ) (abs_nonneg _) (norm_nonneg _)
    simpa [Real.norm_eq_abs, EuclideanSpace.equiv] using
      PiLp.norm_apply_le ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm diff) γ
  have hnonneg : 0 ≤ euclideanNorm (w - u) := by unfold euclideanNorm; positivity
  have habs : |anchoredFitPolynomial u diff w| ≤ E * R * euclideanNorm (w - u) := by
    refine hpoly.trans ?_
    calc _ ≤ (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (D * R) * euclideanNorm (w - u) := by gcongr
      _ = ((Fintype.card (AnchoredIndex d ℓ) : ℝ) * D) * R * euclideanNorm (w - u) := by ring
      _ ≤ E * R * euclideanNorm (w - u) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hR) hnonneg
  rw [show g w - anchoredFitPolynomial u (anchoredPopulationFit (ℓ := ℓ) u p g) w =
    (g w - anchoredFitPolynomial u c w) - anchoredFitPolynomial u diff w by
      simp only [anchoredFitPolynomial, diff, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; ring]
  exact (abs_sub _ _).trans (add_le_add le_rfl habs)

def dyadicRegressionDifference {d : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : Covariate d → ℝ :=
  fun w => θ.regression (dyadicCellAffine j x w) - θ.regression x

def dyadicPopulationFit {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : AnchoredIndex d ℓ → ℝ :=
  (dyadicPopulationGram θ j x)⁻¹ *ᵥ
    (dyadicResponseMoment θ j x - θ.regression x • dyadicConstantMoment θ j x)

private theorem dyadicCellAffine_continuous {d : ℕ} (j : ℕ) (x : Covariate d) :
    Continuous (dyadicCellAffine j x) :=
  continuous_pi fun i => continuous_const.add (continuous_const.mul (continuous_apply i))

theorem dyadicCellAffine_mem_cube {d : ℕ} (j : ℕ) (x w : Covariate d)
    (hw : w ∈ unitCube d) : dyadicCellAffine j x w ∈ unitCube d := by
  apply gridClosedBox_subset_cube ((2 : ℕ) ^ j) (by positivity) (regularGridCell _ (by positivity) x)
  change w ∈ gridAffine _ _ ⁻¹' gridClosedBox _ _
  rwa [gridAffine_preimage_box _ (by positivity) _]

theorem dyadicCellAffine_anchor {d : ℕ} (j : ℕ) (x : Covariate d) :
    dyadicCellAffine j x (dyadicNormalizedAnchor j x) = x := by
  funext i
  simp only [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hk : (((2 : ℕ) ^ j : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp; ring

private theorem dyadicCellAffine_difference {d : ℕ} (j : ℕ) (x w : Covariate d) :
    dyadicCellAffine j x w - x = ((2 : ℝ) ^ j)⁻¹ • (w - dyadicNormalizedAnchor j x) := by
  funext i
  simp only [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Nat.cast_pow, Nat.cast_ofNat]
  have hk : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp; ring

private theorem admissible_regression_continuousOn_cube {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) : ContinuousOn θ.regression (unitCube d) := by
  obtain ⟨F, hF, hreg, _⟩ := hθ.2.2.2.2.1
  exact (hreg.continuousOn.mono C.cube_subset).congr fun x hx => (hF x hx).symm

theorem dyadicRegressionDifference_continuousOn {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    ContinuousOn (dyadicRegressionDifference θ j x) (unitCube d) :=
  ((admissible_regression_continuousOn_cube C θ hθ).comp
    (dyadicCellAffine_continuous j x).continuousOn (dyadicCellAffine_mem_cube j x)).sub continuousOn_const

theorem dyadicPopulationFit_eq_normalized {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    dyadicPopulationFit (ℓ := ℓ) θ j x = anchoredPopulationFit (dyadicNormalizedAnchor j x)
      (dyadicNormalizedDensity θ j x) (dyadicRegressionDifference θ j x) := by
  unfold dyadicPopulationFit anchoredPopulationFit
  rw [dyadicPopulationGram_eq_normalized C θ hθ,
    dyadicResponseMoment_eq_normalized C θ hθ, dyadicConstantMoment_eq_normalized C θ hθ]
  congr 1
  have hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ dyadicNormalizedDensity θ j x w ∧
      dyadicNormalizedDensity θ j x w ≤ C.densityUpper :=
    (dyadicNormalizedDensity_bounds C θ hθ j x).mono fun _ hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩
  have hc := (admissible_regression_continuousOn_cube C θ hθ).comp
    (dyadicCellAffine_continuous j x).continuousOn (dyadicCellAffine_mem_cube j x)
  rw [show dyadicRegressionDifference θ j x = (θ.regression ∘ dyadicCellAffine j x) - (fun _ => θ.regression x) from rfl,
    anchoredVectorMoment_sub _ _ _ _ (dyadicNormalizedDensity_measurable C θ hθ j x) C.densityUpper hp hc continuousOn_const]
  congr 1; ext γ
  change θ.regression x * (∫ w, dyadicNormalizedDensity θ j x w *
    anchoredFeature (dyadicNormalizedAnchor j x) w γ * 1 ∂cubeVolume d) =
      ∫ w, dyadicNormalizedDensity θ j x w * anchoredFeature (dyadicNormalizedAnchor j x) w γ * θ.regression x ∂cubeVolume d
  simp only [mul_one]; rw [integral_mul_const]; ring

def dyadicTaylorCoefficients {d ℓ : ℕ} (c : AnchoredIndex d ℓ → ℝ) (j : ℕ) :
    AnchoredIndex d ℓ → ℝ := (anchoredTransport d ℓ) ^ j *ᵥ c

theorem dyadicTaylorCoefficients_succ {d ℓ : ℕ} (c : AnchoredIndex d ℓ → ℝ) (j : ℕ) :
    dyadicTaylorCoefficients c (j + 1) = anchoredTransport d ℓ *ᵥ dyadicTaylorCoefficients c j := by
  rw [dyadicTaylorCoefficients, pow_succ', ← Matrix.mulVec_mulVec]; rfl

theorem euclideanNorm_smul {d : ℕ} (a : ℝ) (v : Covariate d) :
    euclideanNorm (a • v) = |a| * euclideanNorm v := by
  unfold euclideanNorm; simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem dyadicCellAffine_euclidean_distance {d : ℕ} (j : ℕ) (x w : Covariate d) :
    euclideanNorm (dyadicCellAffine j x w - x) =
      ((2 : ℝ) ^ j)⁻¹ * euclideanNorm (w - dyadicNormalizedAnchor j x) := by
  rw [dyadicCellAffine_difference, euclideanNorm_smul, abs_of_nonneg (by positivity)]

theorem admissible_dyadic_taylor_family {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (x : Covariate d) (hx : x ∈ unitCube d) :
    ∃ c : AnchoredIndex d C.order → ℝ, ∀ j : ℕ, ∀ w ∈ unitCube d,
      |dyadicRegressionDifference θ j x w -
        anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w| ≤
          taylorErrorFactor C * C.holderBound * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness ∧
      |dyadicRegressionDifference θ j x w -
        anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w| ≤
          ((d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial) *
            (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness *
              euclideanNorm (w - dyadicNormalizedAnchor j x) ^ C.smoothness := by
  obtain ⟨P, hP, herr⟩ := admissible_regression_taylor C θ hθ x hx
  have hxP : MvPolynomial.eval x P = θ.regression x := by
    have h := herr x hx
    simp [euclideanNorm, Real.zero_rpow C.smoothness_pos.ne'] at h
    exact (sub_eq_zero.mp h).symm
  have hP0 : (P - MvPolynomial.C (θ.regression x)).totalDegree ≤ C.order :=
    (MvPolynomial.totalDegree_sub _ _).trans (max_le hP (by simp))
  obtain ⟨c, hc⟩ := polynomial_centered_representation x _ hP0 (by rw [map_sub, MvPolynomial.eval_C, hxP, sub_self])
  have heval_norm (j : ℕ) (w : Covariate d) :
      anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w =
        anchoredFitPolynomial x c (dyadicCellAffine j x w) := by
    have heval (k : ℕ) (z : Covariate d) :
        dyadicAnchoredFeature k x z ⬝ᵥ dyadicTaylorCoefficients c k = anchoredFitPolynomial x c z := by
      induction k with
      | zero =>
        simp only [dyadicTaylorCoefficients, pow_zero, Matrix.one_mulVec, dyadicAnchoredFeature,
          one_mul, anchoredFeature, anchoredFitPolynomial, dotProduct]
        exact Finset.sum_congr rfl fun _ _ => by rw [show (fun i => z i - x i) = z - x from rfl]; ring
      | succ k ih => rw [dyadicTaylorCoefficients_succ, dyadicAnchoredFeature_transport_dot, ih]
    rw [← heval j (dyadicCellAffine j x w),
      show dyadicAnchoredFeature (ℓ := C.order) j x (dyadicCellAffine j x w) =
        anchoredFeature (dyadicNormalizedAnchor j x) w from funext fun γ => dyadicAnchoredFeature_affine j x w γ]
    unfold anchoredFitPolynomial dotProduct; exact Finset.sum_congr rfl fun _ _ => by ring
  refine ⟨c, fun j w hw => ?_⟩
  have heq : dyadicRegressionDifference θ j x w -
      anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w =
        θ.regression (dyadicCellAffine j x w) - MvPolynomial.eval (dyadicCellAffine j x w) P := by
    rw [heval_norm, show anchoredFitPolynomial x c (dyadicCellAffine j x w) =
      MvPolynomial.eval (dyadicCellAffine j x w) (P - MvPolynomial.C (θ.regression x)) from (hc _).symm,
      map_sub, MvPolynomial.eval_C]
    unfold dyadicRegressionDifference; ring
  rw [heq]
  have hy := dyadicCellAffine_mem_cube j x w hw
  have hcoef : 0 ≤ (d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial :=
    div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _) (mul_nonneg (by norm_num) C.holderBound_pos.le)) (Nat.cast_nonneg _)
  have hrad (i : Fin d) : |dyadicCellAffine j x w i - x i| ≤ ((2 : ℝ) ^ j)⁻¹ := by
    have hu : dyadicNormalizedAnchor j x ∈ unitCube d :=
      gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ j) (by positivity) x hx
    have hi : |w i - dyadicNormalizedAnchor j x i| ≤ 1 :=
      abs_le.mpr ⟨by linarith [(hw i).1, (hu i).2], by linarith [(hw i).2, (hu i).1]⟩
    have he := congrFun (dyadicCellAffine_difference j x w) i
    change dyadicCellAffine j x w i - x i = ((2 : ℝ) ^ j)⁻¹ * (w i - dyadicNormalizedAnchor j x i) at he
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((2 : ℝ) ^ j)⁻¹)]
    exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (mul_one _)
  refine ⟨?_, ?_⟩
  · have hdist := euclideanNorm_le_coordinate_radius (dyadicCellAffine j x w - x) (((2 : ℝ) ^ j)⁻¹) (by positivity) hrad
    refine (herr _ hy).trans ((mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by unfold euclideanNorm; positivity) hdist C.smoothness_pos.le) hcoef).trans_eq ?_)
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (by positivity)]; unfold taylorErrorFactor; ring
  · convert herr _ hy using 1
    rw [dyadicCellAffine_euclidean_distance, Real.mul_rpow (by positivity) (by unfold euclideanNorm; positivity)]; ring

-- 7. Known-Gram preconditioned pilot (`PreconditionedPilot`)

def localPilotRow {d ℓ : ℕ} (a : LocalPilotIndex d ℓ) : AnchoredIndex d ℓ :=
  match a with
  | Sum.inl (γ, _) => γ
  | Sum.inr (Sum.inl γ) => γ
  | Sum.inr (Sum.inr γ) => γ

def localPilotReplaceRow {d ℓ : ℕ} (a : LocalPilotIndex d ℓ)
    (β : AnchoredIndex d ℓ) : LocalPilotIndex d ℓ :=
  match a with
  | Sum.inl (_, δ) => Sum.inl (β, δ)
  | Sum.inr (Sum.inl _) => Sum.inr (Sum.inl β)
  | Sum.inr (Sum.inr _) => Sum.inr (Sum.inr β)

def preconditionedPilotFeature {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) : ℝ :=
  ∑ β : AnchoredIndex d ℓ, (dyadicKnownGram j x)⁻¹ (localPilotRow a) β *
    dyadicPilotFeature j x (localPilotReplaceRow a β) z

def preconditionedPilotPopulation {d ℓ : ℕ} (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (a : LocalPilotIndex d ℓ) : ℝ :=
  ∫ z, preconditionedPilotFeature j x a z ∂observationLaw θ

theorem preconditionedPilotFeature_measurable {d ℓ : ℕ} (j : ℕ)
    (x : Covariate d) (a : LocalPilotIndex d ℓ) : Measurable (preconditionedPilotFeature j x a) :=
  Finset.measurable_sum Finset.univ fun _ _ => measurable_const.mul (dyadicPilotFeature_measurable j x _)

theorem preconditionedPilotFeature_memLp_two {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ) :
    MemLp (preconditionedPilotFeature j x a) 2 (observationLaw θ) :=
  memLp_finsetSum Finset.univ fun β _ =>
    (dyadicPilotFeature_memLp_two C θ hθ j x hx (localPilotReplaceRow a β)).const_mul _

theorem preconditionedPilotPopulation_eq_sum {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ) :
    preconditionedPilotPopulation θ j x a =
      ∑ β : AnchoredIndex d ℓ, (dyadicKnownGram j x)⁻¹ (localPilotRow a) β *
        dyadicPilotPopulation θ j x (localPilotReplaceRow a β) := by
  let := observationLaw_isProbability C θ hθ
  unfold preconditionedPilotPopulation preconditionedPilotFeature
  rw [integral_finsetSum _ fun _ _ =>
    ((dyadicPilotFeature_memLp_two C θ hθ j x hx _).integrable (by norm_num)).const_mul _]
  simp only [integral_const_mul, dyadicPilotPopulation]

theorem preconditionedPilotPopulation_gram {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (γ δ : AnchoredIndex d ℓ) :
    preconditionedPilotPopulation θ j x (Sum.inl (γ, δ)) = dyadicPreconditionedGram θ j x γ δ := by
  rw [preconditionedPilotPopulation_eq_sum C θ hθ j x hx]
  simp only [localPilotRow, localPilotReplaceRow, dyadicPilotPopulation_gram C θ hθ,
    dyadicPreconditionedGram, Matrix.mul_apply]

theorem preconditionedPilotPopulation_response {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (γ : AnchoredIndex d ℓ) :
    preconditionedPilotPopulation θ j x (Sum.inr (Sum.inl γ)) =
      anchoredPreconditionedMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
        (θ.regression ∘ dyadicCellAffine j x) γ := by
  rw [preconditionedPilotPopulation_eq_sum C θ hθ j x hx]
  simp only [localPilotRow, localPilotReplaceRow, dyadicPilotPopulation_response C θ hθ j x hx,
    dyadicKnownGram_eq_normalized, anchoredPreconditionedMoment, Matrix.mulVec, dotProduct,
    dyadicResponseMoment_eq_normalized C θ hθ]

theorem preconditionedPilotPopulation_constant {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (γ : AnchoredIndex d ℓ) :
    preconditionedPilotPopulation θ j x (Sum.inr (Sum.inr γ)) =
      anchoredPreconditionedMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) (fun _ => 1) γ := by
  rw [preconditionedPilotPopulation_eq_sum C θ hθ j x hx]
  simp only [localPilotRow, localPilotReplaceRow, dyadicPilotPopulation_constant C θ hθ,
    dyadicKnownGram_eq_normalized, anchoredPreconditionedMoment, Matrix.mulVec, dotProduct,
    dyadicConstantMoment_eq_normalized C θ hθ]

theorem dyadicKnownGram_inverse_uniform_bound {d ℓ : ℕ} :
    ∃ L : ℝ, 0 < L ∧ ∀ j : ℕ, ∀ x ∈ unitCube d, ‖(dyadicKnownGram (ℓ := ℓ) j x)⁻¹‖ ≤ L := by
  obtain ⟨L, hL, hbound⟩ := anchoredGram_inverse_uniform_bound (d := d) (ℓ := ℓ)
  exact ⟨L, hL, fun j x hx => by rw [dyadicKnownGram_eq_normalized]; exact hbound _ (gridNormalizedAnchor_mem_cube _ _ x hx)⟩

def preconditionedPilotMomentConstant {d : ℕ} (C : ModelConstants d) (ℓ : ℕ) : ℝ :=
  max 1 ((Fintype.card (AnchoredIndex d ℓ) : ℝ) ^ 2 *
    (Classical.choose (dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ))) ^ 2 *
    dyadicPilotMomentConstant C)

theorem preconditionedPilotMomentConstant_pos {d : ℕ} (C : ModelConstants d) (ℓ : ℕ) :
    0 < preconditionedPilotMomentConstant C ℓ := zero_lt_one.trans_le (le_max_left _ _)

theorem preconditionedPilotFeature_uniform_second_le {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ) :
    (∫ z, preconditionedPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  letI : Nonempty (AnchoredIndex d ℓ) := ⟨localPilotRow a⟩
  let L := Classical.choose (dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ))
  obtain ⟨hL, hB_all⟩ := Classical.choose_spec (dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ))
  let B := (dyadicKnownGram (ℓ := ℓ) j x)⁻¹
  let f (β : AnchoredIndex d ℓ) (z : Observation d) :=
    B (localPilotRow a) β * dyadicPilotFeature j x (localPilotReplaceRow a β) z
  have hlp (β : AnchoredIndex d ℓ) : MemLp (f β) 2 (observationLaw θ) :=
    (dyadicPilotFeature_memLp_two C θ hθ j x hx _).const_mul _
  have hfirst : (∫ z, preconditionedPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      (Fintype.card (AnchoredIndex d ℓ) : ℝ) * ∑ β, ∫ z, f β z ^ 2 ∂observationLaw θ := by
    have h := integral_mono (preconditionedPilotFeature_memLp_two C θ hθ j x hx a).integrable_sq
      ((integrable_finsetSum Finset.univ fun β _ => (hlp β).integrable_sq).const_mul _)
      fun z => by simpa [preconditionedPilotFeature, f, B] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun β => f β z)
    rwa [integral_const_mul, integral_finsetSum _ fun β _ => (hlp β).integrable_sq] at h
  have hcoord (β : AnchoredIndex d ℓ) : (∫ z, f β z ^ 2 ∂observationLaw θ) ≤
      L ^ 2 * dyadicPilotMomentConstant C * dyadicPilotScale d j := by
    simp only [f, mul_pow, integral_const_mul]
    have hb : |B (localPilotRow a) β| ≤ L := by
      simpa only [Real.norm_eq_abs] using (matrix_real_entry_norm_le B (localPilotRow a) β).trans (hB_all j x hx)
    have hb2 : B (localPilotRow a) β ^ 2 ≤ L ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    refine (mul_le_mul_of_nonneg_left (dyadicPilotFeature_second_le C θ hθ j x hx _) (sq_nonneg _)).trans ?_
    have hc := dyadicPilotMomentConstant_pos C; have hk := dyadicPilotScale_pos d j
    nlinarith [mul_le_mul_of_nonneg_right hb2 (mul_nonneg hc.le hk.le)]
  calc (∫ z, preconditionedPilotFeature j x a z ^ 2 ∂observationLaw θ)
    _ ≤ (Fintype.card (AnchoredIndex d ℓ) : ℝ) * ∑ β, ∫ z, f β z ^ 2 ∂observationLaw θ := hfirst
    _ ≤ (Fintype.card (AnchoredIndex d ℓ) : ℝ) *
          ∑ _β : AnchoredIndex d ℓ, (L ^ 2 * dyadicPilotMomentConstant C * dyadicPilotScale d j) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun β _ => hcoord β) (Nat.cast_nonneg _)
    _ = ((Fintype.card (AnchoredIndex d ℓ) : ℝ) ^ 2 * L ^ 2 * dyadicPilotMomentConstant C) *
          dyadicPilotScale d j := by simp; ring
    _ ≤ preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (dyadicPilotScale_pos d j).le

end NearlyMinimax
