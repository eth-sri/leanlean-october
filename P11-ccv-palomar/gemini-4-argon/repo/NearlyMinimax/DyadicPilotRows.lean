module
public import NearlyMinimax.IncrementPilotFeatures
public import NearlyMinimax.PairDesignMeasure
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
section
open MvPolynomial Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
variable {d ℓ : ℕ}
def affinePullbackPolynomial  (ℓ : ℕ) (a : Covariate d) (h : ℝ)
    (P : MvPolynomial (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ γ : PolynomialBox d ℓ, C (P.coeff (polynomialBoxExponent γ)) *
    ∏ i, (C (a i) + C h * X i) ^ (γ i).val
theorem affinePullbackPolynomial_eval  (a h)
    (P : MvPolynomial (Fin d) ℝ) (hP : P.totalDegree ≤ ℓ) (v ) :
    eval v (affinePullbackPolynomial ℓ a h P) = eval (fun i => a i + h * v i) P := by
  rw [polynomial_box_evaluation P hP]
  simp only [affinePullbackPolynomial, map_sum, map_mul, map_prod, map_pow, map_add,
    eval_C, eval_X]
theorem polynomial_centered_representation  (u : Covariate d)
    (P : MvPolynomial (Fin d) ℝ) (hP : P.totalDegree ≤ ℓ) (hu : eval u P = 0) :
    ∃ c : AnchoredIndex d ℓ → ℝ, ∀ z : Covariate d,
      eval z P = ∑ γ, c γ * anchoredFeature u z γ := by
  let Q := affinePullbackPolynomial ℓ u 1 P
  have h_affinePullbackPolynomial_degree : (affinePullbackPolynomial ℓ u 1 P).totalDegree ≤ ℓ := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro γ hγ
    by_cases hc : P.coeff (polynomialBoxExponent γ) = 0
    · simp [hc]
    have hs := (le_totalDegree (mem_support_iff.mpr hc)).trans hP
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hs
    simp only [polynomial_box_exponent_apply] at hs
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, zero_add]
    apply (MvPolynomial.totalDegree_finsetProd Finset.univ _).trans
    apply (Finset.sum_le_sum _).trans hs
    intro i hi
    have hl : (C (u i) + C 1 * X i).totalDegree ≤ 1 := by
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le (by simp)
      apply (MvPolynomial.totalDegree_mul _ _).trans
      simp
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left _ hl)
  have hQ  := h_affinePullbackPolynomial_degree
  have hQ0 : Q.coeff 0 = 0 := by
    rw [← constantCoeff_eq, ← eval_zero]
    have he := affinePullbackPolynomial_eval u 1 P hP 0
    simpa only [Pi.zero_apply, mul_zero, add_zero, hu, Q] using he
  refine ⟨fun γ => Q.coeff (anchoredExponent γ), ?_⟩
  intro z
  have he := affinePullbackPolynomial_eval u 1 P hP (z - u)
  have hz : (fun i => u i + 1 * (z - u) i) = z := by
    funext i
    simp
  rw [hz] at he
  have h_polynomial_as_anchored_sum : Q = anchoredPolynomial (fun γ : AnchoredIndex d ℓ => Q.coeff (anchoredExponent γ)) := by
    let pred : PolynomialBox d ℓ → Prop := fun γ =>
      0 < ∑ i, (γ i).val ∧ (∑ i, (γ i).val) ≤ ℓ
    let f : PolynomialBox d ℓ → MvPolynomial (Fin d) ℝ := fun γ =>
      monomial (polynomialBoxExponent γ) (Q.coeff (polynomialBoxExponent γ))
    have hz : ∀ γ, ¬ pred γ → f γ = 0 := by
      intro γ hγ
      have hn : Q.coeff (polynomialBoxExponent γ) = 0 := by
        by_contra hc
        have hs := (le_totalDegree (mem_support_iff.mpr hc)).trans hQ
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hs
        simp only [polynomial_box_exponent_apply] at hs
        have hpos : 0 < ∑ i, (γ i).val := by
          by_contra hnot
          have hs0 : (∑ i, (γ i).val) = 0 := by omega
          have he : polynomialBoxExponent γ = 0 := by
            ext i
            have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (γ j).val) (Finset.mem_univ i)
            rw [hs0] at hi
            simp only [polynomial_box_exponent_apply, Finsupp.zero_apply]
            omega
          rw [he, hQ0] at hc
          exact hc rfl
        exact hγ ⟨hpos, hs⟩
      simp only [f, hn, map_zero]
    have hsum := Fintype.sum_subtype_add_sum_subtype pred f
    have hc : (∑ γ : {γ : PolynomialBox d ℓ // ¬ pred γ}, f γ.val) = 0 := by
      apply Finset.sum_eq_zero
      intro γ hγ
      exact hz γ.val γ.property
    rw [hc, add_zero] at hsum
    calc
      Q = ∑ γ : PolynomialBox d ℓ,
          monomial (polynomialBoxExponent γ) (Q.coeff (polynomialBoxExponent γ)) :=
        polynomial_as_box_sum Q hQ
      _ = anchoredPolynomial (fun γ => Q.coeff (anchoredExponent γ)) := hsum.symm
  calc
    eval z P = eval (z - u) Q := he.symm
    _ = eval (z - u) (anchoredPolynomial (fun γ => Q.coeff (anchoredExponent γ))) :=
      congrArg (eval (z - u)) h_polynomial_as_anchored_sum
    _ = _ := anchoredPolynomial_eval _ (z - u)
def anchoredPopulationFit  (u : Covariate d) (p g : Covariate d → ℝ) :
    AnchoredIndex d ℓ → ℝ := (anchoredDensityGram u p)⁻¹ *ᵥ anchoredVectorMoment u p g
def anchoredFitPolynomial  (u : Covariate d) (c : AnchoredIndex d ℓ → ℝ) :
    Covariate d → ℝ := fun w => ∑ γ, c γ * anchoredFeature u w γ
theorem dyadicAnchoredFeature_transport_dot  (j x z c) :
    dyadicAnchoredFeature (j + 1) x z ⬝ᵥ (anchoredTransport d ℓ *ᵥ c) =
      dyadicAnchoredFeature j x z ⬝ᵥ c := by
  rw [Matrix.dotProduct_mulVec]
  have hT : (anchoredTransport d ℓ)ᵀ = anchoredTransport d ℓ := Matrix.diagonal_transpose _
  have h_dyadicAnchoredFeature_transport : anchoredTransport d ℓ *ᵥ dyadicAnchoredFeature (j + 1) x z =
      dyadicAnchoredFeature j x z := by
    ext γ
    rw [anchoredTransport, mulVec_diagonal, dyadicAnchoredFeature_scale, ← zpow_natCast 2 (anchoredDegree γ), ← mul_assoc,
      _root_.zpow_neg_mul_zpow_self (anchoredDegree γ ) (by norm_num)]
    simp
  rw [← hT, Matrix.vecMul_transpose, h_dyadicAnchoredFeature_transport]
def anchoredIncrement {d ℓ : ℕ} (a : ℕ → AnchoredIndex d ℓ → ℝ) :
    ℕ → AnchoredIndex d ℓ → ℝ
  | 0 => a 0
  | j + 1 => a (j + 1) - anchoredTransport d ℓ *ᵥ a j
theorem anchored_increment_telescope  (a : ℕ → AnchoredIndex d ℓ → ℝ)
    (x z : Covariate d) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), dyadicAnchoredFeature j x z ⬝ᵥ anchoredIncrement a j) =
      dyadicAnchoredFeature J x z ⬝ᵥ a J := by
  induction J with
  | zero => simp [anchoredIncrement]
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    change dyadicAnchoredFeature J x z ⬝ᵥ a J +
      dyadicAnchoredFeature (J + 1) x z ⬝ᵥ
        (a (J + 1) - anchoredTransport d ℓ *ᵥ a J) = _
    rw [dotProduct_sub, dyadicAnchoredFeature_transport_dot]
    ring
theorem anchoredVectorMoment_sub  (u p g h) (hpmeas : Measurable p) (b : ℝ)
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b)
    (hg : ContinuousOn g (unitCube d)) (hh : ContinuousOn h (unitCube d)) :
    anchoredVectorMoment (ℓ := ℓ) u p (g - h) =
      anchoredVectorMoment u p g - anchoredVectorMoment u p h := by
  have h_anchoredVectorMoment_integrable (g) (hpmeas : Measurable p) (b) (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) (hg : ContinuousOn g (unitCube d)) (γ : AnchoredIndex d ℓ) : Integrable (fun w => p w * anchoredFeature u w γ * g w) (cubeVolume d) := by
    have hc : ContinuousOn (fun w => anchoredFeature u w γ * g w) (unitCube d) :=
      (((anchoredMonomial_continuous γ).comp (continuous_id.sub continuous_const)).continuousOn).mul hg
    have hi := ContinuousOn.integrableOn_compact (μ := volume) (unitCube_isCompact d) hc
    have hpi := hi.bdd_mul hpmeas.aestronglyMeasurable
      (hp.mono (fun w hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2))
    convert hpi using 1
    · funext w; ring
    · rfl
  ext γ
  change (∫ w, p w * anchoredFeature u w γ * (g w - h w) ∂cubeVolume d) = _
  simp only [mul_sub]
  exact integral_sub (h_anchoredVectorMoment_integrable g hpmeas b hp hg γ)
    (h_anchoredVectorMoment_integrable h hpmeas b hp hh γ)
theorem anchoredPopulationFit_coefficient_error  [Nonempty (AnchoredIndex d ℓ)]
    (a b ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ D, 0 < D ∧ ∀ u ∈ unitCube d, ∀ p g,
      Measurable p → (∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) →
      ContinuousOn g (unitCube d) → ∀ c,
      ∀ R : ℝ, 0 ≤ R → (∀ w ∈ unitCube d, |g w - anchoredFitPolynomial u c w| ≤ R) →
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredPopulationFit u p g - c)‖ ≤ D * R := by
  have h_anchoredGram_uniform_bounds : ∃ cB CB : ℝ, 0 < cB ∧ 0 < CB ∧
      ∀ u ∈ unitCube d, ∀ c : AnchoredCoefficientSpace d ℓ,
        cB * ‖c‖ ^ 2 ≤ anchoredQuadratic u c ∧
        anchoredQuadratic u c ≤ CB * ‖c‖ ^ 2 := by
    classical
    let S : Set (Covariate d × AnchoredCoefficientSpace d ℓ) :=
      unitCube d ×ˢ Metric.sphere 0 1
    have hS : IsCompact S := (unitCube_isCompact d).prod (isCompact_sphere 0 1)
    let γ : AnchoredIndex d ℓ := Classical.choice inferInstance
    have hSne : S.Nonempty := by
      refine ⟨(0, EuclideanSpace.single γ 1), ?_, ?_⟩
      · intro i; simp
      · simp [Metric.mem_sphere, dist_eq_norm, EuclideanSpace.norm_single]
    obtain ⟨zmin, hzmin, hmin⟩ := hS.exists_isMinOn hSne anchoredQuadratic_continuous.continuousOn
    obtain ⟨zmax, hzmax, hmax⟩ := hS.exists_isMaxOn hSne anchoredQuadratic_continuous.continuousOn
    have hcB : 0 < anchoredQuadratic zmin.1 zmin.2 := anchoredQuadratic_pos _ _ (by intro he; have hh := hzmin.2; simp [Metric.mem_sphere, he] at hh)
    refine ⟨anchoredQuadratic zmin.1 zmin.2, max 1 (anchoredQuadratic zmax.1 zmax.2),
      hcB, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro u hu c
    by_cases hc : c = 0
    · subst c
      simp [anchoredQuadratic]
    have hn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    let c' : AnchoredCoefficientSpace d ℓ := ‖c‖⁻¹ • c
    have huc : (u, c') ∈ S := ⟨hu, by simpa [Metric.mem_sphere, dist_eq_norm] using (by simp [c', norm_smul, Real.norm_eq_abs, abs_of_pos hn, hn.ne', inv_mul_cancel₀])⟩
    have hup := (hmax huc).trans (le_max_right 1 _)
    have hrestore : ‖c‖ • c' = c := by
      dsimp [c']
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hscale : anchoredQuadratic u c = ‖c‖ ^ 2 * anchoredQuadratic u c' := by
      have h_anchoredQuadratic_smul : anchoredQuadratic u (‖c‖ • c') = ‖c‖ ^ 2 * anchoredQuadratic u c' := by
        change (∑ γ, (‖c‖ * c' γ) * ∑ δ, anchoredGram u γ δ * (‖c‖ * c' δ)) =
          ‖c‖ ^ 2 * ∑ γ, c' γ * ∑ δ, anchoredGram u γ δ * c' δ
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro γ hγ
        apply Finset.sum_congr rfl
        intro δ hδ
        ring
      calc
        anchoredQuadratic u c = anchoredQuadratic u (‖c‖ • c') := congrArg _ hrestore.symm
        _ = ‖c‖ ^ 2 * anchoredQuadratic u c' := h_anchoredQuadratic_smul
    rw [hscale]
    constructor
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hmin huc) (sq_nonneg ‖c‖)
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hup (sq_nonneg ‖c‖)
  obtain ⟨cB, CB, hcB, hCB, hGram⟩ := h_anchoredGram_uniform_bounds
  let D := max 1 (Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * b / (a * cB))
  refine ⟨D, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro u hu p g hpmeas hp hg c R hR hres
  have h_anchoredPopulationFit_error_equation : anchoredDensityGram u p *ᵥ (anchoredPopulationFit u p g - c) =
      anchoredVectorMoment u p (g - anchoredFitPolynomial u c) := by
    have h_anchoredFitPolynomial_continuous : Continuous (anchoredFitPolynomial u c) := by
      apply continuous_finsetSum
      intro γ _
      exact ((anchoredMonomial_continuous γ).comp (continuous_id.sub continuous_const)).const_mul _
    have h_anchoredPopulationFit_normal_equation : anchoredDensityGram (ℓ := ℓ) u p *ᵥ anchoredPopulationFit u p g =
      anchoredVectorMoment u p g := by
      have h_anchoredDensityGram_posDef : (anchoredDensityGram (ℓ := ℓ) u p).PosDef := by
        apply Matrix.PosDef.of_dotProduct_mulVec_pos (anchoredDensityGram_isHermitian u p)
        intro c hc
        simp only [star_trivial]
        exact (mul_pos ha (by simpa only [star_trivial] using (anchoredGram_posDef u).dotProduct_mulVec_pos hc)).trans_le
          (anchoredDensityGram_quadratic_bounds u p hpmeas a b ha.le hp c).1
      have hdet := (Matrix.isUnit_iff_isUnit_det _).mp
        h_anchoredDensityGram_posDef.isUnit
      rw [anchoredPopulationFit, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have h_anchoredVectorMoment_polynomial (c : AnchoredIndex d ℓ → ℝ) : anchoredVectorMoment u p (anchoredFitPolynomial u c) = anchoredDensityGram u p *ᵥ c := by
      have hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b := hp.mono (fun w hw => ⟨ha.le.trans hw.1, hw.2⟩)
      classical
      ext γ
      unfold anchoredVectorMoment anchoredFitPolynomial
      simp only [Finset.mul_sum]
      rw [integral_finsetSum]
      · change (∑ δ, ∫ w, p w * anchoredFeature u w γ * (c δ * anchoredFeature u w δ)
          ∂cubeVolume d) = ∑ δ, anchoredDensityGram u p γ δ * c δ
        apply Finset.sum_congr rfl
        intro δ _
        have he : (fun w => p w * anchoredFeature u w γ * (c δ * anchoredFeature u w δ)) =
            fun w => (p w * (anchoredFeature u w γ * anchoredFeature u w δ)) * c δ := by
          funext w; ring
        rw [he, integral_mul_const]
        rfl
      · intro δ _
        have he : (fun w => p w * anchoredFeature u w γ * (c δ * anchoredFeature u w δ)) =
            fun w => (p w * (anchoredFeature u w γ * anchoredFeature u w δ)) * c δ := by
          funext w; ring
        rw [he]
        exact (anchoredDensityGram_product_integrable u p hpmeas b hp γ δ).mul_const _
    rw [Matrix.mulVec_sub, h_anchoredPopulationFit_normal_equation,
      anchoredVectorMoment_sub u p g _ hpmeas b
        (hp.mono (fun w hw => ⟨ha.le.trans hw.1, hw.2⟩)) hg
        h_anchoredFitPolynomial_continuous.continuousOn,
      h_anchoredVectorMoment_polynomial]
  have h_anchoredDensityGram_solve_norm_bound (hB : ∀ c : AnchoredCoefficientSpace d ℓ, cB * ‖c‖ ^ 2 ≤ anchoredQuadratic u c) (e) (r) (her : anchoredDensityGram u p *ᵥ e = r) : ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm e‖ ≤
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm r‖ / (a * cB) := by
    let E := (EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm e
    let R := (EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm r
    have hq := (anchoredDensityGram_quadratic_bounds u p hpmeas a b ha.le hp e).1
    have hb := hB E
    have : e ⬝ᵥ r ≤ ‖E‖ * ‖R‖ := by
      simpa [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm, E, R,
        EuclideanSpace.equiv]
        using real_inner_le_norm E R
    have : a * cB * ‖E‖ ^ 2 ≤ e ⬝ᵥ r := by
      calc
        a * cB * ‖E‖ ^ 2 = a * (cB * ‖E‖ ^ 2) := by ring
        _ ≤ a * anchoredQuadratic u E := mul_le_mul_of_nonneg_left hb ha.le
        _ ≤ e ⬝ᵥ r := by simpa [anchoredQuadratic, her, E, EuclideanSpace.equiv] using hq
    by_cases he : ‖E‖ = 0
    · rw [he]; positivity
    · have  := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
      apply (le_div_iff₀ (mul_pos ha hcB)).2
      nlinarith
  have hr := anchoredVectorMoment_norm_bound (ℓ := ℓ) u hu p (g - anchoredFitPolynomial u c)
    b R hb hR (hp.mono (fun w hw => ⟨ha.le.trans hw.1, hw.2⟩)) hres
  apply (h_anchoredDensityGram_solve_norm_bound (fun v => (hGram u hu v).1) _ _ (h_anchoredPopulationFit_error_equation)).trans
  calc
    _ ≤ (Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (b * R)) / (a * cB) :=
      div_le_div_of_nonneg_right hr (mul_pos ha hcB).le
    _ = (Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * b / (a * cB)) * R := by ring
    _ ≤ D * R := mul_le_mul_of_nonneg_right (le_max_right _ _) hR
theorem anchoredFitPolynomial_sub  (u w : Covariate d)
    (c e : AnchoredIndex d ℓ → ℝ) :
    anchoredFitPolynomial u (c - e) w = anchoredFitPolynomial u c w - anchoredFitPolynomial u e w := by
  simp only [anchoredFitPolynomial, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
theorem anchoredPopulationFit_pointwise_error  [Nonempty (AnchoredIndex d ℓ)]
    (a b ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ D, 0 < D ∧ ∀ u ∈ unitCube d, ∀ p g,
      Measurable p → (∀ᵐ v ∂cubeVolume d, a ≤ p v ∧ p v ≤ b) →
      ContinuousOn g (unitCube d) → ∀ c : AnchoredIndex d ℓ → ℝ,
      ∀ R : ℝ, 0 ≤ R → (∀ v ∈ unitCube d, |g v - anchoredFitPolynomial u c v| ≤ R) →
      ∀ w ∈ unitCube d,
      |g w - anchoredFitPolynomial u (anchoredPopulationFit (ℓ := ℓ) u p g) w| ≤
        |g w - anchoredFitPolynomial u c w| + D * R * euclideanNorm (w - u) := by
  obtain ⟨D, hD, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := ℓ) a b ha hb
  let E := max 1 ((Fintype.card (AnchoredIndex d ℓ) : ℝ) * D)
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro u hu p g hpmeas hp hg c R hR hres w hw
  have := hfit u hu p g hpmeas hp hg c R hR hres
  have h_anchoredFitPolynomial_abs_le_distance (c) : |anchoredFitPolynomial u c w| ≤ (Fintype.card (AnchoredIndex d ℓ) : ℝ) *
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ * euclideanNorm (w - u) := by
    calc
      _ ≤ ∑ γ, |c γ * anchoredFeature u w γ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _γ : AnchoredIndex d ℓ,
          ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ * euclideanNorm (w - u) := by
        apply Finset.sum_le_sum
        intro γ _
        rw [abs_mul]
        apply mul_le_mul _ (by apply anchoredMonomial_abs_le_euclideanNorm; intro i; change |w i - u i| ≤ 1; rw [abs_le]; constructor <;> linarith [(hu i).1, (hu i).2, (hw i).1, (hw i).2])
          (abs_nonneg _) (norm_nonneg _)
        simpa [Real.norm_eq_abs, EuclideanSpace.equiv] using
          PiLp.norm_apply_le ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c) γ
      _ = _ := by simp; ring
  have hpoly := h_anchoredFitPolynomial_abs_le_distance (anchoredPopulationFit u p g - c)
  have hnonneg : 0 ≤ euclideanNorm (w - u) := by unfold euclideanNorm; positivity
  have habs : |anchoredFitPolynomial u (anchoredPopulationFit u p g - c) w| ≤
      E * R * euclideanNorm (w - u) := by
    apply hpoly.trans
    calc
      _ ≤ (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (D * R) * euclideanNorm (w - u) := by
        gcongr
      _ = ((Fintype.card (AnchoredIndex d ℓ) : ℝ) * D) * R * euclideanNorm (w - u) := by ring
      _ ≤ E * R * euclideanNorm (w - u) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hR) hnonneg
  have heq : g w - anchoredFitPolynomial u (anchoredPopulationFit (ℓ := ℓ) u p g) w =
      g w - anchoredFitPolynomial u c w -
        anchoredFitPolynomial u (anchoredPopulationFit u p g - c) w := by
    rw [anchoredFitPolynomial_sub]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add le_rfl habs)
def dyadicRegressionDifference  (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : Covariate d → ℝ :=
  fun w => θ.regression (dyadicCellAffine j x w) - θ.regression x
def dyadicPopulationFit  (θ : RegressionParameter d) (j : ℕ)
    (x : Covariate d) : AnchoredIndex d ℓ → ℝ :=
  (dyadicPopulationGram θ j x)⁻¹ *ᵥ
    (dyadicResponseMoment θ j x - θ.regression x • dyadicConstantMoment θ j x)
theorem dyadicCellAffine_continuous  (j : ℕ) (x : Covariate d) :
    Continuous (dyadicCellAffine j x) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_const.mul (continuous_apply i))
theorem dyadicCellAffine_mem_cube  (j x w)
    (hw : w ∈ unitCube d) : dyadicCellAffine j x w ∈ unitCube d := by
  apply gridClosedBox_subset_cube (2 ^ j) (by positivity) (regularGridCell _ (by positivity) x)
  change w ∈ gridAffine _ _ ⁻¹' gridClosedBox _ _
  rwa [gridAffine_preimage_box _ (by positivity) _]
theorem dyadicCellAffine_difference  (j : ℕ) (x w : Covariate d) :
    dyadicCellAffine j x w - x = ((2 : ℝ) ^ j)⁻¹ • (w - dyadicNormalizedAnchor j x) := by
  funext i
  simp only [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  ring
theorem admissible_regression_continuousOn_cube  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    ContinuousOn θ.regression (unitCube d) := by
  obtain ⟨F, hF, hreg, hNorm⟩ := hθ.2.2.2.2.1
  exact (hreg.continuousOn.mono C.cube_subset).congr (fun x hx => (hF x hx).symm)
theorem dyadicRegressionDifference_continuousOn  (C θ) (hθ : Admissible C θ) (j ) (x : Covariate d) :
    ContinuousOn (dyadicRegressionDifference θ j x) (unitCube d) := by
  exact ((admissible_regression_continuousOn_cube C θ hθ).comp
    (dyadicCellAffine_continuous j x).continuousOn (dyadicCellAffine_mem_cube j x)).sub continuousOn_const
theorem dyadicPopulationFit_eq_normalized  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j ) (x : Covariate d) :
    dyadicPopulationFit (ℓ := ℓ) θ j x = anchoredPopulationFit (dyadicNormalizedAnchor j x)
      (dyadicNormalizedDensity θ j x) (dyadicRegressionDifference θ j x) := by
  unfold dyadicPopulationFit anchoredPopulationFit
  rw [dyadicPopulationGram_eq_normalized C θ hθ,
    dyadicResponseMoment_eq_normalized C θ hθ, dyadicConstantMoment_eq_normalized C θ hθ]
  congr 1
  have hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ dyadicNormalizedDensity θ j x w ∧
      dyadicNormalizedDensity θ j x w ≤ C.densityUpper := (dyadicNormalizedDensity_bounds C θ hθ j x).mono
    (fun w hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩)
  have hc : ContinuousOn (θ.regression ∘ dyadicCellAffine j x) (unitCube d) :=
    (admissible_regression_continuousOn_cube C θ hθ).comp
      (dyadicCellAffine_continuous j x).continuousOn (dyadicCellAffine_mem_cube j x)
  rw [show dyadicRegressionDifference θ j x =
    θ.regression ∘ dyadicCellAffine j x - (fun _ => θ.regression x) by rfl,
    anchoredVectorMoment_sub _ _ _ _ (dyadicNormalizedDensity_measurable C θ hθ j x)
      C.densityUpper hp hc continuousOn_const]
  congr 1
  ext γ
  change θ.regression x * (∫ w, dyadicNormalizedDensity θ j x w *
    anchoredFeature (dyadicNormalizedAnchor j x) w γ * 1 ∂cubeVolume d) =
      ∫ w, dyadicNormalizedDensity θ j x w *
        anchoredFeature (dyadicNormalizedAnchor j x) w γ * θ.regression x ∂cubeVolume d
  rw [integral_mul_const]
  simp only [mul_one]
  rw [integral_mul_const]
  ring
def dyadicTaylorCoefficients  (c : AnchoredIndex d ℓ → ℝ) (j : ℕ) :
    AnchoredIndex d ℓ → ℝ := (anchoredTransport d ℓ) ^ j *ᵥ c
theorem dyadicTaylorCoefficients_succ  (c j) :
    dyadicTaylorCoefficients c (j + 1) = anchoredTransport d ℓ *ᵥ dyadicTaylorCoefficients c j := by
  rw [dyadicTaylorCoefficients, pow_succ', ← Matrix.mulVec_mulVec]
  rfl
theorem dyadicTaylorCoefficients_normalized_evaluation 
    (c : AnchoredIndex d ℓ → ℝ) (j : ℕ) (x w : Covariate d) :
    anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w =
      anchoredFitPolynomial x c (dyadicCellAffine j x w) := by
  have h_dyadicTaylorCoefficients_evaluation (z : Covariate d) : dyadicAnchoredFeature j x z ⬝ᵥ dyadicTaylorCoefficients c j = anchoredFitPolynomial x c z := by
    induction j with
    | zero =>
      simp only [dyadicTaylorCoefficients, pow_zero, Matrix.one_mulVec, dyadicAnchoredFeature,
        one_mul, anchoredFeature, anchoredFitPolynomial, dotProduct]
      apply Finset.sum_congr rfl
      intro γ _
      rw [show (fun i => z i - x i) = z - x by rfl]
      ring
    | succ j ih =>
      rw [dyadicTaylorCoefficients_succ, dyadicAnchoredFeature_transport_dot, ih]
  have he := h_dyadicTaylorCoefficients_evaluation (dyadicCellAffine j x w)
  have hφ : dyadicAnchoredFeature (ℓ := ℓ) j x (dyadicCellAffine j x w) =
      anchoredFeature (dyadicNormalizedAnchor j x) w := by
    funext γ
    exact dyadicAnchoredFeature_affine j x w γ
  rw [hφ] at he
  calc
    _ = anchoredFeature (dyadicNormalizedAnchor j x) w ⬝ᵥ dyadicTaylorCoefficients c j := by
      apply Finset.sum_congr rfl
      intro γ _
      ring
    _ = _ := he
theorem euclideanNorm_smul  (a : ℝ) (v : Covariate d) :
    euclideanNorm (a • v) = |a| * euclideanNorm v := by
  unfold euclideanNorm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]
theorem dyadicCellAffine_euclidean_distance  (j : ℕ) (x w : Covariate d) :
    euclideanNorm (dyadicCellAffine j x w - x) =
      (↑2 ^ j)⁻¹ * euclideanNorm (w - dyadicNormalizedAnchor j x) := by
  rw [dyadicCellAffine_difference, euclideanNorm_smul, abs_of_nonneg (by positivity)]
theorem admissible_dyadic_taylor_family  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (x )
    (hx : x ∈ unitCube d) :
    ∃ c : AnchoredIndex d C.order → ℝ, ∀ j : ℕ, ∀ w ∈ unitCube d,
      |dyadicRegressionDifference θ j x w -
        anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w| ≤
          taylorErrorFactor C * C.holderBound * ((↑2 ^ j)⁻¹) ^ C.smoothness ∧
      |dyadicRegressionDifference θ j x w -
        anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w| ≤
          (↑d ^ C.order * 2 * C.holderBound / C.order.factorial) *
            ((↑2 ^ j)⁻¹) ^ C.smoothness *
              euclideanNorm (w - dyadicNormalizedAnchor j x) ^ C.smoothness := by
  have h_admissible_regression_taylor : ∃ P : MvPolynomial (Fin d) ℝ, P.totalDegree ≤ C.order ∧
      ∀ y ∈ unitCube d, |θ.regression y - MvPolynomial.eval y P| ≤
        (d ^ C.order * (2 * C.holderBound) / C.order.factorial) *
          euclideanNorm (y - x) ^ C.smoothness := by
    rcases hθ with ⟨_, _, _, _, ⟨F, hcube, hreg, hNorm⟩, _, _, _⟩
    refine ⟨modelTaylorPolynomial C F x, modelTaylorPolynomial_degree C F x, ?_⟩
    intro y hy
    have h_modelTaylorPolynomial_error  := modelTaylorPolynomial_error_of_holderBall C F
      (euclideanExtension_mem_holderBall C F hreg hNorm) x y hx hy
    simpa only [hcube y hy] using h_modelTaylorPolynomial_error
  obtain ⟨P, hP, herr⟩ := h_admissible_regression_taylor
  have hxP : eval x P = θ.regression x := by
    have h := herr x hx
    simp [euclideanNorm, Real.zero_rpow C.smoothness_pos.ne'] at h
    exact (sub_eq_zero.mp h).symm
  have hzero : eval x (P - MvPolynomial.C (θ.regression x)) = 0 := by
    rw [map_sub, eval_C, hxP, sub_self]
  obtain ⟨c, hc⟩ := polynomial_centered_representation x _ ((MvPolynomial.totalDegree_sub _ _).trans (max_le hP (by simp))) hzero
  refine ⟨c, ?_⟩
  intro j w hw
  have heq : dyadicRegressionDifference θ j x w -
      anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w =
        θ.regression (dyadicCellAffine j x w) - eval (dyadicCellAffine j x w) P := by
    rw [dyadicTaylorCoefficients_normalized_evaluation,
      show anchoredFitPolynomial x c (dyadicCellAffine j x w) =
        eval (dyadicCellAffine j x w) (P - MvPolynomial.C (θ.regression x)) from (hc _).symm,
      map_sub, eval_C]
    unfold dyadicRegressionDifference
    ring
  rw [heq]
  have hy := dyadicCellAffine_mem_cube j x w hw
  have hcoef : 0 ≤ d ^ C.order * (2 * C.holderBound) / C.order.factorial :=
    div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _)
      (mul_nonneg (by norm_num) C.holderBound_pos.le)) (Nat.cast_nonneg _)
  constructor
  have h_dyadicCellAffine_radius (i : Fin d) : |dyadicCellAffine j x w i - x i| ≤ (2 ^ j)⁻¹ := by
    have hu : dyadicNormalizedAnchor j x ∈ unitCube d :=
      gridNormalizedAnchor_mem_cube (2 ^ j) (by positivity) x hx
    have he := congrFun (dyadicCellAffine_difference j x w) i
    change dyadicCellAffine j x w i - x i = (2 ^ j)⁻¹ *
      (w i - dyadicNormalizedAnchor j x i) at he
    rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((2 : ℝ) ^ j)⁻¹)]
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [(hw i).1, (hu i).2], by linarith [(hw i).2, (hu i).1]⟩) (by positivity)).trans_eq (mul_one _)
  · have hdist := euclideanNorm_le_coordinate_radius (dyadicCellAffine j x w - x)
      ((↑2 ^ j)⁻¹) (by positivity) h_dyadicCellAffine_radius
    apply (herr _ hy).trans
    apply (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by unfold euclideanNorm; positivity) hdist C.smoothness_pos.le) hcoef).trans_eq
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (by positivity)]
    unfold taylorErrorFactor
    ring
  · convert herr _ hy using 1
    rw [dyadicCellAffine_euclidean_distance, Real.mul_rpow (by positivity)
      (by unfold euclideanNorm; positivity)]
    ring
end NearlyMinimax
end
set_option backward.isDefEq.respectTransparency false
namespace NearlyMinimax
open MeasureTheory Set ProbabilityTheory Matrix
open scoped ENNReal BigOperators Matrix.Norms.L2Operator
section
open Matrix MeasureTheory ProbabilityTheory MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
def rowFunctional  (row : Fin r → ℝ) : (Fin r → ℝ) →L[ℝ] ℝ :=
  ∑ i, row i • (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ)
@[simp] theorem rowFunctional_apply {r : ℕ} (row z : Fin r → ℝ) :
    rowFunctional row z = row ⬝ᵥ z := by
  simp [rowFunctional, dotProduct, smul_eq_mul]
theorem rowFunctional_norm_le {r : ℕ} (row : Fin r → ℝ) :
    ‖rowFunctional row‖ ≤ ∑ i, |row i| := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  intro z
  rw [rowFunctional_apply, dotProduct]
  calc
    ‖∑ i, row i * z i‖ ≤ ∑ i, ‖row i * z i‖ := norm_sum_le _ _
    _ ≤ ∑ i, |row i| * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (abs_nonneg _)
    _ = (∑ i, |row i|) * ‖z‖ := by rw [Finset.sum_mul]
def incrementFinScalar (r ) (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (row : Fin r → ℝ) :
    (Fin (Fintype.card (incrementVariables r)) → ℝ) → ℝ :=
  fun x => row ⬝ᵥ incrementFinVector r lo hi T y m x
theorem incrementFinScalar_iteratedFDeriv (r ) [NeZero r] (lo hi T y m k row x)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    iteratedFDeriv ℝ k (incrementFinScalar r lo hi T y m row) x v =
      rowFunctional row (iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m) x v) := by
  have h := (rowFunctional row).iteratedFDeriv_comp_left (x := x)
    (incrementFinVector_contDiff r lo hi T y m).contDiffAt (show (k : WithTop ℕ∞) ≤ ⊤ from le_top)
  have hFun : (rowFunctional row) ∘ incrementFinVector r lo hi T y m =
      incrementFinScalar r lo hi T y m row := by
    funext z
    exact rowFunctional_apply row _
  rw [hFun] at h
  have he := congrArg (fun D => D v) h
  change iteratedFDeriv ℝ k (incrementFinScalar r lo hi T y m row) x v =
    rowFunctional row (iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m) x v) at he
  exact he
theorem anchored_actual_population_row_derivative_operator_bound 
    [Nonempty (AnchoredIndex d ℓ)] (a b F Y )
    (ha : 0 < a) (hab : a < b) (hF : 0 ≤ F) (hY : 0 ≤ Y) :
    ∃ C A, 0 < C ∧ 0 < A ∧
      ∀ u v, u ∈ unitCube d → v ∈ unitCube d →
      ∀ p q f g, Measurable p → Measurable q →
      (∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) →
      (∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b) →
      (∀ w ∈ unitCube d, |f w| ≤ F) → (∀ w ∈ unitCube d, |g w| ≤ F) →
      ∀ y, |y| ≤ Y → ∀ m k row,
        ‖iteratedFDeriv ℝ k
          (incrementFinScalar (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) y m row)
          (fun j => incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q)
            (anchoredFinMomentFamilies u p f) (anchoredFinMomentFamilies v q g)
            ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm j))‖ ≤
          (∑ i, |row i|) * C * k.factorial * A ^ k := by
  have h_anchored_actual_population_inverse_derivatives : ∃ C A, 0 < C ∧ 0 < A ∧
      ∀ u v, u ∈ unitCube d → v ∈ unitCube d →
      ∀ p q f g, Measurable p → Measurable q →
      (∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) →
      (∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b) →
      (∀ w ∈ unitCube d, |f w| ≤ F) →
      (∀ w ∈ unitCube d, |g w| ≤ F) →
      ∀ y, |y| ≤ Y → ∀ m k directions,
        ‖iteratedFDeriv ℝ k
          (incrementFinVector (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) y m)
          (fun j => incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q)
            (anchoredFinMomentFamilies u p f) (anchoredFinMomentFamilies v q g)
            ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm j)) directions‖ ≤
          C * k.factorial * A ^ k * ∏ j, ‖directions j‖ := by
    obtain ⟨W, hW, hmom⟩ := anchoredFinMomentFamilies_uniform_bound (d := d) (ℓ := ℓ) b F ((ha.trans hab).le) hF
    obtain ⟨C, A, hC, hA, hder⟩ := anchored_population_inverse_derivatives
      (d := d) (ℓ := ℓ) a b W Y ha hab hW.le hY
    refine ⟨C, A, hC, hA, ?_⟩
    intro u v hu hv p q f g hpmeas hqmeas hp hq hf hg y hy m k directions
    exact hder u v hu hv p q hpmeas hqmeas hp hq
      (anchoredFinMomentFamilies u p f) (anchoredFinMomentFamilies v q g)
      (hmom u hu p f (hp.mono (fun w hw => ⟨ha.le.trans hw.1, hw.2⟩)) hf)
      (hmom v hv q g (hq.mono (fun w hw => ⟨ha.le.trans hw.1, hw.2⟩)) hg)
      y hy m k directions
  obtain ⟨C, A, hC, hA, hDer⟩ := h_anchored_actual_population_inverse_derivatives
  refine ⟨C, A, hC, hA, ?_⟩
  intro u v hu hv p q f g hpmeas hqmeas hp hq hf hg y hy m k row
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro directions
  rw [incrementFinScalar_iteratedFDeriv]
  calc
    _ ≤ ‖rowFunctional row‖ * ‖iteratedFDeriv ℝ k
        (incrementFinVector (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) y m)
        (fun j => incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q)
          (anchoredFinMomentFamilies u p f) (anchoredFinMomentFamilies v q g)
          ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm j)) directions‖ :=
      (rowFunctional row).le_opNorm _
    _ ≤ (∑ i, |row i|) * (C * ↑k.factorial * A ^ k * ∏ j, ‖directions j‖) := by
      apply mul_le_mul (rowFunctional_norm_le row)
        (hDer u v hu hv p q f g hpmeas hqmeas hp hq hf hg y hy m k directions)
        (norm_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    _ = (∑ i, |row i|) * C * k.factorial * A ^ k * ∏ j, ‖directions j‖ := by ring
theorem dyadicFinPilotMoments_eq_anchored  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j x)
    (hx : x ∈ unitCube d) :
    dyadicFinPilotMoments (ℓ := ℓ) θ j x = anchoredFinMomentFamilies
      (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
      (θ.regression ∘ dyadicCellAffine j x) := by
  funext t i
  cases t
  have h_preconditionedPilotPopulation_response (γ : AnchoredIndex d ℓ) : preconditionedPilotPopulation θ j x (Sum.inr (Sum.inl γ)) =
      anchoredPreconditionedMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
        (θ.regression ∘ dyadicCellAffine j x) γ := by
    rw [preconditionedPilotPopulation_eq_sum C θ hθ j x hx]
    simp only [localPilotRow, localPilotReplaceRow, dyadicPilotPopulation_response C θ hθ j x hx,
      dyadicKnownGram_eq_normalized, anchoredPreconditionedMoment, Matrix.mulVec, dotProduct,
      dyadicResponseMoment_eq_normalized C θ hθ]
  · exact h_preconditionedPilotPopulation_response _
  have h_preconditionedPilotPopulation_constant (γ : AnchoredIndex d ℓ) : preconditionedPilotPopulation θ j x (Sum.inr (Sum.inr γ)) =
      anchoredPreconditionedMoment (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
        (fun _ => 1) γ := by
    rw [preconditionedPilotPopulation_eq_sum C θ hθ j x hx]
    simp only [localPilotRow, localPilotReplaceRow, dyadicPilotPopulation_constant C θ hθ,
      dyadicKnownGram_eq_normalized, anchoredPreconditionedMoment, Matrix.mulVec, dotProduct,
      dyadicConstantMoment_eq_normalized C θ hθ]
  · exact h_preconditionedPilotPopulation_constant _
theorem dyadicIncrementRawMean_eq_normalized  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j ) (hj : j ≠ 0)
    (x ) (hx : x ∈ unitCube d) :
    dyadicIncrementRawMean (ℓ := ℓ) θ j x = fun a =>
      incrementValuation
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x))
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor (j - 1) x) (dyadicNormalizedDensity θ (j - 1) x))
        (anchoredFinMomentFamilies (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x)
          (θ.regression ∘ dyadicCellAffine j x))
        (anchoredFinMomentFamilies (dyadicNormalizedAnchor (j - 1) x) (dyadicNormalizedDensity θ (j - 1) x)
          (θ.regression ∘ dyadicCellAffine (j - 1) x))
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) := by
  rw [dyadicIncrementRawMean_eq_population C θ hθ j x hx]
  simp only [dyadicIncrementPopulation, if_neg hj,
    dyadicFinPilotGram_eq_normalized C θ hθ,
    dyadicFinPilotMoments_eq_anchored C θ hθ j x hx,
    dyadicFinPilotMoments_eq_anchored C θ hθ (j - 1) x hx]
def rowIncrementPolynomial (r ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (row : Fin r → ℝ) :
    MvPolynomial (Fin (Fintype.card (incrementVariables r))) ℝ :=
  ∑ i, C (row i) * incrementFinPolynomial r a b T y m i
theorem rowIncrementPolynomial_eval (r a b T y m row z) :
    eval z (rowIncrementPolynomial r a b T y m row) = incrementFinScalar r a b T y m row z := by
  simp [rowIncrementPolynomial, incrementFinScalar, incrementFinVector, dotProduct]
theorem rowIncrementPolynomial_degree (r ) [NeZero r] (a b T y m row) :
    (rowIncrementPolynomial r a b T y m row).totalDegree ≤ m + r + 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply (totalDegree_mul _ _).trans
  have h_incrementEntryPolynomial_degree : (incrementEntryPolynomial r a b T y m i).totalDegree ≤ m + r + 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j hj
    apply (MvPolynomial.totalDegree_mul _ _).trans
    exact (Nat.add_le_add ((MvPolynomial.totalDegree_rename_le _ _).trans
      (parentInverseEntryPolynomial_degree a b r m i j))
      (by unfold numeratorPolynomial; apply (MvPolynomial.totalDegree_sub _ _).trans; apply max_le (rawNumeratorPolynomial_degree r T false j); apply (MvPolynomial.totalDegree_mul _ _).trans; simpa using rawNumeratorPolynomial_degree r T true j)).trans_eq (by omega)
  simpa only [totalDegree_C, zero_add, incrementFinPolynomial] using
    (totalDegree_rename_le _ _).trans h_incrementEntryPolynomial_degree
theorem anchoredFinNormalizedGram_one {d ℓ : ℕ} (u : Covariate d) :
    anchoredFinNormalizedGram (ℓ := ℓ) u (fun _ => 1) = 1 := by
  have hG : anchoredDensityGram (ℓ := ℓ) u (fun _ => 1) = anchoredGram u := by
    ext γ δ
    simp [anchoredDensityGram, anchoredGram]
  unfold anchoredFinNormalizedGram
  rw [hG, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_posDef u).isUnit)]
  exact map_one _
theorem dyadicIncrementRawMean_root_eq_normalized  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (x : Covariate d) (hx : x ∈ unitCube d) :
    dyadicIncrementRawMean (ℓ := ℓ) θ 0 x = fun a =>
      incrementValuation
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor 0 x) (dyadicNormalizedDensity θ 0 x))
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor 0 x) (fun _ => 1))
        (anchoredFinMomentFamilies (dyadicNormalizedAnchor 0 x) (dyadicNormalizedDensity θ 0 x)
          (θ.regression ∘ dyadicCellAffine 0 x)) 0
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) := by
  rw [dyadicIncrementRawMean_eq_population C θ hθ 0 x hx]
  simp only [dyadicIncrementPopulation, ite_true, anchoredFinNormalizedGram_one,
    dyadicFinPilotGram_eq_normalized C θ hθ, dyadicFinPilotMoments_eq_anchored C θ hθ 0 x hx]
def dyadicPolynomialPilot  (C : ModelConstants d) (n j : ℕ) (x : Covariate d)
    (y : ℝ) (m : ℕ) (row : Fin (anchoredDimension d C.order) → ℝ)
    (z : Fin n → Observation d) : ℝ :=
  RoughRegime.Upper.polynomialLift
    (rowIncrementPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
      (anchoredFinTransport d C.order) y m row)
    (fun i z => dyadicIncrementRawVector j x (z i)) z
theorem dyadicPolynomialPilot_moment_facts  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (n j x) (hx : x ∈ unitCube d) (y m row)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (dyadicPolynomialPilot C n j x y m row) 2 (sampleLaw θ n) ∧
    (∫ z, dyadicPolynomialPilot C n j x y m row z ∂sampleLaw θ n) =
      incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
        (anchoredFinTransport d C.order) y m row (dyadicIncrementRawMean θ j x) := by
  let := sampleLaw_isProbability C θ hθ n
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := dyadicIncrementRawVector_sample_facts C θ hθ j x hx
  refine ⟨LiftL2.polynomialLift_memLp_two_l2 _ _ (dyadicIncrementRawMean θ j x)
    (rowIncrementPolynomial_degree _ _ _ _ _ _ _) hdegree hind hmeas hL2, ?_⟩
  rw [← rowIncrementPolynomial_eval]
  exact LiftL2.polynomialLift_expectation_l2 _ _ (dyadicIncrementRawMean θ j x)
    (rowIncrementPolynomial_degree _ _ _ _ _ _ _) hdegree hind hmeas hid hL2 hmean
end
theorem partitionPairMeasure_fst_le 
    [MeasurableSpace X] [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] [MeasurableEq I]
    (μ : Measure X) [IsProbabilityMeasure μ] (label : X → I) (hlabel : Measurable label)
    {weight cap : ℝ} (hw : 0 ≤ weight) (hcap : 0 ≤ cap)
    (hmass : ∀ i, μ.real (label ⁻¹' {i}) ≤ cap) :
    (partitionPairMeasure μ label weight).map Prod.fst ≤ ENNReal.ofReal (weight * cap) • μ := by
  apply Measure.le_iff.2
  intro A hA
  have hC : MeasurableSet {z : X × X | label z.1 = label z.2} :=
    measurableSet_eq_fun (hlabel.comp measurable_fst) (hlabel.comp measurable_snd)
  rw [Measure.map_apply measurable_fst hA, partitionPairMeasure,
    Measure.smul_apply, Measure.restrict_apply (measurable_fst hA),
    Measure.prod_apply ((measurable_fst hA).inter hC), Measure.smul_apply,
    ENNReal.ofReal_mul hw]
  change ENNReal.ofReal weight *
    (∫⁻ x, μ (Prod.mk x ⁻¹' (Prod.fst ⁻¹' A ∩ {z : X × X | label z.1 = label z.2})) ∂μ) ≤
      ENNReal.ofReal weight * ENNReal.ofReal cap * μ A
  have : (∫⁻ x, μ (Prod.mk x ⁻¹'
      (Prod.fst ⁻¹' A ∩ {z : X × X | label z.1 = label z.2})) ∂μ) ≤
      ENNReal.ofReal cap * μ A := by
    calc
      _ ≤ ∫⁻ x, A.indicator (fun _ => ENNReal.ofReal cap) x ∂μ := by
        apply lintegral_mono
        intro x
        change μ (Prod.mk x ⁻¹' (Prod.fst ⁻¹' A ∩ {z : X × X | label z.1 = label z.2})) ≤ _
        by_cases hx : x ∈ A
        · have he : Prod.mk x ⁻¹'
              (Prod.fst ⁻¹' A ∩ {z : X × X | label z.1 = label z.2}) =
              label ⁻¹' {label x} := by
            ext y
            simp [hx, eq_comm]
          rw [he, Set.indicator_of_mem hx]
          simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)] using (ENNReal.ofReal_le_ofReal (hmass (label x)))
        · have he : Prod.mk x ⁻¹'
              (Prod.fst ⁻¹' A ∩ {z : X × X | label z.1 = label z.2}) = ∅ := by
            ext y
            simp [hx]
          rw [he, measure_empty, Set.indicator_of_notMem hx]
      _ = _ := lintegral_indicator_const hA _
  calc
    _ ≤ ENNReal.ofReal weight * (ENNReal.ofReal cap * μ A) := by gcongr
    _ = _ := (mul_assoc _ _ _).symm
theorem preconditionedPilotFeature_zero_off_cell {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) (hz : z.1 ∉ dyadicPilotCell j x) :
    preconditionedPilotFeature j x a z = 0 := by
  simp [preconditionedPilotFeature, dyadicPilotFeature, hz]
theorem dyadicIncrementRawVector_zero_off_parent {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (z : Observation d) (hz : z.1 ∉ dyadicPilotCell (j - 1) x) :
    dyadicIncrementRawVector (ℓ := ℓ) j x z = 0 := by
  have hj : j ≠ 0 := by
    intro h
    subst j
    apply hz
    change regularGridCell 1 (by positivity) z.1 = regularGridCell 1 (by positivity) x
    exact Subsingleton.elim _ _
  have hcur : z.1 ∉ dyadicPilotCell j x := fun h => hz (dyadicPilotCell_subset_parent j x h)
  funext a
  change dyadicIncrementFeature j x
    ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) z = 0
  generalize (Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a = v
  cases v with
  | inl v =>
    cases v with
    | inl v =>
      rcases v with ⟨i, t⟩
      exact preconditionedPilotFeature_zero_off_cell j x _ z hcur
    | inr v =>
      simpa only [dyadicIncrementFeature, if_neg hj] using
        preconditionedPilotFeature_zero_off_cell (j - 1) x
          (Sum.inl (anchoredFinIndex v.2.1, anchoredFinIndex v.2.2)) z hz
  | inr v =>
    rcases v with ⟨parent, response, i⟩
    cases parent <;> cases response
    all_goals first
      | simpa [dyadicIncrementFeature, hj] using
          preconditionedPilotFeature_zero_off_cell j x (Sum.inr (Sum.inl (anchoredFinIndex i))) z hcur
      | simpa [dyadicIncrementFeature, hj] using
          preconditionedPilotFeature_zero_off_cell j x (Sum.inr (Sum.inr (anchoredFinIndex i))) z hcur
      | simpa [dyadicIncrementFeature, hj] using
          preconditionedPilotFeature_zero_off_cell (j - 1) x (Sum.inr (Sum.inl (anchoredFinIndex i))) z hz
      | simpa [dyadicIncrementFeature, hj] using
          preconditionedPilotFeature_zero_off_cell (j - 1) x (Sum.inr (Sum.inr (anchoredFinIndex i))) z hz
theorem dyadic_increment_raw_kernel_zero_off_parent {d ℓ k : ℕ} (j x)
    (H : ContinuousMultilinearMap ℝ
      (fun _ : Fin k => Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) ℝ)
    (z : Fin k → Observation d) (i : Fin k) (hz : (z i).1 ∉ dyadicPilotCell (j - 1) x) :
    H (fun t => dyadicIncrementRawVector j x (z t)) = 0 :=
  H.map_coord_zero i (dyadicIncrementRawVector_zero_off_parent j x (z i) hz)
end NearlyMinimax
namespace NearlyMinimax
open MeasureTheory ProbabilityTheory Matrix MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
variable {d ℓ : ℕ}
abbrev DyadicGlobalDimension (d ℓ j : ℕ) :=
  Fintype.card (PilotBasisIndex (Fintype.card (DyadicPilotLabelIndex d j)) d (2 * ℓ))
abbrev IncrementGlobalIndex (d ℓ j : ℕ) :=
  Unit ⊕ (Fin (DyadicGlobalDimension d ℓ j) ⊕ Fin (DyadicGlobalDimension d ℓ (j - 1)))
def incrementGlobalFeature  (j ) (a : IncrementGlobalIndex d ℓ j)
    (z : Observation d) : ℝ :=
  match a with
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl i) => pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel j) z i
  | Sum.inr (Sum.inr i) => pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel (j - 1)) z i
def incrementGlobalVector  (j ) (z : Observation d) :
    Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ :=
  fun a => incrementGlobalFeature j ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)).symm a) z
def incrementGlobalMean  (θ : RegressionParameter d) (j ) :
    Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ :=
  fun a => ∫ z, incrementGlobalVector (ℓ := ℓ) j z a ∂observationLaw θ
theorem incrementGlobalFeature_measurable  (j )
    (a : IncrementGlobalIndex d ℓ j) : Measurable (incrementGlobalFeature j a) := by
  cases a with
  | inl _ => exact measurable_const
  | inr a =>
    cases a <;> exact pilotBasisFeature_measurable _ (dyadicPilotLabel_measurable _) _
theorem incrementGlobalVector_measurable  (j ) :
    Measurable (incrementGlobalVector (d := d) (ℓ := ℓ) j) :=
  measurable_pi_iff.mpr (fun _ => incrementGlobalFeature_measurable j _)
theorem incrementGlobalFeature_memLp_two  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
    (a : IncrementGlobalIndex d ℓ j) : MemLp (incrementGlobalFeature j a) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  cases a with
  | inl _ => exact memLp_const _
  | inr a =>
    cases a <;> exact pilotBasisFeature_memLp_two C θ hθ _ (dyadicPilotLabel_measurable _) _
def incrementGlobalCurrent  (j ) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ]
      (Fin (DyadicGlobalDimension d ℓ j) → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj
    ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)) (Sum.inr (Sum.inl i))))
def incrementGlobalParent  (j ) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ]
      (Fin (DyadicGlobalDimension d ℓ (j - 1)) → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj
    ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)) (Sum.inr (Sum.inr i))))
def incrementGlobalOne  (j ) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)) (Sum.inl ()))
@[simp] theorem incrementGlobalCurrent_raw  (j : ℕ) (z : Observation d) :
    incrementGlobalCurrent (ℓ := ℓ) j (incrementGlobalVector j z) =
      pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel j) z := by
  funext i
  simp [incrementGlobalCurrent, incrementGlobalVector, incrementGlobalFeature]
@[simp] theorem incrementGlobalParent_raw  (j : ℕ) (z : Observation d) :
    incrementGlobalParent (ℓ := ℓ) j (incrementGlobalVector j z) =
      pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel (j - 1)) z := by
  funext i
  simp [incrementGlobalParent, incrementGlobalVector, incrementGlobalFeature]
@[simp] theorem incrementGlobalOne_raw  (j : ℕ) (z : Observation d) :
    incrementGlobalOne (ℓ := ℓ) j (incrementGlobalVector j z) = 1 := by
  simp [incrementGlobalOne, incrementGlobalVector, incrementGlobalFeature]
def preconditionedPilotCoordinate  (j ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) : (Fin (DyadicGlobalDimension d ℓ j) → ℝ) →L[ℝ] ℝ :=
  ∑ β : AnchoredIndex d ℓ, (dyadicKnownGram j x)⁻¹ (localPilotRow a) β •
    dyadicPilotCoordinate j x (localPilotReplaceRow a β)
@[simp] theorem preconditionedPilotCoordinate_raw  (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) (z : Observation d) :
    preconditionedPilotCoordinate j x a (pilotRawVector (dyadicPilotLabel j) z) =
      preconditionedPilotFeature j x a z := by
  simp [preconditionedPilotCoordinate, preconditionedPilotFeature, smul_eq_mul,
    dyadicPilotCoordinate_raw_apply]
def incrementPilotFreeCoordinate  (j ) (x : Covariate d)
    (a : incrementVariables (anchoredDimension d ℓ)) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ :=
  match a with
  | Sum.inl (Sum.inl it) =>
    (preconditionedPilotCoordinate j x (Sum.inl (anchoredFinIndex it.1, anchoredFinIndex it.2))).comp
      (incrementGlobalCurrent j)
  | Sum.inl (Sum.inr it) =>
    if j = 0 then (if it.2.1 = it.2.2 then incrementGlobalOne j else 0) else
      (preconditionedPilotCoordinate (j - 1) x (Sum.inl (anchoredFinIndex it.2.1, anchoredFinIndex it.2.2))).comp
        (incrementGlobalParent j)
  | Sum.inr pri =>
    if pri.1 && (j == 0) then 0 else
      if pri.1 then
        (preconditionedPilotCoordinate (j - 1) x
          (if pri.2.1 then Sum.inr (Sum.inr (anchoredFinIndex pri.2.2))
            else Sum.inr (Sum.inl (anchoredFinIndex pri.2.2)))).comp (incrementGlobalParent j)
      else
        (preconditionedPilotCoordinate j x
          (if pri.2.1 then Sum.inr (Sum.inr (anchoredFinIndex pri.2.2))
            else Sum.inr (Sum.inl (anchoredFinIndex pri.2.2)))).comp (incrementGlobalCurrent j)
def incrementPilotCoordinate  (j ) (x : Covariate d) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ]
      (Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) :=
  ContinuousLinearMap.pi (fun a => incrementPilotFreeCoordinate j x
    ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a))
@[simp] theorem incrementPilotCoordinate_raw  (j x)
    (z : Observation d) :
    incrementPilotCoordinate j x (incrementGlobalVector j z) = dyadicIncrementRawVector (ℓ := ℓ) j x z := by
  funext a
  have h_incrementPilotFreeCoordinate_raw {ℓ : ℕ} (a : incrementVariables (anchoredDimension d ℓ)) : incrementPilotFreeCoordinate j x a (incrementGlobalVector j z) = dyadicIncrementFeature j x a z := by
    cases a with
    | inl a =>
      cases a with
      | inl a =>
        rcases a with ⟨i, t⟩
        simp [incrementPilotFreeCoordinate, dyadicIncrementFeature]
      | inr a =>
        by_cases hj : j = 0
        · by_cases hit : a.2.1 = a.2.2 <;> simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj, hit]
        · simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj]
    | inr a =>
      rcases a with ⟨parent, response, i⟩
      cases parent <;> cases response <;> by_cases hj : j = 0
      all_goals simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj]
  exact h_incrementPilotFreeCoordinate_raw _
theorem incrementGlobalVector_sample_facts {d ℓ n : ℕ} (C θ) (hθ : Admissible C θ) (j ) :
    iIndepFun (fun i (z : Fin n → Observation d) => incrementGlobalVector (ℓ := ℓ) j (z i)) (sampleLaw θ n) ∧
    (∀ i : Fin n, Measurable (fun z : Fin n → Observation d => incrementGlobalVector (ℓ := ℓ) j (z i))) ∧
    (∀ i t, IdentDistrib
      (fun z => incrementGlobalVector (ℓ := ℓ) j (z i))
      (fun z => incrementGlobalVector (ℓ := ℓ) j (z t)) (sampleLaw θ n) (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, MemLp (fun z => incrementGlobalVector (ℓ := ℓ) j (z i) a)
      2 (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, (∫ z : Fin n → Observation d, incrementGlobalVector (ℓ := ℓ) j (z i) a ∂sampleLaw θ n) =
      incrementGlobalMean θ j a) := by
  let := observationLaw_isProbability C θ hθ
  have hm := incrementGlobalVector_measurable (d := d) (ℓ := ℓ) j
  have hp (i : Fin n) : MeasurePreserving (fun z => z i)
      (sampleLaw θ n) (observationLaw θ) := measurePreserving_eval _ i
  refine ⟨iIndepFun_pi (fun _ : Fin n => hm.aemeasurable),
    fun i => hm.comp (measurable_pi_apply i), ?_, ?_, ?_⟩
  · intro i t
    have ht : IdentDistrib (fun z => z i)
        (fun z => z t) (sampleLaw θ n) (sampleLaw θ n) :=
      ⟨(hp i).aemeasurable, (hp t).aemeasurable, (hp i).map_eq.trans (hp t).map_eq.symm⟩
    exact ht.comp hm
  · intro i a
    exact (incrementGlobalFeature_memLp_two C θ hθ j _).comp_measurePreserving (hp i)
  · intro i a
    exact integral_comp_eval (μ := fun _ => observationLaw θ) (i := i)
      ((incrementGlobalFeature_measurable j
        ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)).symm a)).aestronglyMeasurable)
def dyadicIncrementKernel  (C : ModelConstants d) (θ : RegressionParameter d)
    (j ) (x : Covariate d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ) (k : ℕ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin k => Fin (Fintype.card (IncrementGlobalIndex d C.order j)) → ℝ) ℝ :=
  (iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
    C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
      (dyadicIncrementRawMean θ j x)).compContinuousLinearMap
        (fun _ => incrementPilotCoordinate j x)
theorem dyadicIncrementKernel_raw  (C : ModelConstants d) (θ j x y m)
    (row : Fin (anchoredDimension d C.order) → ℝ) (k : ℕ) (z : Fin k → Observation d) :
    dyadicIncrementKernel C θ j x y m row k (fun i => incrementGlobalVector j (z i)) =
      iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
        (dyadicIncrementRawMean θ j x) (fun i => dyadicIncrementRawVector j x (z i)) := by
  simp [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply]
theorem dyadicIncrementKernel_disjoint  (C θ j k) (hk : 0 < k) (x v )
    (hxv : dyadicPilotLabel (j - 1) x ≠ dyadicPilotLabel (j - 1) v)
    (y t m l row s)
    (z : Fin k → Observation d) :
    dyadicIncrementKernel C θ j x y m row k (fun i => incrementGlobalVector j (z i)) *
      dyadicIncrementKernel C θ j v t l s k (fun i => incrementGlobalVector j (z i)) = 0 := by
  rw [dyadicIncrementKernel_raw, dyadicIncrementKernel_raw]
  have h_dyadic_increment_raw_kernels_disjoint {ℓ : ℕ} (H : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) ℝ) (G : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) ℝ) : H (fun t => dyadicIncrementRawVector j x (z t)) *
      G (fun t => dyadicIncrementRawVector j v (z t)) = 0 := by
    let i : Fin k := ⟨0, hk⟩
    by_cases hz : (z i).1 ∈ dyadicPilotCell (j - 1) x
    · have hzy : (z i).1 ∉ dyadicPilotCell (j - 1) v := by
        intro h
        apply hxv
        exact ((dyadicPilotLabel_eq_iff (j - 1) x (z i).1).mpr hz).symm.trans
          ((dyadicPilotLabel_eq_iff (j - 1) v (z i).1).mpr h)
      rw [dyadic_increment_raw_kernel_zero_off_parent j v G z i hzy, mul_zero]
    · rw [dyadic_increment_raw_kernel_zero_off_parent j x H z i hz, zero_mul]
  exact h_dyadic_increment_raw_kernels_disjoint _ _
theorem dyadicPolynomialPilot_centered_global  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (n j : ℕ) (x y m row)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n) (z : Fin n → Observation d) :
    LiftL2.centeredKernelExpansion 0
      (fun r : Fin (m + anchoredDimension d C.order + 1) =>
        dyadicIncrementKernel C θ j x y m row (r.val + 1))
      (fun i z => incrementGlobalVector j (z i) - incrementGlobalMean θ j) z =
      dyadicPolynomialPilot C n j x y m row z -
        incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) y m row (dyadicIncrementRawMean θ j x) := by
  let F := rowIncrementPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m row
  have hF : (fun z => eval z F) = incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row := by
    funext z
    exact rowIncrementPolynomial_eval _ _ _ _ _ _ _ _
  have he := LiftL2.polynomialLift_centering_l2 F
    (fun i (z : Fin n → Observation d) => dyadicIncrementRawVector j x (z i))
    (dyadicIncrementRawMean θ j x) (rowIncrementPolynomial_degree _ _ _ _ _ _ _) hdegree
  change _ = RoughRegime.Upper.polynomialLift F
    (fun i (z : Fin n → Observation d) => dyadicIncrementRawVector j x (z i)) z - _
  rw [he]
  change _ = eval (dyadicIncrementRawMean θ j x) F + _ - _
  rw [rowIncrementPolynomial_eval, add_sub_cancel_left]
  simp only [LiftL2.centeredKernelExpansion, zero_add]
  apply Finset.sum_congr rfl
  intro r _
  unfold LiftL2.kernelStatistic LiftL2.kernelSum
  apply congrArg (fun a => (((r.val + 1).factorial : ℝ) *
    (n.descFactorial (r.val + 1) : ℝ))⁻¹ * a)
  apply Finset.sum_congr rfl
  intro e _
  rw [hF]
  have h_dyadicIncrementKernel_centered (k) (z : Fin k → Observation d) : dyadicIncrementKernel C θ j x y m row k
      (fun i => incrementGlobalVector j (z i) - incrementGlobalMean θ j) =
      iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
        (dyadicIncrementRawMean θ j x)
        (fun i => dyadicIncrementRawVector j x (z i) - dyadicIncrementRawMean θ j x) := by
    have h_incrementPilotCoordinate_mean {ℓ : ℕ} j (x : Covariate d) : incrementPilotCoordinate (ℓ := ℓ) j x (incrementGlobalMean θ j) = dyadicIncrementRawMean θ j x := by
      let := observationLaw_isProbability C θ hθ
      have hlp := KernelMomentBounds.vector_memLp_two (incrementGlobalVector (ℓ := ℓ) j)
        (incrementGlobalVector_measurable j) (fun a => incrementGlobalFeature_memLp_two C θ hθ j _)
      have hi := hlp.integrable (by norm_num)
      have hm : (∫ z, incrementGlobalVector (ℓ := ℓ) j z ∂observationLaw θ) = incrementGlobalMean θ j := by
        funext a
        exact ((ContinuousLinearMap.proj a :
          (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ).integral_comp_comm hi).symm
      rw [← hm, ← (incrementPilotCoordinate (ℓ := ℓ) j x).integral_comp_comm hi]
      simp only [incrementPilotCoordinate_raw]
      funext a
      simpa only [ContinuousLinearMap.proj_apply, incrementPilotCoordinate_raw,
        dyadicIncrementRawMean] using ((ContinuousLinearMap.proj a :
        (Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) →L[ℝ] ℝ).integral_comp_comm
        ((incrementPilotCoordinate (ℓ := ℓ) j x).integrable_comp hi)).symm
    simp [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      map_sub, h_incrementPilotCoordinate_mean]
  exact h_dyadicIncrementKernel_centered _ (fun i => z (e i))
theorem dyadicPilotCell_subset_coarser  (j J : ℕ) (hj : j ≤ J) (x : Covariate d) :
    dyadicPilotCell J x ⊆ dyadicPilotCell j x := by
  induction J with
  | zero =>
    have he : j = 0 := by omega
    subst j
    exact subset_rfl
  | succ J ih =>
    by_cases he : j = J + 1
    · subst j
      exact subset_rfl
    · intro z hz
      apply ih (by omega)
      simpa using dyadicPilotCell_subset_parent (J + 1) x hz
def dyadicPilotRow  (j : ℕ) (x z : Covariate d) : Fin (anchoredDimension d ℓ) → ℝ :=
  fun i => dyadicAnchoredFeature j x z (anchoredFinIndex i)
theorem dyadicPilotRow_sum_abs_le_distance  (j x z)
    (hx : x ∈ unitCube d) (hz : z ∈ unitCube d) (hc : z ∈ dyadicPilotCell j x) :
    (∑ i, |dyadicPilotRow (ℓ := ℓ) j x z i|) ≤
      anchoredDimension d ℓ  * ↑2 ^ j * euclideanNorm (z - x) := by
  have h_dyadicAnchoredFeature_abs_le_distance (γ : AnchoredIndex d ℓ) : |dyadicAnchoredFeature j x z γ| ≤ ↑2 ^ j * euclideanNorm (z - x) := by
    have hv (i : Fin d) : |((2 : ℝ) ^ j • (z - x)) i| ≤ 1 := by
      have hr := regular_grid_same_cell_radius (2 ^ j) (by positivity) z x hz hx hc i
      have he : ((2 ^ j : ℕ) : ℝ) = 2 ^ j := by simp
      rw [he] at hr
      change |(2 : ℝ) ^ j * (z i - x i)| ≤ 1
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans_eq (by field_simp)
    have h := anchoredMonomial_abs_le_euclideanNorm γ ((2 : ℝ) ^ j • (z - x)) hv
    rw [euclideanNorm_smul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j)] at h
    exact h
  apply (Finset.sum_le_sum (fun i _ => (h_dyadicAnchoredFeature_abs_le_distance _))).trans_eq
  simp [mul_assoc]
theorem dyadicPilotRow_sum_abs_le_fine_cell  (j J ) (hj : j ≤ J)
    (x z ) (hx : x ∈ unitCube d) (hz : z ∈ unitCube d)
    (hc : z ∈ dyadicPilotCell J x) :
    (∑ i, |dyadicPilotRow (ℓ := ℓ) j x z i|) ≤
      anchoredDimension d ℓ  * 2 ^ j * Real.sqrt d * (2 ^ J)⁻¹ := by
  apply (dyadicPilotRow_sum_abs_le_distance j x z hx hz
    (dyadicPilotCell_subset_coarser j J hj x hc)).trans
  have hr := euclideanNorm_le_coordinate_radius (z - x) (1 / ((↑2 ^ J : ℕ) : ℝ))
    (by positivity) (regular_grid_same_cell_radius (2 ^ J) (by positivity) z x hz hx hc)
  apply (mul_le_mul_of_nonneg_left hr (by positivity)).trans_eq
  simp [mul_assoc]
end NearlyMinimax
