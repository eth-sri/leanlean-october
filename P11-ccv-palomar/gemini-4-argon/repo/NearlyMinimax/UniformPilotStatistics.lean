module
public import Mathlib
public import NearlyMinimax.UniformPopulationBounds
@[expose] public section
noncomputable section
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
variable {d ℓ q p k : ℕ}
def pilotModelConstants  (C : ModelConstants d) : ModelConstants d :=
  { C with
    holderBound := max C.holderBound 1
    holderBound_pos := C.holderBound_pos.trans_le (le_max_left _ _) }
theorem admissible_pilotModelConstants  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    Admissible (pilotModelConstants C) θ := by
  obtain ⟨hpd, hpf, hpb, hpone, ⟨F, hFeq, hFdiff, hFnorm⟩, hVlo, hVhi, herr⟩ := hθ
  refine ⟨hpd, hpf, hpb, hpone, ⟨F, hFeq, hFdiff, ?_⟩, hVlo, hVhi, herr⟩
  exact hFnorm.trans (ENNReal.ofReal_mono (le_max_left _ _))
section
open Set MvPolynomial MeasureTheory Matrix ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator ENNReal
theorem finiteContinuousFamily_uniform_cube_bound   [Fintype ι]
    (f : Covariate d → ι → ℝ) (hf : ∀ i, Continuous (fun x => f x i)) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ i, |f x i| ≤ M := by
  obtain ⟨M, hM⟩ := (unitCube_isCompact d).bddAbove_image (continuous_pi hf).norm.continuousOn
  refine ⟨max 1 M, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro x hx i
  have hi : |f x i| ≤ ‖f x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (f x) i
  exact hi.trans ((hM (mem_image_of_mem _ hx)).trans (le_max_right _ _))
theorem dyadicPilotPolynomial_coeff_continuous  (j )
    (a : LocalPilotIndex d ℓ) (e : Fin d →₀ ℕ) :
    Continuous (fun x : Covariate d => (dyadicPilotPolynomial j x a).coeff e) := by
  have h_dyadicFeatureProduct_coeff_continuous {ℓ : ℕ} (γ : AnchoredIndex d ℓ) (δ : AnchoredIndex d ℓ) : Continuous (fun x : Covariate d =>
      (dyadicFeaturePolynomial j x γ * dyadicFeaturePolynomial j x δ).coeff e) := polynomialCoefficientContinuous_mul _ _ (dyadicFeaturePolynomial_coeff_continuous j γ)
    (dyadicFeaturePolynomial_coeff_continuous j δ) e
  cases a with
  | inl a => exact (h_dyadicFeatureProduct_coeff_continuous a.1 a.2)
  | inr a => cases a <;> exact dyadicFeaturePolynomial_coeff_continuous j _ e
theorem preconditionedPilotCoordinate_measurable  (j : ℕ) (a : LocalPilotIndex d ℓ) :
    Measurable (fun x : Covariate d => preconditionedPilotCoordinate j x a) := by
  have h_dyadicPilotCoordinate_measurable {d : ℕ} {ℓ : ℕ} (a : LocalPilotIndex d ℓ) : Measurable (fun x => dyadicPilotCoordinate j x a) := by
    have hlin : Measurable (fun x => pilotPolynomialLinear (ℓ := 2 * ℓ)
        (dyadicPilotLabel j x) (dyadicPilotPolynomial j x a) (dyadicPilotResponse a)) := by
      apply Finset.measurable_sum
      intro β _
      exact (dyadicPilotPolynomial_coeff_continuous j a _).measurable.smul
        ((measurable_of_countable (fun c : Fin (Fintype.card (DyadicPilotLabelIndex d j)) =>
          (ContinuousLinearMap.proj ((Fintype.equivFin
            (PilotBasisIndex (Fintype.card (DyadicPilotLabelIndex d j)) d (2 * ℓ)))
              ((c, β), dyadicPilotResponse a)) :
            (Fin (DyadicGlobalDimension d ℓ j) → ℝ) →L[ℝ] ℝ))).comp (dyadicPilotLabel_measurable j))
    exact (measurable_const : Measurable (fun _ => dyadicPilotScale d j)).smul hlin
  exact Finset.measurable_sum Finset.univ (fun β _ =>
    ((dyadicKnownGram_inverse_measurable j).eval_matrix (i := localPilotRow a) (j := β)).smul
      (h_dyadicPilotCoordinate_measurable (localPilotReplaceRow a β)))
theorem incrementPilotFreeCoordinate_measurable  (j )
    (a : incrementVariables (anchoredDimension d ℓ)) :
    Measurable (fun x : Covariate d => incrementPilotFreeCoordinate j x a) := by
  let pc : ((Fin (DyadicGlobalDimension d ℓ j) → ℝ) →L[ℝ] ℝ) →L[ℝ]
      ((Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ (incrementGlobalCurrent j)
  let pp : ((Fin (DyadicGlobalDimension d ℓ (j - 1)) → ℝ) →L[ℝ] ℝ) →L[ℝ]
      ((Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ (incrementGlobalParent j)
  have hc (a : LocalPilotIndex d ℓ) : Measurable (fun x : Covariate d =>
      (preconditionedPilotCoordinate j x a).comp (incrementGlobalCurrent j)) :=
    pc.measurable.comp
      (preconditionedPilotCoordinate_measurable j a)
  have hp (a : LocalPilotIndex d ℓ) : Measurable (fun x : Covariate d =>
      (preconditionedPilotCoordinate (j - 1) x a).comp (incrementGlobalParent j)) :=
    pp.measurable.comp
      (preconditionedPilotCoordinate_measurable (j - 1) a)
  cases a with
  | inl a =>
    cases a with
    | inl a => exact hc _
    | inr a =>
      change Measurable (fun x => if j = 0 then
        (if a.2.1 = a.2.2 then incrementGlobalOne j else 0) else _)
      split_ifs
      · exact measurable_const
      · exact measurable_const
      · exact hp (Sum.inl (anchoredFinIndex a.2.1, anchoredFinIndex a.2.2))
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    simp only [incrementPilotFreeCoordinate]
    split_ifs
    · exact measurable_const
    · exact hp (Sum.inr (Sum.inr (anchoredFinIndex i)))
    · exact hp (Sum.inr (Sum.inl (anchoredFinIndex i)))
    · exact hc (Sum.inr (Sum.inr (anchoredFinIndex i)))
    · exact hc (Sum.inr (Sum.inl (anchoredFinIndex i)))
theorem incrementPilotCoordinate_measurable  (j ) :
    Measurable (incrementPilotCoordinate (d := d) (ℓ := ℓ) j) := by
  exact (ContinuousLinearMap.piEquivL ℝ
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ)
    (fun _ => ℝ)).continuous.measurable.comp
      (measurable_pi_iff.mpr (fun _ => incrementPilotFreeCoordinate_measurable j _))
theorem real_pi_projection_norm_le  [Fintype ι] (i ) :
    ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm v i
theorem pilotPolynomialLinear_norm_le  (c : Fin q)
    (P : MvPolynomial (Fin d) ℝ) (response ) (M : ℝ) (hM : 0 ≤ M)
    (hP : ∀ β : PolynomialBox d ℓ, |P.coeff (polynomialBoxExponent β)| ≤ M) :
    ‖pilotPolynomialLinear (ℓ := ℓ) c P response‖ ≤
      (Fintype.card (PolynomialBox d ℓ) : ℝ) * M := by
  apply (norm_sum_le _ _).trans
  calc
    (∑ β : PolynomialBox d ℓ, ‖P.coeff (polynomialBoxExponent β) •
      (ContinuousLinearMap.proj ((Fintype.equivFin (PilotBasisIndex q d ℓ)) ((c, β), response)) :
        (Fin (Fintype.card (PilotBasisIndex q d ℓ)) → ℝ) →L[ℝ] ℝ)‖) ≤ ∑ _β : PolynomialBox d ℓ, M := by
      apply Finset.sum_le_sum
      intro β _
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul (hP β) (real_pi_projection_norm_le _) (norm_nonneg _) hM).trans_eq (mul_one M)
    _ = (Fintype.card (PolynomialBox d ℓ) : ℝ) * M := by simp
theorem preconditionedPilotCoordinate_uniform_bound  (j ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ a : LocalPilotIndex d ℓ,
      ‖preconditionedPilotCoordinate j x a‖ ≤ M := by
  obtain ⟨L, hL, hLb⟩ := dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ)
  have h_dyadicPilotCoordinate_uniform_bound : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ a : LocalPilotIndex d ℓ,
      ‖dyadicPilotCoordinate j x a‖ ≤ M := by
    have h_dyadicPilotPolynomial_coeff_uniform_bound : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ a : LocalPilotIndex d ℓ,
      ∀ β : PolynomialBox d (2 * ℓ),
        |(dyadicPilotPolynomial j x a).coeff (polynomialBoxExponent β)| ≤ M := by
      obtain ⟨M, hM, hb⟩ := finiteContinuousFamily_uniform_cube_bound
        (fun x (i : LocalPilotIndex d ℓ × PolynomialBox d (2 * ℓ)) =>
          (dyadicPilotPolynomial j x i.1).coeff (polynomialBoxExponent i.2))
        (fun i => dyadicPilotPolynomial_coeff_continuous j i.1 _)
      exact ⟨M, hM, fun x hx a β => hb x hx (a, β)⟩
    obtain ⟨P, hP, hcap⟩ := h_dyadicPilotPolynomial_coeff_uniform_bound
    let B := dyadicPilotScale d j * ((Fintype.card (PolynomialBox d (2 * ℓ)) : ℝ) * P)
    refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
    intro x hx a
    have hscale : 0 ≤ dyadicPilotScale d j := by dsimp [dyadicPilotScale]; positivity
    rw [dyadicPilotCoordinate, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
    exact (mul_le_mul_of_nonneg_left (pilotPolynomialLinear_norm_le _ _ _ P hP.le
      (hcap x hx a)) hscale).trans (le_max_right _ _)
  obtain ⟨P, hP, hPb⟩ := h_dyadicPilotCoordinate_uniform_bound
  let B := (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (L * P)
  refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro x hx a
  letI : Nonempty (AnchoredIndex d ℓ) := ⟨localPilotRow a⟩
  apply (norm_sum_le _ _).trans
  calc
    (∑ β : AnchoredIndex d ℓ, ‖(dyadicKnownGram j x)⁻¹ (localPilotRow a) β •
        dyadicPilotCoordinate j x (localPilotReplaceRow a β)‖) ≤ ∑ _β : AnchoredIndex d ℓ, L * P := by
      apply Finset.sum_le_sum
      intro β _
      rw [norm_smul]
      exact mul_le_mul ((matrix_real_entry_norm_le _ _ _).trans (hLb j x hx))
        (hPb x hx _) (norm_nonneg _) hL.le
    _ = B := by simp [B]
    _ ≤ max 1 B := le_max_right _ _
theorem incrementPilotCoordinate_uniform_bound  (j ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ‖incrementPilotCoordinate (ℓ := ℓ) j x‖ ≤ M := by
  obtain ⟨C, hC, hCb⟩ := preconditionedPilotCoordinate_uniform_bound (d := d) (ℓ := ℓ) j
  obtain ⟨P, hP, hPb⟩ := preconditionedPilotCoordinate_uniform_bound (d := d) (ℓ := ℓ) (j - 1)
  let M := max 1 (max C P)
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨M, hM, ?_⟩
  intro x hx
  have hc (a : LocalPilotIndex d ℓ) :
      ‖(preconditionedPilotCoordinate j x a).comp (incrementGlobalCurrent j)‖ ≤ M :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (hCb x hx a) (ContinuousLinearMap.norm_pi_le_of_le (fun _ => real_pi_projection_norm_le _) zero_le_one) (norm_nonneg _) hC.le).trans
        (by simpa only [mul_one] using ((le_max_left C P).trans (le_max_right 1 (max C P)))))
  have hp (a : LocalPilotIndex d ℓ) :
      ‖(preconditionedPilotCoordinate (j - 1) x a).comp (incrementGlobalParent j)‖ ≤ M :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (hPb x hx a) (ContinuousLinearMap.norm_pi_le_of_le (fun _ => real_pi_projection_norm_le _) zero_le_one) (norm_nonneg _) hP.le).trans
        (by simpa only [mul_one] using ((le_max_right C P).trans (le_max_right 1 (max C P)))))
  apply ContinuousLinearMap.norm_pi_le_of_le _ hM.le
  intro i
  let a := (Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm i
  change ‖incrementPilotFreeCoordinate j x a‖ ≤ M
  cases a with
  | inl a =>
    cases a with
    | inl a => exact hc _
    | inr a =>
      simp only [incrementPilotFreeCoordinate]
      split_ifs
      · exact (real_pi_projection_norm_le _).trans (le_max_left _ _)
      · simpa only [norm_zero] using hM.le
      · exact hp (Sum.inl (anchoredFinIndex a.2.1, anchoredFinIndex a.2.2))
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    simp only [incrementPilotFreeCoordinate]
    split_ifs
    · simpa only [norm_zero] using hM.le
    · exact hp (Sum.inr (Sum.inr (anchoredFinIndex i)))
    · exact hp (Sum.inr (Sum.inl (anchoredFinIndex i)))
    · exact hc (Sum.inr (Sum.inr (anchoredFinIndex i)))
    · exact hc (Sum.inr (Sum.inl (anchoredFinIndex i)))
instance finiteInputMultilinearMeasurableSpace {p k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    MeasurableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) F) := borel _
instance finiteInputMultilinearBorelSpace {p k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    BorelSpace (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) F) := ⟨rfl⟩
instance finiteInputScalarMultilinearFiniteDimensional (p k : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ) := by
  let e : (ContinuousMultilinearMap ℝ (fun _ => Fin p → ℝ) ℝ) →L[ℝ]
      ((Fin k → Fin p) → ℝ) := ContinuousLinearMap.pi (fun σ =>
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin p → ℝ) ℝ
      (fun i => Pi.single (σ i) 1))
  apply FiniteDimensional.of_injective e.toLinearMap
  intro H G he
  ext v
  change H.toMultilinearMap v = G.toMultilinearMap v
  rw [LiftL2.multilinear_coordinate_expansion H.toMultilinearMap,
    LiftL2.multilinear_coordinate_expansion G.toMultilinearMap]
  apply Finset.sum_congr rfl
  intro σ _
  have hc := congrFun he σ
  change H (fun i => Pi.single (σ i) 1) = G (fun i => Pi.single (σ i) 1) at hc
  exact congrArg (fun a => a * ∏ i, v i (σ i)) hc
theorem continuous_row_postcompose {p r k : ℕ} :
    Continuous (fun z : (Fin r → ℝ) ×
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) (Fin r → ℝ) =>
        (rowFunctional z.1).compContinuousMultilinearMap z.2) := by
  change Continuous (fun z : (Fin r → ℝ) ×
      ContinuousMultilinearMap ℝ (fun _ => Fin p → ℝ) (Fin r → ℝ) =>
    (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ => Fin p → ℝ)
      (Fin r → ℝ) ℝ (rowFunctional z.1)) z.2)
  exact ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => Fin p → ℝ)
    (Fin r → ℝ) ℝ).continuous.comp ((continuous_finset_sum Finset.univ (fun i _ => (continuous_apply i).smul continuous_const)).comp continuous_fst)).clm_apply continuous_snd
theorem continuous_multilinear_pullback  :
    Continuous (fun z :
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ ×
        ((Fin q → ℝ) →L[ℝ] (Fin p → ℝ)) =>
        z.1.compContinuousLinearMap (fun _ => z.2)) := by
  change Continuous (fun z :
      ContinuousMultilinearMap ℝ (fun _ => Fin p → ℝ) ℝ ×
        ((Fin q → ℝ) →L[ℝ] (Fin p → ℝ)) =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ => Fin q → ℝ) (fun _ => Fin p → ℝ) ℝ (fun _ => z.2)) z.1)
  exact ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ => Fin q → ℝ) (fun _ => Fin p → ℝ) ℝ).cont.comp
    (continuous_pi (fun _ => continuous_snd))).clm_apply continuous_fst
theorem dyadicIncrementKernel_field_measurable  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (j y m k row)
    (hrow : Measurable row) :
    Measurable (fun w : Covariate d × Covariate d =>
      dyadicIncrementKernel C θ j w.1 y m (row w) k) := by
  have hm : Measurable (fun w : Covariate d × Covariate d =>
      dyadicIncrementRawMean (ℓ := C.order) θ j w.1) :=
    (dyadicIncrementRawMean_measurable (ℓ := C.order) C θ hθ j).comp measurable_fst
  have hD := ((incrementFinVector_contDiff (anchoredDimension d C.order)
    C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m).continuous_iteratedFDeriv
      (show (k : WithTop ℕ∞) ≤ ⊤ from le_top)).measurable.comp hm
  have hscalar := continuous_row_postcompose.measurable.comp (hrow.prodMk hD)
  change Measurable (fun w =>
    (rowFunctional (row w)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ k (incrementFinVector (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m)
        (dyadicIncrementRawMean θ j w.1))) at hscalar
  have heq : (fun w =>
      (rowFunctional (row w)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (incrementFinVector (anchoredDimension d C.order)
          C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m)
          (dyadicIncrementRawMean θ j w.1))) =
      (fun w => iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m (row w))
        (dyadicIncrementRawMean θ j w.1)) := by
    funext w
    ext v
    exact (incrementFinScalar_iteratedFDeriv _ _ _ _ _ _ _ _ _ _).symm
  rw [heq] at hscalar
  exact continuous_multilinear_pullback.measurable.comp
    (hscalar.prodMk ((incrementPilotCoordinate_measurable (ℓ := C.order) j).comp measurable_fst))
theorem dyadicIncrementKernel_field_norm_bound  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (j y) (hy : |y| ≤ C.holderBound) (m k : ℕ)
    (row : Covariate d × Covariate d → Fin (anchoredDimension d C.order) → ℝ)
    (M : Measure (Covariate d × Covariate d)) (R : ℝ) (hR : 0 ≤ R)
    (hcube : ∀ᵐ w ∂M, w.1 ∈ unitCube d)
    (hrow : ∀ᵐ w ∂M, (∑ i, |row w i|) ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ w ∂M, ‖dyadicIncrementKernel C θ j w.1 y m (row w) k‖ ≤ B := by
  have h_admissible_dyadic_increment_all_derivative_bound : ∃ D A, 0 < D ∧ 0 < A ∧
      ∀ θ, Admissible C θ → ∀ j,
      ∀ x ∈ unitCube d, ∀ y, |y| ≤ C.holderBound → ∀ m k row,
        ‖iteratedFDeriv ℝ k
          (incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) y m row)
          (dyadicIncrementRawMean θ j x)‖ ≤
          (∑ i, |row i|) * D * k.factorial * A ^ k := by
    have h_admissible_dyadic_increment_root_derivative_bound : ∃ D A, 0 < D ∧ 0 < A ∧
        ∀ θ, Admissible C θ → ∀ x ∈ unitCube d,
        ∀ y, |y| ≤ C.holderBound → ∀ m k row,
          ‖iteratedFDeriv ℝ k
            (incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
              (anchoredFinTransport d C.order) y m row)
            (dyadicIncrementRawMean θ 0 x)‖ ≤
            (∑ i, |row i|) * D * k.factorial * A ^ k := by
      obtain ⟨W, hW, hmom⟩ := anchoredFinMomentFamilies_uniform_bound
        (d := d) (ℓ := C.order) C.densityUpper C.holderBound (zero_le_one.trans C.one_lt_densityUpper.le) C.holderBound_pos.le
      obtain ⟨D, A, hD, hA, hder⟩ := anchored_population_inverse_derivatives
        (d := d) (ℓ := C.order) C.densityLower C.densityUpper W C.holderBound
        C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le C.holderBound_pos.le
      refine ⟨D, A, hD, hA, ?_⟩
      intro θ hθ x hx y hy m k row
      have hu : dyadicNormalizedAnchor 0 x ∈ unitCube d :=
        gridNormalizedAnchor_mem_cube _ (by positivity) x hx
      have hp := dyadicNormalizedDensity_bounds C θ hθ 0 x
      have hU := hmom _ hu _ _
        (hp.mono (fun w hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩)) (fun w hw => admissible_regression_value_bound C θ hθ _ (dyadicCellAffine_mem_cube 0 x w hw))
      apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
      intro directions
      rw [incrementFinScalar_iteratedFDeriv, dyadicIncrementRawMean_root_eq_normalized C θ hθ x hx]
      have hd := hder _ _ hu hu _ (fun _ => 1)
        (dyadicNormalizedDensity_measurable C θ hθ 0 x) measurable_const hp
        (Filter.Eventually.of_forall (fun _ => ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩))
        _ 0 hU (by simpa using hW.le) y hy m k directions
      calc
        _ ≤ ‖rowFunctional row‖ * ‖iteratedFDeriv ℝ k
            (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
              (anchoredFinTransport d C.order) y m)
            (fun a => incrementValuation
              (anchoredFinNormalizedGram (dyadicNormalizedAnchor 0 x) (dyadicNormalizedDensity θ 0 x))
              (anchoredFinNormalizedGram (dyadicNormalizedAnchor 0 x) (fun _ => 1))
              (anchoredFinMomentFamilies (dyadicNormalizedAnchor 0 x) (dyadicNormalizedDensity θ 0 x)
                (θ.regression ∘ dyadicCellAffine 0 x)) 0
              ((Fintype.equivFin (incrementVariables (anchoredDimension d C.order))).symm a)) directions‖ :=
          (rowFunctional row).le_opNorm _
        _ ≤ (∑ i, |row i|) * (D * k.factorial * A ^ k * ∏ i, ‖directions i‖) :=
          mul_le_mul (rowFunctional_norm_le row) hd (norm_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _))
        _ = (∑ i, |row i|) * D * k.factorial * A ^ k * ∏ i, ‖directions i‖ := by ring
    obtain ⟨D₀, A₀, hD₀, hA₀, hroot⟩ := h_admissible_dyadic_increment_root_derivative_bound
    have h_admissible_dyadic_increment_derivative_bound : ∃ D A, 0 < D ∧ 0 < A ∧
        ∀ θ, Admissible C θ → ∀ j, j ≠ 0 →
        ∀ x ∈ unitCube d, ∀ y, |y| ≤ C.holderBound → ∀ m k row,
          ‖iteratedFDeriv ℝ k
            (incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
              (anchoredFinTransport d C.order) y m row)
            (dyadicIncrementRawMean θ j x)‖ ≤
            (∑ i, |row i|) * D * k.factorial * A ^ k := by
      obtain ⟨D, A, hD, hA, hder⟩ := anchored_actual_population_row_derivative_operator_bound
        (d := d) (ℓ := C.order) C.densityLower C.densityUpper C.holderBound C.holderBound
        C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)
        C.holderBound_pos.le C.holderBound_pos.le
      refine ⟨D, A, hD, hA, ?_⟩
      intro θ hθ j hj x hx y hy m k row
      rw [dyadicIncrementRawMean_eq_normalized C θ hθ j hj x hx]
      exact hder _ _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx)
        (gridNormalizedAnchor_mem_cube _ (by positivity) x hx) _ _ _ _
        (dyadicNormalizedDensity_measurable C θ hθ j x)
        (dyadicNormalizedDensity_measurable C θ hθ (j - 1) x)
        (dyadicNormalizedDensity_bounds C θ hθ j x)
        (dyadicNormalizedDensity_bounds C θ hθ (j - 1) x)
        (fun w hw => admissible_regression_value_bound C θ hθ _ (dyadicCellAffine_mem_cube j x w hw))
        (fun w hw => admissible_regression_value_bound C θ hθ _ (dyadicCellAffine_mem_cube (j - 1) x w hw))
        y hy m k row
    obtain ⟨D₁, A₁, hD₁, hA₁, hnext⟩ := h_admissible_dyadic_increment_derivative_bound
    refine ⟨max D₀ D₁, max A₀ A₁, hD₀.trans_le (le_max_left _ _), hA₀.trans_le (le_max_left _ _), ?_⟩
    intro θ hθ j x hx y hy m k row
    by_cases hj : j = 0
    · subst j
      apply (hroot θ hθ x hx y hy m k row).trans
      gcongr <;> exact le_max_left _ _
    · apply (hnext θ hθ j hj x hx y hy m k row).trans
      gcongr <;> exact le_max_right _ _
  obtain ⟨D, A, hD, hA, hder⟩ := h_admissible_dyadic_increment_all_derivative_bound
  obtain ⟨L, hL, hmap⟩ := incrementPilotCoordinate_uniform_bound (d := d) (ℓ := C.order) j
  refine ⟨max 1 (R * D * ↑k.factorial * A ^ k * L ^ k), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hcube, hrow] with w hw hr
  apply le_trans _ (le_max_right _ _)
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  exact mul_le_mul (by apply (hder θ hθ j w.1 hw y hy m k (row w)).trans; gcongr) ((Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hmap _ hw)).trans_eq (by simp)) (Finset.prod_nonneg (fun i _ => norm_nonneg _)) (by positivity)
theorem dyadicIncrementKernel_weighted_integrable  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (j y) (hy : |y| ≤ C.holderBound) (m k )
    (row : Covariate d × Covariate d → Fin (anchoredDimension d C.order) → ℝ)
    (hrowMeas : Measurable row) (M : Measure (Covariate d × Covariate d)) [IsFiniteMeasure M]
    (R : ℝ) (hR : 0 ≤ R) (hcube : ∀ᵐ w ∂M, w.1 ∈ unitCube d)
    (hrow : ∀ᵐ w ∂M, (∑ i, |row w i|) ≤ R) (ν : Covariate d × Covariate d → ℝ)
    (hν : MemLp ν 2 M) :
    Integrable (fun w => ν w • dyadicIncrementKernel C θ j w.1 y m (row w) k) M := by
  obtain ⟨B, _, hcap⟩ := dyadicIncrementKernel_field_norm_bound C θ hθ j y hy m k row M R hR hcube hrow
  exact (hν.integrable (by norm_num)).smul_bdd B
    (dyadicIncrementKernel_field_measurable C θ hθ j y m k row hrowMeas).aestronglyMeasurable hcap
theorem dyadicPilotRow_field_measurable  (j : ℕ) :
    Measurable (fun w : Covariate d × Covariate d => dyadicPilotRow (ℓ := ℓ) j w.1 w.2) := by
  apply measurable_pi_iff.mpr
  intro i
  exact ((anchoredMonomial_continuous (anchoredFinIndex i)).comp
    (continuous_pi (fun t => continuous_const.mul
      (((continuous_apply t).comp continuous_snd).sub
        ((continuous_apply t).comp continuous_fst))))).measurable
def dyadicPilotRowCap (d ℓ j J : ℕ) : ℝ :=
  anchoredDimension d ℓ  * 2 ^ j * Real.sqrt d * (2 ^ J)⁻¹
theorem dyadicPilotRowCap_nonneg (d ℓ j J ) : 0 ≤ dyadicPilotRowCap d ℓ j J := by
  unfold dyadicPilotRowCap
  positivity
theorem dyadicPilotRow_pair_cap  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j J : ℕ) (hj : j ≤ J) :
    ∀ᵐ w ∂regularPairDesignMeasure θ (↑2 ^ J) (by positivity),
      (∑ i, |dyadicPilotRow (ℓ := ℓ) j w.1 w.2 i|) ≤ dyadicPilotRowCap d ℓ j J := by
  have h_regularPairDesignMeasure_same_cell_ae (k : ℕ) (hk : 0 < k) : ∀ᵐ w ∂regularPairDesignMeasure θ k hk, regularGridCell k hk w.1 = regularGridCell k hk w.2 := by
    apply Measure.ae_smul_measure
    exact ae_restrict_mem (measurableSet_eq_fun
      ((regular_grid_cell_measurable k hk).comp measurable_fst)
      ((regular_grid_cell_measurable k hk).comp measurable_snd))
  filter_upwards [regularPairDesignMeasure_cube_ae C θ hθ ((2 : ℕ) ^ J) (by positivity),
    h_regularPairDesignMeasure_same_cell_ae (2 ^ J) (by positivity)] with w hw hc
  exact dyadicPilotRow_sum_abs_le_fine_cell j J hj w.1 w.2 hw.1 hw.2 hc.symm
def dyadicPilotErrorField  (C : ModelConstants d) (θ : RegressionParameter d)
    (n j : ℕ) (y : ℝ) (m : ℕ) (z : Fin n → Observation d) (w : Covariate d × Covariate d) : ℝ :=
  dyadicPolynomialPilot C n j w.1 y m (dyadicPilotRow j w.1 w.2) z -
    incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
      (anchoredFinTransport d C.order) y m (dyadicPilotRow j w.1 w.2)
        (dyadicIncrementRawMean θ j w.1)
theorem dyadicPilotErrorField_test_moment_facts  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (n j J ) (hj : j ≤ J) (y ) (hy : |y| ≤ C.holderBound) (m )
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n)
    (ν )
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity))) :
    MemLp (fun z => ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w
      ∂regularPairDesignMeasure θ (2 ^ J) (by positivity)) 2 (sampleLaw θ n) ∧
    (∫ z, ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w
      ∂regularPairDesignMeasure θ (2 ^ J) (by positivity) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  let M := regularPairDesignMeasure θ (2 ^ J) (by positivity)
  let := regularPairDesignMeasure_isFinite C θ hθ (2 ^ J) (by positivity)
  let R := m + anchoredDimension d C.order + 1
  let H (w : Covariate d × Covariate d) (r : Fin R) :=
    dyadicIncrementKernel C θ j w.1 y m (dyadicPilotRow j w.1 w.2) (r.val + 1)
  have hH (r : Fin R) : Integrable (fun w => ν w • H w r) M :=
    dyadicIncrementKernel_weighted_integrable C θ hθ j y hy m (r.val + 1) _
      (dyadicPilotRow_field_measurable j) M (dyadicPilotRowCap d C.order j J)
      (dyadicPilotRowCap_nonneg _ _ _ _) ((regularPairDesignMeasure_cube_ae C θ hθ (2 ^ J) (by positivity)).mono (fun w hw => hw.1)) (dyadicPilotRow_pair_cap (ℓ := C.order) C θ hθ j J hj) ν hν
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := incrementGlobalVector_sample_facts (ℓ := C.order) C θ hθ j
  have h := FieldLiftCovariance.integrated_centered_lift_moment_facts H ν hH
    (fun i (z : Fin n → Observation d) => incrementGlobalVector j (z i))
    (incrementGlobalMean θ j) hind hmeas hid hL2 hmean
  have heq : (fun z => ∫ w, ν w *
      LiftL2.centeredKernelExpansion 0 (H w)
        (fun i z => incrementGlobalVector j (z i) - incrementGlobalMean θ j) z ∂M) =
      (fun z => ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w ∂M) := by
    funext z
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => congrArg (fun a => ν w * a)
      (dyadicPolynomialPilot_centered_global C θ hθ n j w.1 y m (dyadicPilotRow j w.1 w.2) hdegree z)
  rwa [heq] at h
end
theorem secondMoment_dyadic_sum_le  [MeasurableSpace Ω]
    (μ : Measure Ω) (J : ℕ) (X : Fin (J + 1) → Ω → ℝ)
    (hX : ∀ j, MemLp (X j) 2 μ) (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ j, (∫ z, X j z ^ 2 ∂μ) ≤ B * ((2 : ℝ) ^ j.val) ^ 2) :
    (∫ z, (∑ j, X j z) ^ 2 ∂μ) ≤ 4 * B * (↑2 ^ J) ^ 2 := by
  have h_secondMoment_sum_le_weighted {ι} [Fintype ι] (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hE : ∀ i, (∫ z, X i z ^ 2 ∂μ) ≤ B * w i ^ 2) : (∫ z, (∑ i, X i z) ^ 2 ∂μ) ≤ B * (∑ i, w i) ^ 2 := by
    have hsum : MemLp (fun z => ∑ i, X i z) 2 μ := memLp_finsetSum _ (fun i _ => hX i)
    have hi (i) : Integrable (fun z => X i z ^ 2 / w i) μ :=
      (hX i).integrable_sq.div_const _
    have hpoint (z) : (∑ i, X i z) ^ 2 ≤ (∑ i, w i) * ∑ i, X i z ^ 2 / w i := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (fun i _ => (hw i).le) (fun i _ => div_nonneg (sq_nonneg _) (hw i).le)
      intro i _
      exact le_of_eq (by field_simp [(hw i).ne'])
    have hm := integral_mono hsum.integrable_sq
      ((integrable_finsetSum Finset.univ (fun i _ => hi i)).const_mul (∑ i, w i)) hpoint
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hi i)] at hm
    have hterms : (∑ i, ∫ z, X i z ^ 2 / w i ∂μ) ≤ B * ∑ i, w i := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      rw [integral_div]
      apply (div_le_div_of_nonneg_right (hE i) (hw i).le).trans_eq
      field_simp [(hw i).ne']
    calc
      _ ≤ (∑ i, w i) * (B * ∑ i, w i) := hm.trans
        (mul_le_mul_of_nonneg_left hterms (Finset.sum_nonneg (fun i _ => (hw i).le)))
      _ = _ := by ring
  have h := (h_secondMoment_sum_le_weighted X hX (fun j => ↑2 ^ j.val) (fun _ => by positivity) hE)
  have h_dyadic_geometric_sum_bound : (∑ j : Fin (J + 1), ↑2 ^ j.val) ≤ 2 * (2 : ℝ) ^ J := by
    rw [Fin.sum_univ_eq_sum_range]
    have h := geom_sum_mul_of_one_le (by norm_num : (1 : ℝ) ≤ 2) (J + 1)
    norm_num only [sub_self, add_zero, sub_zero, mul_one] at h
    rw [h, pow_succ]
    linarith
  have hs := h_dyadic_geometric_sum_bound
  have hnon : 0 ≤ ∑ j : Fin (J + 1), (2 : ℝ) ^ j.val := by positivity
  apply h.trans
  nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnon hs 2) hB]
theorem centeredKernelExpansion_field_measurable 
    [MeasurableSpace Ω] [MeasurableSpace W] {n p R : ℕ}
    (H : W → (r : Fin R) → ContinuousMultilinearMap ℝ
      (fun _ : Fin (r.val + 1) => Fin p → ℝ) ℝ)
    (hH : ∀ r, Measurable (fun w => H w r))
    (X : Fin n → Ω → Fin p → ℝ) (hX : ∀ i, Measurable (X i)) :
    Measurable (fun t : Ω × W => LiftL2.centeredKernelExpansion 0 (H t.2) X t.1) := by
  unfold LiftL2.centeredKernelExpansion LiftL2.kernelStatistic LiftL2.kernelSum
  simp only [zero_add]
  apply Finset.measurable_sum
  intro r _
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro e _
  exact (continuous_eval).measurable.comp (((hH r).comp measurable_snd).prodMk (measurable_pi_iff.mpr (fun i => (hX (e i)).comp measurable_fst)))
def dyadicMultilevelErrorField  (C : ModelConstants d) (θ : RegressionParameter d)
    (n J : ℕ) (y : ℝ) (m : ℕ → ℕ) (z : Fin n → Observation d)
    (w : Covariate d × Covariate d) : ℝ :=
  ∑ j : Fin (J + 1), dyadicPilotErrorField C θ n j.val y (m j.val) z w
def dyadicMultilevelBudget (H : ℝ) (J L : ℕ) : ℝ :=
  ((2 ^ L)⁻¹) ^ 2 * (2 ^ J) ^ 2 * H
theorem dyadicPilotRowCap_square (d ℓ j L D) :
    (dyadicPilotRowCap d ℓ j L * D) ^ 2 =
      ((anchoredDimension d ℓ ) * D) ^ 2 * d *
        ((2 ^ L)⁻¹) ^ 2 * (2 ^ j) ^ 2 := by
  simp only [dyadicPilotRowCap, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  ring
theorem dyadicPilotErrorField_point_moment_facts  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (n j x) (hx : x ∈ unitCube d) (z y m) (hdegree : m + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (fun t => dyadicPilotErrorField C θ n j y m t (x, z)) 2 (sampleLaw θ n) ∧
      (∫ t, dyadicPilotErrorField C θ n j y m t (x, z) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  obtain ⟨hL2, hmean⟩ := dyadicPolynomialPilot_moment_facts C θ hθ n j x hx y m
    (dyadicPilotRow j x z) hdegree
  refine ⟨hL2.sub (memLp_const _), ?_⟩
  unfold dyadicPilotErrorField
  rw [integral_sub (hL2.integrable (by norm_num)) (integrable_const _), hmean]
  simp
theorem dyadicMultilevelErrorField_point_moment_facts  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (n J x) (hx : x ∈ unitCube d) (z y m)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (fun t => dyadicMultilevelErrorField C θ n J y m t (x, z)) 2 (sampleLaw θ n) ∧
      (∫ t, dyadicMultilevelErrorField C θ n J y m t (x, z) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  have hf (j : Fin (J + 1)) := dyadicPilotErrorField_point_moment_facts C θ hθ n j.val x hx z y
    (m j.val) (hdegree j)
  refine ⟨memLp_finsetSum _ (fun j _ => (hf j).1), ?_⟩
  unfold dyadicMultilevelErrorField
  rw [integral_finsetSum Finset.univ (fun j _ => (hf j).1.integrable (by norm_num))]
  exact Finset.sum_eq_zero (fun j _ => (hf j).2)
theorem dyadicPilotErrorField_weighted_integrable  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (n j L ) (hj : j ≤ L) (y ) (hy : |y| ≤ C.holderBound) (m )
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n)
    (ν )
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)))
    (t ) :
    Integrable (fun w => ν w * dyadicPilotErrorField C θ n j y m t w)
      (regularPairDesignMeasure θ (2 ^ L) (by positivity)) := by
  let M := regularPairDesignMeasure θ (2 ^ L) (by positivity)
  let := regularPairDesignMeasure_isFinite C θ hθ (2 ^ L) (by positivity)
  let R := m + anchoredDimension d C.order + 1
  let H (w : Covariate d × Covariate d) (r : Fin R) :=
    dyadicIncrementKernel C θ j w.1 y m (dyadicPilotRow j w.1 w.2) (r.val + 1)
  let X (i : Fin n) (z : Fin n → Observation d) :=
    incrementGlobalVector (ℓ := C.order) j (z i) - incrementGlobalMean θ j
  have hH (r : Fin R) : Integrable (fun w => ν w • H w r) M :=
    dyadicIncrementKernel_weighted_integrable C θ hθ j y hy m (r.val + 1) _
      (dyadicPilotRow_field_measurable j) M (dyadicPilotRowCap d C.order j L)
      (dyadicPilotRowCap_nonneg _ _ _ _) ((regularPairDesignMeasure_cube_ae C θ hθ (2 ^ L) (by positivity)).mono (fun w hw => hw.1)) (dyadicPilotRow_pair_cap (ℓ := C.order) C θ hθ j L hj) ν hν
  have := integrable_finsetSum Finset.univ (fun r _ =>
    FieldLiftCovariance.weighted_kernel_statistic_integrable X ν (fun w => H w r) (hH r) t)
  have heq : (fun w => ν w * dyadicPilotErrorField C θ n j y m t w) =
      (fun w => ∑ r : Fin R, ν w * LiftL2.kernelStatistic (H w r) X t) := by
    funext w
    unfold dyadicPilotErrorField
    rw [← dyadicPolynomialPilot_centered_global C θ hθ n j w.1 y m
      (dyadicPilotRow j w.1 w.2) hdegree t]
    simp only [LiftL2.centeredKernelExpansion, zero_add, Finset.mul_sum]
    rfl
  rwa [heq]
theorem dyadicMultilevelErrorField_test_integral_sum  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (n J L ) (hJL : J ≤ L) (y ) (hy : |y| ≤ C.holderBound) (m )
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n)
    (ν )
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)))
    (t ) :
    (∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ (2 ^ L) (by positivity)) =
    ∑ j : Fin (J + 1), ∫ w, ν w * dyadicPilotErrorField C θ n j.val y (m j.val) t w
      ∂regularPairDesignMeasure θ (2 ^ L) (by positivity) := by
  unfold dyadicMultilevelErrorField
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum Finset.univ (fun j _ =>
    dyadicPilotErrorField_weighted_integrable C θ hθ n j.val L
      ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy (m j.val) (hdegree j) ν hν t)
theorem dyadicMultilevelErrorField_test_moment_facts  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (n J L ) (hJL : J ≤ L) (y ) (hy : |y| ≤ C.holderBound) (m )
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n)
    (ν )
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity))) :
    MemLp (fun t => ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ (2 ^ L) (by positivity)) 2 (sampleLaw θ n) ∧
    (∫ t, ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ (2 ^ L) (by positivity) ∂sampleLaw θ n) = 0 := by
  let := sampleLaw_isProbability C θ hθ n
  have hf (j : Fin (J + 1)) := dyadicPilotErrorField_test_moment_facts C θ hθ n j.val L
    ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy (m j.val) (hdegree j) ν hν
  simp_rw [dyadicMultilevelErrorField_test_integral_sum C θ hθ n J L hJL y hy m hdegree ν hν]
  refine ⟨memLp_finsetSum _ (fun j _ => (hf j).1), ?_⟩
  rw [integral_finsetSum Finset.univ (fun j _ => (hf j).1.integrable (by norm_num))]
  exact Finset.sum_eq_zero (fun j _ => (hf j).2)
theorem dyadicMultilevelErrorField_joint_measurable  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (n J y m)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) :
    Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicMultilevelErrorField C θ n J y m t.1 t.2) := by
  have h_dyadicPolynomialPilot_centered_field_measurable (j) (m) (row) (hrow : Measurable row) (hdegree : m + anchoredDimension d C.order + 1 ≤ n) : Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicPolynomialPilot C n j t.2.1 y m (row t.2) t.1 -
      incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
        (anchoredFinTransport d C.order) y m (row t.2)
          (dyadicIncrementRawMean θ j t.2.1)) := by
    let R := m + anchoredDimension d C.order + 1
    let H (w : Covariate d × Covariate d) (r : Fin R) :=
      dyadicIncrementKernel C θ j w.1 y m (row w) (r.val + 1)
    have hH (r : Fin R) : Measurable (fun w => H w r) :=
      dyadicIncrementKernel_field_measurable C θ hθ j y m (r.val + 1) row hrow
    have hX (i : Fin n) : Measurable (fun z : Fin n → Observation d =>
        incrementGlobalVector (ℓ := C.order) j (z i) - incrementGlobalMean θ j) :=
      ((incrementGlobalVector_measurable j).comp (measurable_pi_apply i)).sub measurable_const
    have h := centeredKernelExpansion_field_measurable H hH _ hX
    have heq : (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
        LiftL2.centeredKernelExpansion 0 (H t.2)
          (fun i z => incrementGlobalVector j (z i) - incrementGlobalMean θ j) t.1) =
        (fun t => dyadicPolynomialPilot C n j t.2.1 y m (row t.2) t.1 -
          incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) y m (row t.2)
              (dyadicIncrementRawMean θ j t.2.1)) := by
      funext t
      exact dyadicPolynomialPilot_centered_global C θ hθ n j t.2.1 y m (row t.2) hdegree t.1
    rwa [heq] at h
  have hm := Finset.measurable_sum Finset.univ (fun (j : Fin (J + 1)) _ =>
    (h_dyadicPolynomialPilot_centered_field_measurable j.val (m j.val) (fun w => dyadicPilotRow j.val w.1 w.2) (dyadicPilotRow_field_measurable j.val) (hdegree j)))
  convert hm using 1
  funext t
  simp only [dyadicMultilevelErrorField]
  rfl
theorem dyadicMultilevelErrorField_envelope_test_moment_facts  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (n J L ) (hJL : J ≤ L) (y ) (hy : |y| ≤ max C.holderBound 1) (m )
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n)
    (ν )
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity))) :
    MemLp (fun t => ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ (2 ^ L) (by positivity)) 2 (sampleLaw θ n) ∧
    (∫ t, ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ (2 ^ L) (by positivity) ∂sampleLaw θ n) = 0 := by
  letI : Nonempty (AnchoredIndex d (pilotModelConstants C).order) :=
    inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  exact dyadicMultilevelErrorField_test_moment_facts (pilotModelConstants C) θ
    (admissible_pilotModelConstants C θ hθ) n J L hJL y hy m hdegree ν hν
theorem dyadicMultilevelErrorField_envelope_weighted_integrable  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ ) (hθ : Admissible C θ)
    (n J L ) (hJL : J ≤ L) (y ) (hy : |y| ≤ max C.holderBound 1) (m )
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n)
    (ν )
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)))
    (t ) :
    Integrable (fun w => ν w * dyadicMultilevelErrorField C θ n J y m t w)
      (regularPairDesignMeasure θ (2 ^ L) (by positivity)) := by
  letI : Nonempty (AnchoredIndex d (pilotModelConstants C).order) :=
    inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  have hi (j : Fin (J + 1)) := dyadicPilotErrorField_weighted_integrable (pilotModelConstants C) θ
    (admissible_pilotModelConstants C θ hθ) n j.val L ((Nat.le_of_lt_succ j.isLt).trans hJL)
      y hy (m j.val) (hdegree j) ν hν t
  convert (integrable_finsetSum Finset.univ (fun j _ => hi j)) using 1
  funext w
  simp only [dyadicMultilevelErrorField, Finset.mul_sum]
  rfl
end NearlyMinimax
end
open Filter MeasureTheory Set Matrix ProbabilityTheory MvPolynomial
open scoped Topology RealInnerProductSpace BigOperators Matrix.Norms.L2Operator ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
variable {ell : ℝ}
def paperUpperVarpi  (C : ModelConstants d) : ℝ :=
  (d - 4 * C.smoothness) / (d * (d + 4))
def paperUpperEta  (C : ModelConstants d) : ℝ :=
  2 * (d + 4 * C.smoothness) / (d * (d + 4))
def paperUpperSaddle  (C : ModelConstants d) : ℝ :=
  upperSaddleCoefficient C.smoothness d (paperTau C)
def paperUpperShift  (C : ModelConstants d) : ℝ :=
  1 + 2 * (paperUpperEta C + 2) / paperDegreeSlope C
def paperUpperRiskDepthCoefficient  (C : ModelConstants d) : ℝ :=
  2 * (C.smoothness - 1) / (d + 4)
theorem paperUpperEta_pos  (C : ModelConstants d) : 0 < paperUpperEta C := by
  have : 0 < d := Nat.cast_pos.mpr C.dimension_pos
  have := C.smoothness_pos
  unfold paperUpperEta
  positivity
theorem paperDegreeSlope_pos  (C : ModelConstants d) (hs : 1 < C.smoothness) :
    0 < paperDegreeSlope C := div_pos (paperSpatialExponent_pos C hs) (paperTau_pos C)
theorem paperDegreeReserve_pos  (C : ModelConstants d) (hs : 1 < C.smoothness) :
    0 < paperDegreeReserve C := div_pos (by positivity) (paperSpatialExponent_pos C hs)
theorem paperUpperSaddle_pos  (C : ModelConstants d) (hreg : highSmoothnessRegime C) :
    0 < paperUpperSaddle C := by
  have : 0 < d := Nat.cast_pos.mpr C.dimension_pos
  have : 0 < C.smoothness - 1 := sub_pos.mpr hreg.1
  have  := sub_pos.mpr hreg.2
  have := paperTau_pos C
  unfold paperUpperSaddle upperSaddleCoefficient
  positivity
theorem paper_upper_saddle_budget_identity  (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) :
    paperDegreeSlope C * paperUpperSaddle C ^ 2 / 4 = 2 * paperUpperVarpi C := by
  have : d ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
  have : d + 4 ≠ 0 := by positivity
  have hsp  := sub_pos.mpr hreg.1
  have  := hsp.ne'
  have := paperTau_pos C
  have : 0 < d - 4 * C.smoothness := sub_pos.mpr hreg.2
  unfold paperDegreeSlope paperSpatialExponent paperUpperSaddle upperSaddleCoefficient paperUpperVarpi
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  ring
theorem paper_spatial_reserve_identity  (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (L T ) :
    2 * spatialBalanceLog C.smoothness d L T + 2 / d * (L + T) =
      -2 * paperUpperVarpi C * L + paperUpperEta C * T := by
  have : d ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
  have : d + 4 ≠ 0 := by positivity
  unfold spatialBalanceLog paperUpperVarpi paperUpperEta
  field_simp
  ring
def dyadicLevelFromLogSide (ell : ℝ) : ℕ := Nat.ceil (-ell / Real.log 2)
def dyadicRoundedLogSide (ell : ℝ) : ℝ := -Real.log 2 * dyadicLevelFromLogSide ell 
def dyadicRoundedSide (ell : ℝ) : ℝ := Real.exp (dyadicRoundedLogSide ell)
theorem dyadicRoundedLogSide_bounds  (hell : ell ≤ 0) :
    ell - Real.log 2 < dyadicRoundedLogSide ell ∧ dyadicRoundedLogSide ell ≤ ell := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg (neg_nonneg.mpr hell) hl.le)) hl
  have hhi := mul_le_mul_of_nonneg_right (Nat.le_ceil (-ell / Real.log 2)) hl.le
  rw [div_mul_cancel₀ _ hl.ne'] at hhi
  rw [add_mul, div_mul_cancel₀ _ hl.ne', one_mul] at hlo
  unfold dyadicRoundedLogSide dyadicLevelFromLogSide
  constructor <;> linarith only [hlo, hhi]
theorem dyadicRoundedSide_eq_inv_pow (ell ) :
    dyadicRoundedSide ell = (2 ^ dyadicLevelFromLogSide ell)⁻¹ := by
  unfold dyadicRoundedSide dyadicRoundedLogSide
  rw [neg_mul, Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
theorem dyadicRoundedSide_bounds  (hell : ell ≤ 0) :
    Real.exp ell / 2 < dyadicRoundedSide ell ∧ dyadicRoundedSide ell ≤ Real.exp ell := by
  obtain ⟨hlo, hhi⟩ := dyadicRoundedLogSide_bounds hell
  constructor
  · have h := Real.exp_lt_exp.mpr hlo
    rw [Real.exp_sub, Real.exp_log (by norm_num)] at h
    exact h
  · exact Real.exp_le_exp.mpr hhi
theorem dyadicRoundedLevel_ge  {j : ℕ}
    (hguard : ell + Real.log 2 * (j : ℝ) ≤ 0) : j ≤ dyadicLevelFromLogSide ell := by
  have hj : j ≤ -ell / Real.log 2 := (le_div_iff₀ (Real.log_pos (by norm_num))).mpr (by linarith only [hguard])
  exact_mod_cast hj.trans (Nat.le_ceil (-ell / Real.log 2))
theorem dyadicRounded_noise_bound {ell d : ℝ} (hell : ell ≤ 0) (hd : 0 ≤ d) (L ) :
    Real.exp (-L - d / 2 * dyadicRoundedLogSide ell) ≤
      Real.exp (d / 2 * Real.log 2) * Real.exp (-L - d / 2 * ell) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [mul_le_mul_of_nonneg_left ((dyadicRoundedLogSide_bounds hell).1.le) (by positivity : 0 ≤ d / 2)]
def paperAllocatedDepth  (C : ModelConstants d) (H x : ℝ) : ℝ :=
  roundedTerminalDepth (paperDyadicStep C) (Real.log x)
    (candidateTerminalDepth (paperUpperSaddle C) (paperUpperShift C) H (paperDegreeReserve C) x)
def paperAllocatedLogSide  (C : ModelConstants d) (H x : ℝ) : ℝ :=
  spatialBalanceLog C.smoothness d (Real.log x) (paperAllocatedDepth C H x)
def paperAllocatedFinestLevel  (C : ModelConstants d) (H x : ℝ) : ℕ :=
  dyadicLevelFromLogSide (paperAllocatedLogSide C H x)
def paperAllocatedSide  (C : ModelConstants d) (H x : ℝ) : ℝ :=
  dyadicRoundedSide (paperAllocatedLogSide C H x)
def paperAllocatedRiskScale  (C : ModelConstants d) (H x : ℝ) : ℝ :=
  Real.exp (-rateExponent C.smoothness d * Real.log x -
    paperUpperRiskDepthCoefficient C * paperAllocatedDepth C H x)
theorem paperAllocatedDepth_eq_level {d : ℕ} (C : ModelConstants d) (H x : ℝ) :
    paperAllocatedDepth C H x = paperDyadicStep C *
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ) - Real.log x := rfl
theorem eventually_paper_allocated_depth_le_width {d : ℕ} (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H) :
    ∀ᶠ x : ℝ in atTop, paperAllocatedDepth C H x ≤
      allocationWidth (paperUpperSaddle C) (paperUpperShift C) x := by
  have hw := allocationWidth_tendsto_atTop (paperUpperSaddle_pos C hreg) (paperUpperShift C)
  filter_upwards [hw.eventually (eventually_ge_atTop ↑2),
    (hw.const_mul_atTop hH).eventually (eventually_ge_atTop ↑1),
    eventually_terminal_cell_log_nonneg (paperUpperSaddle_pos C hreg) hH
      (paperUpperShift C) (paperDegreeReserve C)] with x hS hHS hLT
  have ht := (roundedTerminalDepth_bounds (paperDyadicStep_pos C) hLT).2
  unfold candidateTerminalDepth at ht
  exact ht.trans (by linarith only [Real.log_nonneg hHS, mul_nonneg (paperDegreeReserve_pos C hreg.1).le (Real.log_nonneg (by linarith only [hS]))])
theorem eventually_paper_allocated_grid_guard  (C : ModelConstants d)
    (hreg : highSmoothnessRegime C)  (hH : 0 < H) :
    ∀ᶠ x : ℝ in atTop,
      paperAllocatedLogSide C H x ≤ 0 ∧
      paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x ≤
        paperAllocatedFinestLevel C H x := by
  filter_upwards [(allocationWidth_tendsto_atTop (paperUpperSaddle_pos C hreg) (paperUpperShift C)).eventually (eventually_ge_atTop ↑2),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ↑0),
    eventually_paper_allocated_depth_le_width C hreg hH] with x hS hL hT
  have hb := quadratic_allocation_budget (paperDegreeSlope_pos C hreg.1)
    (show 0 ≤ paperUpperEta C + 2 by linarith only [paperUpperEta_pos C])
    (show 0 ≤ allocationWidth (paperUpperSaddle C) (paperUpperShift C) x by linarith only [hS])
    (show allocationWidth (paperUpperSaddle C) (paperUpperShift C) x =
      paperUpperSaddle C * Real.sqrt (Real.log x) -
        (1 + 2 * (paperUpperEta C + 2) / paperDegreeSlope C) by rfl)
  have hbase : paperDegreeSlope C * (paperUpperSaddle C * Real.sqrt (Real.log x)) ^ 2 / 4 =
      2 * paperUpperVarpi C * Real.log x := by
    rw [mul_pow, Real.sq_sqrt hL]
    calc
      _ = (paperDegreeSlope C * paperUpperSaddle C ^ 2 / 4) * Real.log x := by ring
      _ = _ := by rw [paper_upper_saddle_budget_identity C hreg]
  rw [hbase] at hb
  have hm := mul_le_mul_of_nonneg_left hT (paperUpperEta_pos C).le
  have hquad : 0 ≤ paperDegreeSlope C *
      (allocationWidth (paperUpperSaddle C) (paperUpperShift C) x) ^ 2 / 4 := by
    exact div_nonneg (mul_nonneg (paperDegreeSlope_pos C hreg.1).le (sq_nonneg _)) (by norm_num)
  have hn : -2 * paperUpperVarpi C * Real.log x +
      paperUpperEta C * paperAllocatedDepth C H x ≤ 0 := by
    nlinarith only [hb, hm, hquad, hS]
  rw [← paper_spatial_reserve_identity C hreg] at hn
  have : 0 < ↑d := Nat.cast_pos.mpr C.dimension_pos
  have hlevel : Real.log x + paperAllocatedDepth C H x =
      paperDyadicStep C * (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ) := by
    rw [paperAllocatedDepth_eq_level]
    ring
  rw [hlevel] at hn
  have hlog : 2 / ↑d * (paperDyadicStep C *
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ)) =
      2 * (Real.log 2 * (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ)) := by
    unfold paperDyadicStep
    field_simp
  rw [hlog] at hn
  have hg : paperAllocatedLogSide C H x + Real.log 2 *
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ) ≤ 0 := by
    change spatialBalanceLog C.smoothness d (Real.log x) (paperAllocatedDepth C H x) + _ ≤ 0
    linarith only [hn]
  have hnonneg : 0 ≤ Real.log 2 *
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x : ℝ) :=
    mul_nonneg (Real.log_pos (by norm_num)).le (Nat.cast_nonneg _)
  exact ⟨by linarith only [hg, hnonneg], dyadicRoundedLevel_ge hg⟩
theorem uniform_domain_admissible_dyadicPopulationCoefficients_supported_bound  (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ Cp, 0 < Cp ∧ ∀ Udom θ, Admissible (C.withDomain Udom) θ →
      ∀ J Jh, J ≤ Jh → ∀ m,
      ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
        sameLabelKernel (regularGridCell (2 ^ Jh) (by positivity)) w ≠ 0 →
          ‖dyadicPopulationCoefficients C θ J m w‖ ≤ Cp := by
  have h_uniform_domain_admissible_dyadicPopulationCoefficients_uniform_bound : ∃ Cp, 0 < Cp ∧ ∀ Udom θ, Admissible (C.withDomain Udom) θ →
      ∀ J m, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell J x → ‖dyadicPopulationCoefficients C θ J m (x, y)‖ ≤ Cp := by
    have h_uniform_domain_admissible_dyadicPopulationPilotSum_uniform_bound : ∃ R, 0 ≤ R ∧ ∀ Udom θ, Admissible (C.withDomain Udom) θ →
        ∀ J m, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
        y ∈ dyadicPilotCell J x → ∀ t, |dyadicPopulationPilotSum C θ J m t (x, y)| ≤ R := by
      have h_uniform_domain_admissible_dyadicPopulationRawPolynomial_uniform_bound : ∃ B, 0 < B ∧ ∀ Udom θ, Admissible (C.withDomain Udom) θ →
        ∀ j, ∀ x ∈ unitCube d, ∀ t m,
          ‖dyadicPopulationRawPolynomial C θ j x t m‖ ≤ B := by
        let := anchoredIndex_nonempty_of_one_lt_smoothness C hs
        have h_uniform_domain_admissible_dyadicPopulationPolynomial_uniform_bound : ∃ B, 0 < B ∧ ∀ Udom θ, Admissible (C.withDomain Udom) θ →
            ∀ j, ∀ x ∈ unitCube d, ∀ y, |y| ≤ 1 → ∀ m,
              ‖dyadicPopulationPolynomial C θ j x y m‖ ≤ B := by
          obtain ⟨W, hW, hmom⟩ := uniform_domain_admissible_dyadicFinPilotMoments_uniform_bound C
          obtain ⟨B, A, hB, hA, hder⟩ := anchored_population_inverse_derivatives
            (d := d) (ℓ := C.order) C.densityLower C.densityUpper W 1 C.densityLower_pos
            (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le zero_le_one
          refine ⟨B, hB, ?_⟩
          intro Udom θ hθ j x hx y hy m
          let q := if j = 0 then (fun _ => 1) else dyadicNormalizedDensity θ (j - 1) x
          have hqm : Measurable q := by
            by_cases hj : j = 0
            · simp [q, hj, ModelConstants.withDomain]
            · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ (j - 1) x
          have hqb : ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ q w ∧ q w ≤ C.densityUpper := by
            by_cases hj : j = 0
            · exact Filter.Eventually.of_forall (fun _ => by
                simpa [q, hj, ModelConstants.withDomain] using And.intro C.densityLower_lt_one.le C.one_lt_densityUpper.le)
            · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ (j - 1) x
          have hV (t : Bool) : ‖(if j = 0 then (0 : Bool → Fin (anchoredDimension d C.order) → ℝ)
              else dyadicFinPilotMoments θ (j - 1) x) t‖ ≤ W := by
            by_cases hj : j = 0
            · simpa [hj] using hW.le
            · simpa only [hj, ite_false] using hmom Udom θ hθ (j - 1) x hx t
          have hd := hder (dyadicNormalizedAnchor j x) (dyadicNormalizedAnchor (j - 1) x)
            (gridNormalizedAnchor_mem_cube (2 ^ j) (by positivity) x hx)
            (gridNormalizedAnchor_mem_cube (2 ^ (j - 1)) (by positivity) x hx)
            (dyadicNormalizedDensity θ j x) q
            (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x) hqm
            (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x) hqb
            (dyadicFinPilotMoments θ j x) (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)
            (hmom Udom θ hθ j x hx) hV y hy m 0 (fun i => Fin.elim0 i)
          rw [← dyadicIncrementRawMean_eq_with_virtual_parent (C.withDomain Udom) θ hθ j x hx] at hd
          simpa only [dyadicPopulationPolynomial, iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one,
            Fin.prod_univ_zero] using hd
        obtain ⟨B, hB, hb⟩ := h_uniform_domain_admissible_dyadicPopulationPolynomial_uniform_bound
        refine ⟨2 * B, mul_pos (by norm_num) hB, ?_⟩
        intro Udom θ hθ j x hx t m
        have h0 := hb Udom θ hθ j x hx 0 (by norm_num) m
        have := hb Udom θ hθ j x hx 1 (by norm_num) m
        have he0 : dyadicPopulationRawPolynomial C θ j x false m = dyadicPopulationPolynomial C θ j x 0 m := by
          rw [dyadicPopulationPolynomial_affine, zero_smul, sub_zero]
        cases t
        · have hf : ‖dyadicPopulationRawPolynomial C θ j x false m‖ ≤ B := by rw [he0]; exact h0
          exact hf.trans (by linarith)
        · have he : dyadicPopulationRawPolynomial C θ j x true m =
              dyadicPopulationPolynomial C θ j x 0 m - dyadicPopulationPolynomial C θ j x 1 m := by
            rw [dyadicPopulationPolynomial_affine, dyadicPopulationPolynomial_affine]
            simp only [zero_smul, sub_zero, one_smul]
            abel
          rw [he]
          exact (norm_sub_le _ _).trans (by linarith)
      obtain ⟨B, hB, hb⟩ := h_uniform_domain_admissible_dyadicPopulationRawPolynomial_uniform_bound
      let R := 2 * anchoredDimension d C.order  * Real.sqrt d * B
      refine ⟨R, by dsimp [R]; positivity, ?_⟩
      intro Udom θ hθ J m x hx y hy hcell t
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑ j ∈ Finset.range (J + 1), (∑ i, |dyadicPilotRow (ℓ := C.order) j x y i|) * B := by
          apply Finset.sum_le_sum
          intro j hj
          exact (finite_row_abs_dot_le_pi_norm _ _).trans
            (mul_le_mul_of_nonneg_left (hb Udom θ hθ j x hx t (m j)) (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
        _ = (∑ j ∈ Finset.range (J + 1), ∑ i, |dyadicPilotRow (ℓ := C.order) j x y i|) * B := by
          rw [Finset.sum_mul]
        _ ≤ R := mul_le_mul_of_nonneg_right (dyadicPilotRow_total_abs_le J x y hx hy hcell) hB.le
    obtain ⟨R, hR, hb⟩ := h_uniform_domain_admissible_dyadicPopulationPilotSum_uniform_bound
    refine ⟨Real.sqrt 3 * (1 + R), mul_pos (by positivity) (by positivity), ?_⟩
    intro Udom θ hθ J m x hx y hy hc
    have hcoord (i : Fin 3) : |dyadicPopulationCoefficients C θ J m (x, y) i| ≤ 1 + R := by
      fin_cases i
      · simpa [dyadicPopulationCoefficients] using hR
      · change |-1 + dyadicPopulationPilotSum C θ J m true (x, y)| ≤ 1 + R
        exact (abs_add_le _ _).trans (by simpa using add_le_add_left (hb Udom θ hθ J m x hx y hy hc true) 1)
      · change |-dyadicPopulationPilotSum C θ J m false (x, y)| ≤ 1 + R
        rw [abs_neg]
        exact (hb Udom θ hθ J m x hx y hy hc false).trans (by linarith)
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc
      (∑ i : Fin 3, ‖dyadicPopulationCoefficients C θ J m (x, y) i‖ ^ 2) ≤ ∑ _i : Fin 3, (1 + R) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hcoord i) 2
      _ = 3 * (1 + R) ^ 2 := by simp
      _ = (Real.sqrt 3 * (1 + R)) ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
  obtain ⟨Cp, hCp, hb⟩ := h_uniform_domain_admissible_dyadicPopulationCoefficients_uniform_bound
  refine ⟨Cp, hCp, ?_⟩
  intro Udom θ hθ J Jh hJJh m
  let := designLaw_isProbability (C.withDomain Udom) θ hθ
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := designLaw θ) (ν := designLaw θ)).ae
      (designLaw_cube_ae θ),
    (Measure.quasiMeasurePreserving_snd (μ := designLaw θ) (ν := designLaw θ)).ae
      (designLaw_cube_ae θ)] with w hx hy hw
  have hc : w.2 ∈ dyadicPilotCell Jh w.1 := by
    change regularGridCell (2 ^ Jh) (by positivity) w.2 =
      regularGridCell (2 ^ Jh) (by positivity) w.1
    by_contra h
    apply hw
    simp [sameLabelKernel, Ne.symm h]
  exact hb Udom θ hθ J m w.1 hx w.2 hy (dyadicPilotCell_subset_coarser J Jh hJJh w.1 hc)
theorem uniform_domain_allocated_population_pair_witnesses  (C : ModelConstants d)
    (hreg : highSmoothnessRegime C)  (hH : 0 < H) :
    ∃ Cp B, 0 < Cp ∧ 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      ∀ Udom θ, Admissible (C.withDomain Udom) θ →
      let J := paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n
      let m := paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) H n
      let Jh := paperAllocatedFinestLevel C H n
      Measurable (dyadicPopulationCoefficients C θ J m) ∧
      (∀ w, dyadicPopulationCoefficients C θ J m w 0 = 1) ∧
      (∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
        sameLabelKernel (regularGridCell (2 ^ Jh) (by positivity)) w ≠ 0 →
          ‖dyadicPopulationCoefficients C θ J m w‖ ≤ Cp) ∧
      (∀ᵐ w ∂regularPairDesignMeasure θ (2 ^ Jh) (by positivity),
        |⟪dyadicPopulationCoefficients C θ J m w,
          pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤
          B * Real.sqrt d * paperAllocatedSide C H n *
            (dyadicPilotScale d J) ^ (-paperSpatialExponent C)) := by
  obtain ⟨Cp, hCp, hc⟩ := uniform_domain_admissible_dyadicPopulationCoefficients_supported_bound C hreg.1
  have h_uniform_domain_eventually_allocated_population_pair_residual (a) (offset) (ha : 0 < a) : ∃ B, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      ∀ Udom θ, Admissible (C.withDomain Udom) θ →
      ∀ Jh, paperDyadicTerminalLevel C a offset H n ≤ Jh →
      ∀ᵐ w ∂regularPairDesignMeasure θ (2 ^ Jh) (by positivity),
        |⟪dyadicPopulationCoefficients C θ (paperDyadicTerminalLevel C a offset H n)
            (paperDyadicApproximationDegree C a offset H n) w,
          pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤
          B * Real.sqrt d * (2 ^ Jh)⁻¹ *
            (dyadicPilotScale d (paperDyadicTerminalLevel C a offset H n)) ^ (-paperSpatialExponent C) := by
    have h_uniform_domain_admissible_dyadicPopulationResidual_bound (hs : 1 < C.smoothness) : ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
        ∀ J : ℕ, ∀ m : ℕ → ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
        y ∈ dyadicPilotCell J x →
          |dyadicPopulationResidual C θ J m x y| ≤
            E * euclideanNorm (y - x) * dyadicPopulationBiasBudget C J m := by
      let := anchoredIndex_nonempty_of_one_lt_smoothness C hs
      have h_uniform_domain_admissible_dyadicPopulationFit_physical_error : ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
          ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d, y ∈ dyadicPilotCell j x →
          |θ.regression y - θ.regression x - dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ j x| ≤
            E * euclideanNorm (y - x) * ((↑2 ^ j)⁻¹) ^ (C.smoothness - 1) := by
        have h_uniform_domain_admissible_dyadicPopulationFit_spatial_error : ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
            ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ w ∈ unitCube d,
            |dyadicRegressionDifference θ j x w - anchoredFitPolynomial (dyadicNormalizedAnchor j x)
              (dyadicPopulationFit (ℓ := C.order) θ j x) w| ≤
                E * ((↑2 ^ j)⁻¹) ^ C.smoothness * euclideanNorm (w - dyadicNormalizedAnchor j x) := by
          obtain ⟨D, hD, hpoint⟩ := anchoredPopulationFit_pointwise_error (d := d) (ℓ := C.order)
            C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
          let T := ↑d ^ C.order * 2 * C.holderBound / C.order.factorial
          have := C.holderBound_pos
          have : 0 ≤ T := by positivity
          let E := max 1 (T * max 1 ((Real.sqrt ↑d) ^ C.smoothness) + D * (taylorErrorFactor C * C.holderBound))
          refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
          intro Udom θ hθ j x hx w hw
          obtain ⟨c, hc⟩ := admissible_dyadic_taylor_family (C.withDomain Udom) θ hθ x hx
          let R := taylorErrorFactor C * C.holderBound * ((↑2 ^ j)⁻¹) ^ C.smoothness
          have hR : 0 ≤ R := mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le)
            (Real.rpow_nonneg (by positivity) _)
          have hu : dyadicNormalizedAnchor j x ∈ unitCube d := gridNormalizedAnchor_mem_cube _ (by positivity) x hx
          have hp := hpoint _ hu _ _ (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x)
            (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x) (dyadicRegressionDifference_continuousOn (C.withDomain Udom) θ hθ j x)
            (dyadicTaylorCoefficients c j) R hR (fun v hv => (hc j v hv).1) w hw
          rw [dyadicPopulationFit_eq_normalized (C.withDomain Udom) θ hθ]
          apply hp.trans
          have h := euclideanNorm_le_coordinate_radius (w - dyadicNormalizedAnchor j x) 1 (by norm_num)
            (fun i => by
              change |w i - dyadicNormalizedAnchor j x i| ≤ 1
              exact abs_le.mpr ⟨by linarith [(hw i).1, (hu i).2], by linarith [(hw i).2, (hu i).1]⟩)
          obtain ⟨γ⟩ := (inferInstance : Nonempty (AnchoredIndex d C.order))
          have ho  := γ.property.1.trans_le γ.property.2
          have hor : (1 : ℝ) ≤ C.order := by exact_mod_cast ho
          have hs := hor.trans C.order_lt.le
          have hr0 : 0 ≤ euclideanNorm (w - dyadicNormalizedAnchor j x) := by unfold euclideanNorm; positivity
          have := bounded_rpow_le_linear _ _ _ hr0 (by simpa only [mul_one] using h) hs
          calc
            _ ≤ T * ((↑2 ^ j)⁻¹) ^ C.smoothness *
                euclideanNorm (w - dyadicNormalizedAnchor j x) ^ C.smoothness +
                D * R * euclideanNorm (w - dyadicNormalizedAnchor j x) := add_le_add (hc j w hw).2 le_rfl
            _ ≤ T * ((↑2 ^ j)⁻¹) ^ C.smoothness *
                (max 1 ((Real.sqrt ↑d) ^ C.smoothness) * euclideanNorm (w - dyadicNormalizedAnchor j x)) +
                D * R * euclideanNorm (w - dyadicNormalizedAnchor j x) := by gcongr
            _ = (T * max 1 ((Real.sqrt ↑d) ^ C.smoothness) + D * (taylorErrorFactor C * C.holderBound)) *
                ((↑2 ^ j)⁻¹) ^ C.smoothness * euclideanNorm (w - dyadicNormalizedAnchor j x) := by dsimp [R]; ring
            _ ≤ E * ((↑2 ^ j)⁻¹) ^ C.smoothness * euclideanNorm (w - dyadicNormalizedAnchor j x) := by
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
                (Real.rpow_nonneg (by positivity) _)) hr0
        obtain ⟨E, hE, hfit⟩ := h_uniform_domain_admissible_dyadicPopulationFit_spatial_error
        refine ⟨E, hE, ?_⟩
        intro Udom θ hθ j x hx y hy hcell
        have hw : dyadicNormalizedAnchor j y ∈ unitCube d := gridNormalizedAnchor_mem_cube _ (by positivity) y hy
        have he := dyadicCellAffine_same_cell j x y hcell
        have h := hfit Udom θ hθ j x hx _ hw
        rw [dyadicPopulationFit_physical_evaluation j x y hcell] at h
        unfold dyadicRegressionDifference at h
        rw [he] at h
        apply h.trans_eq
        have hd := dyadicCellAffine_euclidean_distance j x (dyadicNormalizedAnchor j y)
        rw [he] at hd
        rw [mul_assoc, positive_rpow_times_distance _ _ _ (by positivity), ← hd]
        ring
      obtain ⟨A, hA, hfit⟩ := h_uniform_domain_admissible_dyadicPopulationFit_physical_error
      have h_uniform_domain_admissible_dyadic_polynomial_row_error : ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
          ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d, y ∈ dyadicPilotCell j x → ∀ m : ℕ,
          |dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) m -
            dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationIncrement (ℓ := C.order) θ x j| ≤
          E * euclideanNorm (y - x) * ((↑2 ^ j)⁻¹) ^ (C.smoothness - 1) *
            ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-↑m * paperTau C) := by
        have h_uniform_domain_admissible_dyadic_increment_polynomial_error : ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
            ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ m : ℕ,
            ‖(EuclideanSpace.equiv (Fin (anchoredDimension d C.order)) ℝ).symm
              (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
                (anchoredFinTransport d C.order) (θ.regression x) m (dyadicIncrementRawMean θ j x) -
                  anchoredFinVector (dyadicPopulationIncrement θ x j))‖ ≤
              E * ((↑2 ^ j)⁻¹) ^ C.smoothness * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
                Real.exp (-↑m * exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower))) := by
          obtain ⟨χ, hχ, hcond⟩ := anchoredFinSimilarityUnit_uniform_condition (d := d) (ℓ := C.order)
          have h_uniform_domain_admissible_dyadicPopulationIncrement_bound : ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
          ∀ x ∈ unitCube d, ∀ j : ℕ,
          ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x j)‖ ≤
            E * ((↑2 ^ j)⁻¹) ^ C.smoothness := by
            have h_uniform_domain_admissible_dyadicPopulationIncrement_root_bound : ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
                ∀ x ∈ unitCube d,
                ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x 0)‖ ≤ E := by
              obtain ⟨D, hD, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := C.order)
                C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
              let E := max 1 (D * (2 * C.holderBound))
              refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
              intro Udom θ hθ x hx
              have hres : ∀ w ∈ unitCube d, |dyadicRegressionDifference θ 0 x w -
                  anchoredFitPolynomial (dyadicNormalizedAnchor 0 x) (0 : AnchoredIndex d C.order → ℝ) w| ≤
                    2 * C.holderBound := by
                intro w hw
                simp only [anchoredFitPolynomial, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
                exact (abs_sub _ _).trans (by
                  have ha := admissible_regression_value_bound (C.withDomain Udom) θ hθ _ (dyadicCellAffine_mem_cube 0 x w hw)
                  have hb := admissible_regression_value_bound (C.withDomain Udom) θ hθ x hx
                  change |θ.regression (dyadicCellAffine 0 x w)| + |θ.regression x| ≤ _
                  dsimp [ModelConstants.withDomain] at ha hb
                  linarith)
              have h := hfit _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx) _ _
                (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ 0 x) (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ 0 x)
                (dyadicRegressionDifference_continuousOn (C.withDomain Udom) θ hθ 0 x) 0 (2 * C.holderBound)
                (mul_nonneg (by norm_num) C.holderBound_pos.le) hres
              change ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationFit θ 0 x)‖ ≤ E
              rw [dyadicPopulationFit_eq_normalized (C.withDomain Udom) θ hθ]
              simpa only [sub_zero, dyadicNormalizedAnchor, E] using h.trans (le_max_right 1 _)
            obtain ⟨E0, hE0, hroot⟩ := h_uniform_domain_admissible_dyadicPopulationIncrement_root_bound
            have h_uniform_domain_admissible_dyadicPopulationIncrement_successor_bound : ∃ E : ℝ, 0 < E ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
                ∀ x ∈ unitCube d, ∀ j : ℕ,
                ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x (j + 1))‖ ≤
                  E * ((↑2 ^ (j + 1))⁻¹) ^ C.smoothness := by
              have h_uniform_domain_admissible_dyadicPopulationFit_taylor_coefficients : ∃ D : ℝ, 0 < D ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
                  ∀ x ∈ unitCube d, ∃ c : AnchoredIndex d C.order → ℝ, ∀ j : ℕ,
                  ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm
                    (dyadicPopulationFit θ j x - dyadicTaylorCoefficients c j)‖ ≤
                      D * ((↑2 ^ j)⁻¹) ^ C.smoothness := by
                obtain ⟨D, hD, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := C.order)
                  C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
                let E := max 1 (D * taylorErrorFactor C * C.holderBound)
                refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
                intro Udom θ hθ x hx
                obtain ⟨c, hc⟩ := admissible_dyadic_taylor_family (C.withDomain Udom) θ hθ x hx
                refine ⟨c, ?_⟩
                intro j
                let R := taylorErrorFactor C * C.holderBound * ((↑2 ^ j)⁻¹) ^ C.smoothness
                have hR : 0 ≤ R := mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le)
                  (Real.rpow_nonneg (by positivity) _)
                rw [dyadicPopulationFit_eq_normalized (C.withDomain Udom) θ hθ]
                have h := hfit _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx)
                  _ _ (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x) (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x)
                  (dyadicRegressionDifference_continuousOn (C.withDomain Udom) θ hθ j x) (dyadicTaylorCoefficients c j)
                  R hR (fun w hw => (hc j w hw).1)
                apply h.trans
                calc
                  D * R = D * taylorErrorFactor C * C.holderBound * ((↑2 ^ j)⁻¹) ^ C.smoothness := by dsimp [R]; ring
                  _ ≤ E * ((↑2 ^ j)⁻¹) ^ C.smoothness :=
                    mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)
              obtain ⟨D, hD, hcoeff⟩ := h_uniform_domain_admissible_dyadicPopulationFit_taylor_coefficients
              let E := D * (1 + (1 / 2) * ↑2 ^ C.smoothness)
              refine ⟨E, mul_pos hD (by positivity), ?_⟩
              intro Udom θ hθ x hx j
              obtain ⟨c, hc⟩ := hcoeff Udom θ hθ x hx
              let e := fun i => dyadicPopulationFit θ i x - dyadicTaylorCoefficients c i
              rw [dyadicPopulationIncrement_error_identity θ x c j]
              have hsub : ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm
                  (e (j + 1) - anchoredTransport d C.order *ᵥ e j)‖ ≤
                  ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (e (j + 1))‖ +
                  ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (anchoredTransport d C.order *ᵥ e j)‖ := by
                simpa [EuclideanSpace.equiv] using norm_sub_le
                  ((EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (e (j + 1)))
                  ((EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (anchoredTransport d C.order *ᵥ e j))
              apply hsub.trans
              have ht := anchoredTransport_euclidean_norm (e j)
              have ht' := ht.trans (mul_le_mul_of_nonneg_left (hc j) (by norm_num : (0 : ℝ) ≤ 1 / 2))
              apply (add_le_add (hc (j + 1)) ht').trans_eq
              rw [dyadic_inverse_scale_succ j, Real.mul_rpow (by norm_num) (by positivity)]
              dsimp [E]
              ring
            obtain ⟨E1, hE1, hsucc⟩ := h_uniform_domain_admissible_dyadicPopulationIncrement_successor_bound
            refine ⟨max E0 E1, hE0.trans_le (le_max_left _ _), ?_⟩
            intro Udom θ hθ x hx j
            cases j with
            | zero => simpa using (hroot Udom θ hθ x hx).trans (le_max_left E0 E1)
            | succ j =>
              exact (hsucc Udom θ hθ x hx j).trans
                (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _))
          obtain ⟨D, hD, hinc⟩ := h_uniform_domain_admissible_dyadicPopulationIncrement_bound
          let E₀ := χ ^ 2 * C.densityUpper ^ (anchoredDimension d C.order + 1) *
            parentInverseErrorConstant C.densityLower C.densityUpper (anchoredDimension d C.order)
          let E := max 1 (E₀ * D)
          refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
          intro Udom θ hθ j x hx m
          let u := dyadicNormalizedAnchor j x
          let v := dyadicNormalizedAnchor (j - 1) x
          let p := dyadicNormalizedDensity θ j x
          let q := if j = 0 then (fun _ : Covariate d => ↑1) else dyadicNormalizedDensity θ (j - 1) x
          let U := dyadicFinPilotMoments (ℓ := C.order) θ j x
          let V := if j = 0 then 0 else dyadicFinPilotMoments (ℓ := C.order) θ (j - 1) x
          have hqmeas : Measurable q := by
            by_cases hj : j = 0
            · simpa [q, hj, ModelConstants.withDomain] using (measurable_const : Measurable (fun _ : Covariate d => ↑1))
            · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ (j - 1) x
          have hqb : ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ q w ∧ q w ≤ C.densityUpper := by
            by_cases hj : j = 0
            · exact Filter.Eventually.of_forall (fun _ => by
                simpa [q, hj, ModelConstants.withDomain] using And.intro C.densityLower_lt_one.le C.one_lt_densityUpper.le)
            · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ (j - 1) x
          have hparent : anchoredFinNormalizedGram (ℓ := C.order) v q =
              if j = 0 then 1 else dyadicFinPilotGram θ (j - 1) x := by
            by_cases hj : j = 0
            · simp [q, hj, anchoredFinNormalizedGram_one]
            · simp only [q, hj, ite_false]
              exact (dyadicFinPilotGram_eq_normalized (C.withDomain Udom) θ hθ (j - 1) x).symm
          have hactual : (anchoredFinNormalizedGram (ℓ := C.order) u p)⁻¹ *ᵥ
              (U false - θ.regression x • U true) - anchoredFinTransport d C.order *ᵥ
                ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - θ.regression x • V true)) =
                anchoredFinVector (dyadicPopulationIncrement θ x j) := by
            rw [hparent, ← dyadicFinPilotGram_eq_normalized (C.withDomain Udom) θ hθ j x]
            exact dyadicFinite_increment_eq_actual (C.withDomain Udom) θ hθ j x hx
          have he := anchoredNormalized_increment_error u v p q
            (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x) hqmeas
            C.densityLower C.densityUpper χ (D * ((↑2 ^ j)⁻¹) ^ C.smoothness)
            C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)
            (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x) hqb
            (hcond u (gridNormalizedAnchor_mem_cube _ (by positivity) x hx))
            U V (θ.regression x) (anchoredFinTransport d C.order) (by rw [hactual, anchoredFinVector_norm]; exact hinc Udom θ hθ x hx j) m
          rw [hactual] at he
          have hval : dyadicIncrementRawMean (ℓ := C.order) θ j x = fun a =>
              incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q) U V
                ((Fintype.equivFin (incrementVariables (anchoredDimension d C.order))).symm a) := by
            rw [dyadicIncrementRawMean_eq_population (C.withDomain Udom) θ hθ j x hx]
            have hcurrent : anchoredFinNormalizedGram (ℓ := C.order) u p = dyadicFinPilotGram θ j x :=
              (dyadicFinPilotGram_eq_normalized (C.withDomain Udom) θ hθ j x).symm
            simp only [dyadicIncrementPopulation, hparent, hcurrent]
            rfl
          rw [hval, incrementFinVector_eval_population]
          calc
            _ ≤ E₀ * (D * ((↑2 ^ j)⁻¹) ^ C.smoothness) * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
                Real.exp (-↑m * exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower))) := he
            _ = (E₀ * D) * ((↑2 ^ j)⁻¹) ^ C.smoothness * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
                Real.exp (-↑m * exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower))) := by ring
            _ ≤ E * ((↑2 ^ j)⁻¹) ^ C.smoothness * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
                Real.exp (-↑m * exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower))) := by
              gcongr
              exact le_max_right _ _
        obtain ⟨B, hB, herror⟩ := h_uniform_domain_admissible_dyadic_increment_polynomial_error
        let E := max 1 (B * (anchoredDimension d C.order : ℝ))
        refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
        intro Udom θ hθ j x hx y hy hcell m
        have hnorm := herror Udom θ hθ j x hx m
        rw [exteriorTau_sqrt_ratio C.densityLower C.densityUpper C.densityLower_pos
          (C.densityLower_lt_one.trans C.one_lt_densityUpper)] at hnorm
        change ‖(EuclideanSpace.equiv (Fin (anchoredDimension d C.order)) ℝ).symm
          (dyadicPopulationPolynomial C θ j x (θ.regression x) m -
            anchoredFinVector (dyadicPopulationIncrement θ x j))‖ ≤
          B * ((↑2 ^ j)⁻¹) ^ C.smoothness * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
            Real.exp (-↑m * paperTau C) at hnorm
        rw [← dyadicPilotRow_dot_coefficients, ← dotProduct_sub]
        apply (finite_row_abs_dot_le_euclidean_norm _ _).trans
        have hr := dyadicPilotRow_sum_abs_le_distance (ℓ := C.order) j x y hx hy hcell
        have : 0 ≤ euclideanNorm (y - x) := by unfold euclideanNorm; positivity
        calc
          _ ≤ (anchoredDimension d C.order : ℝ) * ↑2 ^ j * euclideanNorm (y - x) *
              (B * ((↑2 ^ j)⁻¹) ^ C.smoothness * ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
                Real.exp (-↑m * paperTau C)) := mul_le_mul hr hnorm (norm_nonneg _) (by positivity)
          _ = B * (anchoredDimension d C.order : ℝ) * euclideanNorm (y - x) *
              (↑2 ^ j * ((↑2 ^ j)⁻¹) ^ C.smoothness) *
                ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-↑m * paperTau C) := by ring
          _ = (B * (anchoredDimension d C.order : ℝ)) * euclideanNorm (y - x) *
              ((↑2 ^ j)⁻¹) ^ (C.smoothness - 1) *
                ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-↑m * paperTau C) := by
            rw [dyadic_scale_rpow_cancel]
          _ ≤ E * euclideanNorm (y - x) * ((↑2 ^ j)⁻¹) ^ (C.smoothness - 1) *
              ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-↑m * paperTau C) := by
            gcongr
            exact le_max_right _ _
      obtain ⟨B, hB, hpoly⟩ := h_uniform_domain_admissible_dyadic_polynomial_row_error
      let E := max A B
      refine ⟨E, hA.trans_le (le_max_left _ _), ?_⟩
      intro Udom θ hθ J m x hx y hy hcell
      have : 0 ≤ euclideanNorm (y - x) := by unfold euclideanNorm; positivity
      have heq : dyadicPopulationResidual C θ J m x y =
          θ.regression y - θ.regression x - dyadicAnchoredFeature J x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ J x +
          ∑ j ∈ Finset.range (J + 1), (dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationIncrement (ℓ := C.order) θ x j -
            dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)) := by
        rw [dyadicPopulationIncrement_telescope, Finset.sum_sub_distrib]
        unfold dyadicPopulationResidual
        ring
      rw [heq]
      apply (abs_add_le _ _).trans
      apply (add_le_add (hfit Udom θ hθ J x hx y hy hcell) (Finset.abs_sum_le_sum_abs _ _)).trans
      calc
        _ ≤ A * euclideanNorm (y - x) * ((↑2 ^ J)⁻¹) ^ (C.smoothness - 1) +
            ∑ j ∈ Finset.range (J + 1), B * euclideanNorm (y - x) *
              ((↑2 ^ j)⁻¹) ^ (C.smoothness - 1) * ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
                Real.exp (-(m j : ℝ) * paperTau C) := by
          apply add_le_add le_rfl
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_sub_comm]
          exact hpoly Udom θ hθ j x hx y hy
            (dyadicPilotCell_subset_coarser j J (by exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x hcell) (m j)
        _ ≤ E * euclideanNorm (y - x) * ((↑2 ^ J)⁻¹) ^ (C.smoothness - 1) +
            ∑ j ∈ Finset.range (J + 1), E * euclideanNorm (y - x) *
              ((↑2 ^ j)⁻¹) ^ (C.smoothness - 1) * ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
                Real.exp (-(m j : ℝ) * paperTau C) := by
          apply add_le_add
          · gcongr
            exact le_max_left _ _
          · apply Finset.sum_le_sum
            intro j _
            gcongr
            exact le_max_right _ _
        _ = E * euclideanNorm (y - x) * dyadicPopulationBiasBudget C J m := by
          unfold dyadicPopulationBiasBudget
          rw [mul_add, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          push_cast; ring
    obtain ⟨E, hE, he⟩ := (h_uniform_domain_admissible_dyadicPopulationResidual_bound hreg.1)
    have h_eventually_paper_dyadic_bias_budget : ∃ B, 0 < B ∧ ∀ᶠ n : ℝ in atTop,
        dyadicPopulationBiasBudget C (paperDyadicTerminalLevel C a offset H n)
          (paperDyadicApproximationDegree C a offset H n) ≤
        B * (dyadicPilotScale d (paperDyadicTerminalLevel C a offset H n)) ^ (-paperSpatialExponent C) := by
      have hθ := paperSpatialExponent_pos C hreg.1
      have hτ := paperTau_pos C
      obtain ⟨B, hB, hb⟩ := eventually_actual_allocation_bias_sum
        (anchoredDimension d C.order) (paperPolynomialDimension C) (paperDyadicStep C) a offset H
        (paperDegreeReserve C) (paperDegreeSlope C) (paperSpatialExponent C) (paperTau C)
        (paperDyadicStep_pos C) ha hH (div_pos hθ hτ) hθ hτ (by unfold paperDegreeSlope; exact mul_div_cancel₀ _ hτ.ne') (by unfold paperDegreeReserve; exact mul_div_cancel₀ _ hθ.ne')
      refine ⟨1 + B, by positivity, ?_⟩
      filter_upwards [hb] with n hn
      have h_dyadicPopulationBiasBudget_eq_scalar J (m : ℕ → ℕ) : dyadicPopulationBiasBudget C J m =
          (Real.exp (paperDyadicStep C * J)) ^ (-paperSpatialExponent C) +
          ∑ j ∈ Finset.range (J + 1), (Real.exp (paperDyadicStep C * j)) ^ (-paperSpatialExponent C) *
            ((m j ) + 1) ^ anchoredDimension d C.order * (Real.exp (-paperTau C)) ^ m j := by
        have h_dyadic_spatial_weight_eq j : ((2 ^ j)⁻¹) ^ (C.smoothness - 1) =
            (dyadicPilotScale d j) ^ (-paperSpatialExponent C) := by
          rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (dyadicPilotScale_pos d j), Real.log_inv]
          unfold dyadicPilotScale paperSpatialExponent
          rw [Real.log_pow, Real.log_pow, Real.log_pow]
          congr 1
          have : d ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
          field_simp
        unfold dyadicPopulationBiasBudget
        simp_rw [h_dyadic_spatial_weight_eq, dyadicPilotScale_eq_exp C, exp_negative_nat_eq_pow]
      rw [h_dyadicPopulationBiasBudget_eq_scalar, dyadicPilotScale_eq_exp C]
      change (Real.exp (paperDyadicStep C * paperDyadicTerminalLevel C a offset H n )) ^ (-paperSpatialExponent C) +
          _ ≤ (1 + B) * (Real.exp (paperDyadicStep C * paperDyadicTerminalLevel C a offset H n )) ^ (-paperSpatialExponent C)
      exact (add_le_add le_rfl hn).trans_eq (by unfold paperDyadicTerminalLevel; ring)
    obtain ⟨B, hB, hb⟩ := h_eventually_paper_dyadic_bias_budget
    refine ⟨E * B, mul_pos hE hB, ?_⟩
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hb] with n hn
    intro Udom θ hθ Jh hJJh
    have h_regularPairDesignMeasure_dyadic_cell_ae : ∀ᵐ w ∂regularPairDesignMeasure θ (2 ^ Jh) (by positivity),
        w.2 ∈ dyadicPilotCell Jh w.1 := by
      apply regularPairDesignMeasure_ae_of_supported
      filter_upwards [] with w hw
      change regularGridCell (2 ^ Jh) (by positivity) w.2 =
        regularGridCell (2 ^ Jh) (by positivity) w.1
      by_contra h
      apply hw
      simp [sameLabelKernel, Ne.symm h]
    filter_upwards [regularPairDesignMeasure_cube_ae (C.withDomain Udom) θ hθ (2 ^ Jh) (by positivity),
      h_regularPairDesignMeasure_dyadic_cell_ae] with w hw hc
    have h_dyadicPopulationCoefficients_residual (θ : RegressionParameter d) J (m : ℕ → ℕ) (x : Covariate d) (y : Covariate d) : ⟪dyadicPopulationCoefficients C θ J m (x, y), pairResponseVector (θ.regression x) (θ.regression y)⟫ =
        dyadicPopulationResidual C θ J m x y := by
      have hsum : (∑ j ∈ Finset.range (J + 1),
          dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)) =
          dyadicPopulationPilotSum C θ J m false (x, y) -
            θ.regression x * dyadicPopulationPilotSum C θ J m true (x, y) := by
        simp only [dyadicPopulationPolynomial_affine, dotProduct_sub, dotProduct_smul, smul_eq_mul,
          Finset.sum_sub_distrib, dyadicPopulationPilotSum]
        rw [Finset.mul_sum]
      rw [pairResponseVector_inner]
      change 1 * θ.regression y + (-1 + dyadicPopulationPilotSum C θ J m true (x, y)) * θ.regression x +
        (-dyadicPopulationPilotSum C θ J m false (x, y)) = dyadicPopulationResidual C θ J m x y
      unfold dyadicPopulationResidual
      rw [hsum]
      ring
    rw [h_dyadicPopulationCoefficients_residual]
    have hr : euclideanNorm (w.2 - w.1) ≤ Real.sqrt d * (2 ^ Jh)⁻¹ := by
      have hcoord := regular_grid_same_cell_radius (2 ^ Jh) (by positivity) w.2 w.1 hw.2 hw.1 hc
      simpa [Nat.cast_pow, one_div] using euclideanNorm_le_coordinate_radius (w.2 - w.1)
        (1 / ((2 ^ Jh : ℕ) : ℝ)) (by positivity) hcoord
    apply (he Udom θ hθ _ _ w.1 hw.1 w.2 hw.2
      (dyadicPilotCell_subset_coarser _ Jh hJJh w.1 hc)).trans
    calc
      E * euclideanNorm (w.2 - w.1) * dyadicPopulationBiasBudget C
          (paperDyadicTerminalLevel C a offset H n) (paperDyadicApproximationDegree C a offset H n) ≤
        E * euclideanNorm (w.2 - w.1) *
          (B * (dyadicPilotScale d (paperDyadicTerminalLevel C a offset H n)) ^ (-paperSpatialExponent C)) :=
        mul_le_mul_of_nonneg_left hn (mul_nonneg hE.le (by unfold euclideanNorm; positivity))
      _ ≤ E * (Real.sqrt d * (2 ^ Jh)⁻¹) *
          (B * (dyadicPilotScale d (paperDyadicTerminalLevel C a offset H n)) ^ (-paperSpatialExponent C)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hE.le)
          (mul_nonneg hB.le (Real.rpow_nonneg (dyadicPilotScale_pos _ _).le _))
      _ = _ := by ring
  obtain ⟨B, hB, hb⟩ := h_uniform_domain_eventually_allocated_population_pair_residual (paperUpperSaddle C) (paperUpperShift C) (paperUpperSaddle_pos C hreg)
  have hg  :=
    tendsto_natCast_atTop_atTop.eventually ((eventually_paper_allocated_grid_guard C hreg hH).mono fun _ h => h.2)
  refine ⟨Cp, B, hCp, hB, ?_⟩
  filter_upwards [hb, hg] with n hb hg
  intro Udom θ hθ
  have h_dyadicPopulationCoefficients_first (J : ℕ) (m : ℕ → ℕ) (w : Covariate d × Covariate d) : dyadicPopulationCoefficients C θ J m w 0 = 1 := by
    rfl
  refine ⟨?_, h_dyadicPopulationCoefficients_first _ _, hc Udom θ hθ _ _ hg _, ?_⟩
  · exact dyadicPopulationCoefficients_measurable (C.withDomain Udom) θ hθ _ _
  · simpa only [paperAllocatedSide, dyadicRoundedSide_eq_inv_pow, paperAllocatedFinestLevel] using
      hb Udom θ hθ (paperAllocatedFinestLevel C H n) hg
theorem uniform_domain_admissible_dyadic_increment_all_derivative_bound  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (Y ) (hY : 0 ≤ Y) :
    ∃ D A, 0 < D ∧ 0 < A ∧
      ∀ Udom θ, Admissible (C.withDomain Udom) θ →
      ∀ j, ∀ x ∈ unitCube d, ∀ y, |y| ≤ Y → ∀ m k row,
        ‖iteratedFDeriv ℝ k
          (incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) y m row)
          (dyadicIncrementRawMean θ j x)‖ ≤
          (∑ i, |row i|) * D * k.factorial * A ^ k := by
  have h_uniform_domain_dyadic_increment_vector_derivative_bound : ∃ D A, 0 < D ∧ 0 < A ∧
      ∀ Udom θ, Admissible (C.withDomain Udom) θ →
      ∀ j, ∀ x ∈ unitCube d, ∀ y, |y| ≤ Y → ∀ m k directions,
        ‖iteratedFDeriv ℝ k
          (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) y m)
          (dyadicIncrementRawMean θ j x) directions‖ ≤
          D * k.factorial * A ^ k * ∏ i, ‖directions i‖ := by
    obtain ⟨W, hW, hmom⟩ := uniform_domain_admissible_dyadicFinPilotMoments_uniform_bound C
    obtain ⟨B, A, hB, hA, hder⟩ := anchored_population_inverse_derivatives
      (d := d) (ℓ := C.order) C.densityLower C.densityUpper W Y C.densityLower_pos
      (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le hY
    refine ⟨B, A, hB, hA, ?_⟩
    intro Udom θ hθ j x hx y hy m k directions
    let q := if j = 0 then (fun _ => 1) else dyadicNormalizedDensity θ (j - 1) x
    have hqm : Measurable q := by
      by_cases hj : j = 0
      · simp [q, hj, ModelConstants.withDomain]
      · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ (j - 1) x
    have hqb : ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ q w ∧ q w ≤ C.densityUpper := by
      by_cases hj : j = 0
      · exact Filter.Eventually.of_forall (fun _ => by
          simpa [q, hj, ModelConstants.withDomain] using And.intro C.densityLower_lt_one.le C.one_lt_densityUpper.le)
      · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ (j - 1) x
    have hV (t : Bool) : ‖(if j = 0 then (0 : Bool → Fin (anchoredDimension d C.order) → ℝ)
        else dyadicFinPilotMoments θ (j - 1) x) t‖ ≤ W := by
      by_cases hj : j = 0
      · simpa [hj] using hW.le
      · simpa only [hj, ite_false] using hmom Udom θ hθ (j - 1) x hx t
    have hd := hder (dyadicNormalizedAnchor j x) (dyadicNormalizedAnchor (j - 1) x)
      (gridNormalizedAnchor_mem_cube (2 ^ j) (by positivity) x hx)
      (gridNormalizedAnchor_mem_cube (2 ^ (j - 1)) (by positivity) x hx)
      (dyadicNormalizedDensity θ j x) q
      (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x) hqm
      (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x) hqb
      (dyadicFinPilotMoments θ j x) (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)
      (hmom Udom θ hθ j x hx) hV y hy m k directions
    rw [← dyadicIncrementRawMean_eq_with_virtual_parent (C.withDomain Udom) θ hθ j x hx] at hd
    exact hd
  obtain ⟨D, A, hD, hA, hder⟩ := h_uniform_domain_dyadic_increment_vector_derivative_bound
  refine ⟨D, A, hD, hA, ?_⟩
  intro Udom θ hθ j x hx y hy m k row
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro directions
  rw [incrementFinScalar_iteratedFDeriv]
  calc
    _ ≤ ‖rowFunctional row‖ * ‖iteratedFDeriv ℝ k
        (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) y m)
        (dyadicIncrementRawMean θ j x) directions‖ := (rowFunctional row).le_opNorm _
    _ ≤ (∑ i, |row i|) * (D * k.factorial * A ^ k * ∏ i, ‖directions i‖) :=
      mul_le_mul (rowFunctional_norm_le row) (hder Udom θ hθ j x hx y hy m k directions) (norm_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    _ = (∑ i, |row i|) * D * k.factorial * A ^ k * ∏ i, ‖directions i‖ := by ring
theorem uniform_domain_common_dyadicMultilevel_bounds  (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ D A, 0 < D ∧ 0 < A ∧ ∀ U θ, Admissible (C.withDomain U) θ →
      ∀ n J L : ℕ, J ≤ L → ∀ y : ℝ, |y| ≤ max C.holderBound 1 → ∀ m : ℕ → ℕ,
      (∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ j : Fin (J + 1), Λ ≤ (n : ℝ) - (m j.val + anchoredDimension d C.order + 1) + 1) →
      (∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
        regularGridCell (2 ^ L) (by positivity) x =
          regularGridCell (2 ^ L) (by positivity) z →
        (∫ t, dyadicMultilevelErrorField C θ n J y m t (x, z) ^ 2 ∂sampleLaw θ n) ≤
          4 * ((anchoredDimension d C.order ) * D) ^ 2 * d *
            dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L) ∧
      (∀ ν,
        MemLp ν 2 (regularPairDesignMeasure θ (2 ^ L) (by positivity)) →
        (∫ t, (∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
          ∂regularPairDesignMeasure θ (2 ^ L) (by positivity)) ^ 2 ∂sampleLaw θ n) ≤
          (4 * C.densityUpper ^ 2 * 2 ^ d *
            ((anchoredDimension d C.order ) * D) ^ 2 * d *
              dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L / Λ) *
            (∫ w, ν w ^ 2 ∂regularPairDesignMeasure θ (2 ^ L) (by positivity))) := by
  letI : Nonempty (AnchoredIndex d (pilotModelConstants C).order) :=
    inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  obtain ⟨D, A, hD, hA, hder⟩ := uniform_domain_admissible_dyadic_increment_all_derivative_bound
    (pilotModelConstants C) (pilotModelConstants C).holderBound (pilotModelConstants C).holderBound_pos.le
  refine ⟨D, A, hD, hA, ?_⟩
  intro U θ hθ n J L hJL y hy m hdegree Λ hΛ hΛn
  let CE := (pilotModelConstants C).withDomain U
  letI : Nonempty (AnchoredIndex d CE.order) := inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  have hθe  := admissible_pilotModelConstants (C.withDomain U) θ hθ
  have hd := hder U θ hθe
  have h_dyadicIncrementKernel_raw_budget_of_derivative : ∀ n j,
      ∀ x ∈ unitCube d, ∀ y, |y| ≤ CE.holderBound → ∀ m k row, ∀ hk,
      ∀ Λ : ℝ, 0 < Λ →
        (((k.factorial : ℝ) * Λ ^ k)⁻¹) *
          (∫ z : Fin n → Observation d,
            dyadicIncrementKernel CE θ j x y m row k
              (fun i => incrementGlobalVector j (z (Fin.castLEEmb hk i))) ^ 2 ∂sampleLaw θ n) ≤
          ((∑ i, |row i|) * D) ^ 2 * k.factorial *
            (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d CE.order)) *
              preconditionedPilotMomentConstant CE CE.order * dyadicPilotScale d j) / Λ) ^ k := by
    intro n j x hx y hy m k row hk Λ hΛ
    let := sampleLaw_isProbability CE θ hθe n
    obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := dyadicIncrementRawVector_sample_facts CE θ hθe j x hx
    let X (i : Fin n) (z : Fin n → Observation d) := dyadicIncrementRawVector (ℓ := CE.order) j x (z i)
    let e := Fin.castLEEmb hk
    let E := (Fintype.card (incrementVariables (anchoredDimension d CE.order)) : ℝ) *
      preconditionedPilotMomentConstant CE CE.order * dyadicPilotScale d j
    have hE : 0 ≤ E := by
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos CE _).le)
        (dyadicPilotScale_pos _ _).le
    have hrow : 0 ≤ (∑ i, |row i|) * D :=
      mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hD.le
    have hb := KernelMomentBounds.factorial_kernel_budget
      (iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d CE.order)
        CE.densityLower CE.densityUpper (anchoredFinTransport d CE.order) y m row) (dyadicIncrementRawMean θ j x))
      (fun i => X (e i)) (hind.precomp e.injective) (fun i => hmeas (e i))
      (fun i a => hL2 (e i) a) E ((∑ i, |row i|) * D) A Λ hE hrow hA.le hΛ
      (fun i => dyadicIncrementRawVector_sample_second_le CE θ hθe j x hx (e i))
      (hd j x hx y hy m k row)
    have heq : (fun z : Fin n → Observation d =>
        dyadicIncrementKernel CE θ j x y m row k
          (fun i => incrementGlobalVector j (z (Fin.castLEEmb hk i))) ^ 2) =
        (fun z => iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d CE.order)
          CE.densityLower CE.densityUpper (anchoredFinTransport d CE.order) y m row) (dyadicIncrementRawMean θ j x)
          (fun i => X (e i) z) ^ 2) := by
      funext z
      rw [dyadicIncrementKernel_raw]
    rw [heq]
    exact hb
  have h_dyadicPilotErrorField_test_variance_of_raw_budget : ∀ n j J : ℕ, j ≤ J →
      ∀ y : ℝ, |y| ≤ CE.holderBound → ∀ m : ℕ,
      m + anchoredDimension d CE.order + 1 ≤ n →
      ∀ Λ : ℝ, 0 < Λ → Λ ≤ (n : ℝ) - (m + anchoredDimension d CE.order + 1) + 1 →
      ∀ ν : Covariate d × Covariate d → ℝ,
      MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)) →
      variance (fun z => ∫ w, ν w * dyadicPilotErrorField CE θ n j y m z w
        ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)) (sampleLaw θ n) ≤
      (CE.densityUpper ^ 2 / dyadicPilotScale d (j - 1)) *
        ((dyadicPilotRowCap d CE.order j J * D) ^ 2 *
          ∑ r : Fin (m + anchoredDimension d CE.order + 1),
            ((r.val + 1).factorial : ℝ) *
              (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d CE.order)) *
                preconditionedPilotMomentConstant CE CE.order * dyadicPilotScale d j) / Λ) ^ (r.val + 1)) *
        (∫ w, ν w ^ 2 ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)) := by
    intro n j J hj y hy m hdegree Λ hΛ hΛn ν hν
    let := sampleLaw_isProbability CE θ hθe n
    let M := regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)
    let := regularPairDesignMeasure_isFinite CE θ hθe ((2 : ℕ) ^ J) (by positivity)
    let R := m + anchoredDimension d CE.order + 1
    let X (i : Fin n) (z : Fin n → Observation d) := incrementGlobalVector (ℓ := CE.order) j (z i)
    let H (w : Covariate d × Covariate d) (r : Fin R) :=
      dyadicIncrementKernel CE θ j w.1 y m (dyadicPilotRow j w.1 w.2) (r.val + 1)
    let rowcap := dyadicPilotRowCap d CE.order j J
    have hrowcap : 0 ≤ rowcap := dyadicPilotRowCap_nonneg _ _ _ _
    have hcube  :=
      (regularPairDesignMeasure_cube_ae CE θ hθe ((2 : ℕ) ^ J) (by positivity)).mono (fun w hw => hw.1)
    have hrow := dyadicPilotRow_pair_cap (ℓ := CE.order) CE θ hθe j J hj
    have hHmeas (r : Fin R) : AEStronglyMeasurable (fun w => H w r) M :=
      (dyadicIncrementKernel_field_measurable CE θ hθe j y m (r.val + 1) _
        (dyadicPilotRow_field_measurable j)).aestronglyMeasurable
    have hH (r : Fin R) : Integrable (fun w => ν w • H w r) M :=
      dyadicIncrementKernel_weighted_integrable CE θ hθe j y hy m (r.val + 1) _
        (dyadicPilotRow_field_measurable j) M rowcap hrowcap hcube hrow ν hν
    obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := incrementGlobalVector_sample_facts (ℓ := CE.order) CE θ hθe j
    let e (r : Fin R) := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans hdegree)
    let Op (r : Fin R) := FieldLiftCovariance.rawKernelOperator (e r) X hind hmeas hL2
    have hcaps (r : Fin R) : ∃ B : ℝ, 0 < B ∧ ∀ᵐ w ∂M, ‖H w r‖ ≤ B :=
      dyadicIncrementKernel_field_norm_bound CE θ hθe j y hy m (r.val + 1) _ M rowcap hrowcap hcube hrow
    let B (r : Fin R) := Classical.choose (hcaps r)
    have hBpos (r : Fin R) : 0 < B r := (Classical.choose_spec (hcaps r)).1
    have hBcap (r : Fin R) : ∀ᵐ w ∂M, ‖H w r‖ ≤ B r := (Classical.choose_spec (hcaps r)).2
    have hopcap (r : Fin R) : ∀ᵐ w ∂M, ‖Op r (H w r)‖ ≤ ‖Op r‖ * B r := by
      filter_upwards [hBcap r] with w hw
      exact ((Op r).le_opNorm _).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
    have hblock (c : Fin (Fintype.card (DyadicPilotLabelIndex d (j - 1)))) :
        M.real {w | dyadicPilotLabel (j - 1) w.1 = c} ≤ CE.densityUpper ^ 2 / dyadicPilotScale d (j - 1) := by
      have hs : {w : Covariate d × Covariate d | dyadicPilotLabel (j - 1) w.1 = c} =
          {w | regularGridCell ((2 : ℕ) ^ (j - 1)) (by positivity) w.1 =
            (Fintype.equivFin (DyadicPilotLabelIndex d (j - 1))).symm c} := by
        ext w
        exact (Fintype.equivFin (DyadicPilotLabelIndex d (j - 1))).apply_eq_iff_eq_symm_apply
      rw [hs]
      have h_regularPairDesignMeasure_parent_block_mass (k) (hk) (c) : (regularPairDesignMeasure θ k hk).real
          {w : Covariate d × Covariate d | regularGridCell (2 ^ (j - 1)) (by positivity) w.1 = c} ≤
            CE.densityUpper ^ 2 / dyadicPilotScale d (j - 1) := by
        let := cubeVolume_isProbability d
        let A : Set (Covariate d) := (regularGridCell (2 ^ (j - 1)) (by positivity)) ⁻¹' {c}
        have hfirst : (regularPairDesignMeasure θ k hk).real (Prod.fst ⁻¹' A) ≤
            CE.densityUpper ^ 2 * (cubeVolume d).real A := by
          rw [← map_measureReal_apply measurable_fst (measurableSet_singleton c |>.preimage (regular_grid_cell_measurable _ _))]
          have h_regularPairDesignMeasure_fst_cube_le : (regularPairDesignMeasure θ k hk).map Prod.fst ≤
            ENNReal.ofReal (CE.densityUpper ^ 2) • cubeVolume d := by
            have h_regularPairDesignMeasure_fst_le : (regularPairDesignMeasure θ k hk).map Prod.fst ≤ ENNReal.ofReal CE.densityUpper • designLaw θ := by
              let := designLaw_isProbability CE θ hθe
              have hkp : 0 < (k : ℝ) ^ d := pow_pos (by exact_mod_cast hk) d
              have h := partitionPairMeasure_fst_le (designLaw θ) (regularGridCell k hk)
                (regular_grid_cell_measurable k hk) hkp.le
                (div_nonneg (by linarith [CE.one_lt_densityUpper]) hkp.le)
                (regularGridProbability_cap CE θ hθe k hk)
              simpa only [regularPairDesignMeasure, partitionPairMeasure,
                mul_div_cancel₀ _ hkp.ne'] using h
            calc
              _ ≤ ENNReal.ofReal CE.densityUpper • designLaw θ :=
                h_regularPairDesignMeasure_fst_le
              _ ≤ ENNReal.ofReal CE.densityUpper • (ENNReal.ofReal CE.densityUpper • cubeVolume d) := by
                gcongr
                exact admissible_designLaw_le_cubeVolume CE θ hθe
              _ = _ := by rw [smul_smul, ← ENNReal.ofReal_mul (by linarith [CE.one_lt_densityUpper]), ← pow_two]
          have ht := ENNReal.toReal_mono
            (show (ENNReal.ofReal (CE.densityUpper ^ 2) • cubeVolume d) A ≠ ⊤ by
              simp only [Measure.smul_apply, smul_eq_mul]
              exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (cubeVolume d) A))
            (h_regularPairDesignMeasure_fst_cube_le A)
          simpa only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (sq_nonneg _)] using ht
        have hvol : (cubeVolume d).real A ≤ (1 / 2 ^ (j - 1)) ^ d := by
          have hv := regular_grid_fiber_volume_le (2 ^ (j - 1)) (by positivity) c
          have ht := ENNReal.toReal_mono (by finiteness :
            ENNReal.ofReal (1 / ((2 ^ (j - 1) : ℕ) : ℝ)) ^ d ≠ ⊤) hv
          simpa [measureReal_def, A, ENNReal.toReal_pow, Nat.cast_pow,
            ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / ((2 ^ (j - 1) : ℕ) : ℝ))] using ht
        apply hfirst.trans
        apply (mul_le_mul_of_nonneg_left hvol (sq_nonneg _)).trans_eq
        simp only [dyadicPilotScale, div_eq_mul_inv, one_mul, inv_pow]
      exact h_regularPairDesignMeasure_parent_block_mass ((2 : ℕ) ^ J) (by positivity) _
    have h_dyadicIncrementKernel_symmetric (x) (row) (k) (σ : Equiv.Perm (Fin k)) (v : Fin k → Fin (Fintype.card (IncrementGlobalIndex d CE.order j)) → ℝ) : dyadicIncrementKernel CE θ j x y m row k (fun i => v (σ i)) =
        dyadicIncrementKernel CE θ j x y m row k v := by
      let F := rowIncrementPolynomial (anchoredDimension d CE.order) CE.densityLower CE.densityUpper
        (anchoredFinTransport d CE.order) y m row
      have hF : (fun z => eval z F) = incrementFinScalar (anchoredDimension d CE.order)
          CE.densityLower CE.densityUpper (anchoredFinTransport d CE.order) y m row := by
        funext z
        exact rowIncrementPolynomial_eval _ _ _ _ _ _ _ _
      simp only [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply]
      rw [← hF]
      exact (AnalyticOnNhd.eval_mvPolynomial F).analyticOn.iteratedFDeriv_comp_perm
        (fun i => incrementPilotCoordinate j x (v i)) σ
    have hu := FieldLiftCovariance.integrated_centered_lift_variance_localized
      (μ := sampleLaw θ n) (M := M) (n := n)
      (p := Fintype.card (IncrementGlobalIndex d CE.order j)) (R := R)
      (q := Fintype.card (DyadicPilotLabelIndex d (j - 1))) H ν hν hH hHmeas
      (fun w r σ v => (h_dyadicIncrementKernel_symmetric w.1 (dyadicPilotRow j w.1 w.2) _ σ v))
      X (incrementGlobalMean θ j) hdegree hind hmeas hid hL2 hmean Λ hΛ
      (by simpa only [R, Nat.cast_add, Nat.cast_one] using hΛn)
      (fun w => dyadicPilotLabel (j - 1) w.1) ((dyadicPilotLabel_measurable _).comp measurable_fst)
      (fun r => ‖Op r‖ * B r) (fun r => mul_nonneg (norm_nonneg (Op r)) (hBpos r).le) hopcap
      (fun r w v hv => Filter.Eventually.of_forall (fun z =>
        dyadicIncrementKernel_disjoint CE θ j (r.val + 1) (by omega) w.1 v.1 hv y y m m
          (dyadicPilotRow j w.1 w.2) (dyadicPilotRow j v.1 v.2) (fun i => z (e r i))))
      (CE.densityUpper ^ 2 / dyadicPilotScale d (j - 1)) hblock
    let δ (r : Fin R) := (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹
    let S (w : Covariate d × Covariate d) := ∑ r : Fin R, δ r * ‖Op r (H w r)‖ ^ 2
    let P := (rowcap * D) ^ 2 * ∑ r : Fin R, ((r.val + 1).factorial : ℝ) *
      (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d CE.order)) *
        preconditionedPilotMomentConstant CE CE.order * dyadicPilotScale d j) / Λ) ^ (r.val + 1)
    have hSmeas : AEStronglyMeasurable S M := by
      have hm : AEStronglyMeasurable (∑ r : Fin R, fun w => δ r * ‖Op r (H w r)‖ ^ 2) M :=
        Finset.aestronglyMeasurable_sum Finset.univ (fun r _ =>
          ((Op r).continuous.comp_aestronglyMeasurable (hHmeas r)).norm.pow 2 |>.const_mul (δ r))
      convert hm using 1
      funext w
      simp only [S, Finset.sum_apply]
    have hSnon (w) : 0 ≤ S w := Finset.sum_nonneg (fun r _ => mul_nonneg (by dsimp [δ]; positivity) (sq_nonneg _))
    have hSbound : ∀ᵐ w ∂M, S w ≤ P := by
      filter_upwards [hcube, hrow] with w hw hr
      unfold S P
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro r _
      have hb := h_dyadicIncrementKernel_raw_budget_of_derivative n j w.1 hw y hy m (r.val + 1) (dyadicPilotRow j w.1 w.2)
        ((Nat.succ_le_of_lt r.isLt).trans hdegree) Λ hΛ
      have he  :=
        FieldLiftCovariance.raw_kernel_operator_norm_sq (e r) X hind hmeas hL2 (H w r)
      rw [he]
      apply hb.trans
      have hc := preconditionedPilotMomentConstant_pos CE CE.order
      have := dyadicPilotScale_pos d j
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_right _
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _))
      apply pow_le_pow_left₀ (mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hD.le)
      exact mul_le_mul_of_nonneg_right hr hD.le
    have hStop  := memLp_top_of_bound hSmeas P (hSbound.mono (fun w hw => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hSnon w)]
      exact hw))
    have hi : Integrable (fun w => ν w ^ 2 * S w) M := by
      convert hν.integrable_sq.mul_of_top_right hStop using 1
      funext w
      simp only [Pi.mul_apply]
      exact mul_comm _ _
    have hile := integral_mono_ae hi (hν.integrable_sq.const_mul P)
      (hSbound.mono (fun w hw => (mul_le_mul_of_nonneg_left hw (sq_nonneg (ν w))).trans_eq (mul_comm _ _)))
    rw [integral_const_mul] at hile
    have hrhs : (∫ w, ν w ^ 2 * ∑ r : Fin R, δ r *
        ∫ z : Fin n → Observation d, H w r (fun i => X (e r i) z) ^ 2 ∂sampleLaw θ n ∂M) =
        ∫ w, ν w ^ 2 * S w ∂M := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by
        apply congrArg (fun a => ν w ^ 2 * a)
        apply Finset.sum_congr rfl
        intro r _
        rw [← FieldLiftCovariance.raw_kernel_operator_norm_sq (e r) X hind hmeas hL2 (H w r)]
    have herr : (fun z : Fin n → Observation d => ∫ w, ν w *
        LiftL2.centeredKernelExpansion 0 (H w) (fun i z => X i z - incrementGlobalMean θ j) z ∂M) =
        (fun z => ∫ w, ν w * dyadicPilotErrorField CE θ n j y m z w ∂M) := by
      funext z
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => congrArg (fun a => ν w * a)
        (dyadicPolynomialPilot_centered_global CE θ hθe n j w.1 y m (dyadicPilotRow j w.1 w.2) hdegree z)
    rw [herr, hrhs] at hu
    exact hu.trans (by
      simpa only [P, R, rowcap, mul_assoc] using mul_le_mul_of_nonneg_left hile (div_nonneg (sq_nonneg _) (dyadicPilotScale_pos _ _).le))
  constructor
  · intro x hx z hz hc
    have h_dyadicPolynomialPilot_variance_of_derivative : ∀ n j : ℕ,
        ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ CE.holderBound → ∀ m : ℕ,
        ∀ row : Fin (anchoredDimension d CE.order) → ℝ,
        m + anchoredDimension d CE.order + 1 ≤ n →
        ∀ Λ : ℝ, 0 < Λ → Λ ≤ ↑n - (m + anchoredDimension d CE.order + 1) + 1 →
          variance (dyadicPolynomialPilot CE n j x y m row) (sampleLaw θ n) ≤
            ((∑ i, |row i|) * D) ^ 2 *
              ∑ t : Fin (m + anchoredDimension d CE.order + 1),
                ((t.val + 1).factorial : ℝ) *
                  (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d CE.order)) *
                    preconditionedPilotMomentConstant CE CE.order * dyadicPilotScale d j) / Λ) ^ (t.val + 1) := by
      intro n j x hx y hy m row hdegree Λ hΛ hΛn
      let := sampleLaw_isProbability CE θ hθe n
      let F := rowIncrementPolynomial (anchoredDimension d CE.order) CE.densityLower CE.densityUpper
        (anchoredFinTransport d CE.order) y m row
      let X (i : Fin n) (z : Fin n → Observation d) := dyadicIncrementRawVector (ℓ := CE.order) j x (z i)
      let E := (Fintype.card (incrementVariables (anchoredDimension d CE.order)) : ℝ) *
        preconditionedPilotMomentConstant CE CE.order * dyadicPilotScale d j
      have hE : 0 ≤ E := by
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos CE _).le)
          (dyadicPilotScale_pos _ _).le
      have hrow : 0 ≤ (∑ i, |row i|) * D :=
        mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hD.le
      obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := dyadicIncrementRawVector_sample_facts CE θ hθe j x hx
      have hv := LiftL2.polynomialLift_variance_le_raw_power_l2 F X (dyadicIncrementRawMean θ j x)
        (rowIncrementPolynomial_degree _ _ _ _ _ _ _) hdegree hind hmeas hid hL2 hmean Λ hΛ
        (by simpa only [Nat.cast_add, Nat.cast_one] using hΛn)
      apply hv.trans
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t _
      let e := Fin.castLEEmb ((Nat.succ_le_of_lt t.isLt).trans hdegree)
      have hFeval : (fun z => eval z F) = incrementFinScalar (anchoredDimension d CE.order)
          CE.densityLower CE.densityUpper (anchoredFinTransport d CE.order) y m row := by
        funext z
        exact rowIncrementPolynomial_eval _ _ _ _ _ _ _ _
      have hd : ‖iteratedFDeriv ℝ (t.val + 1) (fun z => eval z F) (dyadicIncrementRawMean θ j x)‖ ≤
          (∑ i, |row i|) * D * ((t.val + 1).factorial : ℝ) * A ^ (t.val + 1) := by
        rw [hFeval]
        exact hd j x hx y hy m (t.val + 1) row
      have hb := KernelMomentBounds.factorial_kernel_budget
        (iteratedFDeriv ℝ (t.val + 1) (fun z => eval z F) (dyadicIncrementRawMean θ j x))
        (fun i => X (e i)) (hind.precomp e.injective) (fun i => hmeas (e i))
        (fun i a => hL2 (e i) a) E ((∑ i, |row i|) * D) A Λ hE hrow hA.le hΛ
        (fun i => dyadicIncrementRawVector_sample_second_le CE θ hθe j x hx (e i)) hd
      simpa only [E, e, mul_assoc] using hb
    have h_dyadicMultilevelErrorField_point_second_of_variance : ∀ n J L, J ≤ L → ∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
        regularGridCell (2 ^ L) (by positivity) x =
          regularGridCell (2 ^ L) (by positivity) z →
        ∀ y : ℝ, |y| ≤ CE.holderBound → ∀ m : ℕ → ℕ,
        (∀ j : Fin (J + 1), m j.val + anchoredDimension d CE.order + 1 ≤ n) →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ j : Fin (J + 1), Λ ≤ ↑n - (m j.val + anchoredDimension d CE.order + 1) + 1) →
        (∫ t, dyadicMultilevelErrorField CE θ n J y m t (x, z) ^ 2 ∂sampleLaw θ n) ≤
          4 * ((anchoredDimension d CE.order ) * D) ^ 2 * d *
            dyadicMultilevelBudget (dyadicSeriesEnvelope CE A Λ J m) J L := by
      have h_dyadicPilotErrorField_point_second_of_variance : ∀ n j L, j ≤ L → ∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
          regularGridCell (2 ^ L) (by positivity) x =
            regularGridCell (2 ^ L) (by positivity) z →
          ∀ y, |y| ≤ CE.holderBound → ∀ m,
          m + anchoredDimension d CE.order + 1 ≤ n → ∀ Λ, 0 < Λ →
          Λ ≤ (n : ℝ) - (m + anchoredDimension d CE.order + 1) + 1 →
          (∫ t, dyadicPilotErrorField CE θ n j y m t (x, z) ^ 2 ∂sampleLaw θ n) ≤
            (dyadicPilotRowCap d CE.order j L * D) ^ 2 * dyadicPilotSeries CE A Λ j m := by
        intro n j L hj x hx z hz hc y hy m hdegree Λ hΛ hΛn
        obtain ⟨hL2, hmean⟩ := dyadicPolynomialPilot_moment_facts CE θ hθe n j x hx y m
          (dyadicPilotRow j x z) hdegree
        have h := h_dyadicPolynomialPilot_variance_of_derivative n j x hx y hy m (dyadicPilotRow j x z) hdegree Λ hΛ hΛn
        rw [variance_eq_integral hL2.aemeasurable, hmean] at h
        have hr := dyadicPilotRow_sum_abs_le_fine_cell (ℓ := CE.order) j L hj x z hx hz hc.symm
        apply h.trans
        change ((∑ i, |dyadicPilotRow j x z i|) * D) ^ 2 * dyadicPilotSeries CE A Λ j m ≤ _
        apply mul_le_mul_of_nonneg_right _ (dyadicPilotSeries_nonneg CE A Λ hΛ.le _ _)
        apply pow_le_pow_left₀ (mul_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hD.le)
        exact mul_le_mul_of_nonneg_right hr hD.le
      intro n J L hJL x hx z hz hc y hy m hdegree Λ hΛ hΛn
      let H := dyadicSeriesEnvelope CE A Λ J m
      have : 0 ≤ H := dyadicSeriesEnvelope_nonneg CE A Λ hΛ.le J m
      let B := ((anchoredDimension d CE.order : ℝ) * D) ^ 2 * ↑d *
        ((2 ^ L)⁻¹) ^ 2 * H
      have hB : 0 ≤ B := by dsimp [B]; positivity
      let X (j : Fin (J + 1)) (t : Fin n → Observation d) :=
        dyadicPilotErrorField CE θ n j.val y (m j.val) t (x, z)
      have hX (j : Fin (J + 1)) : MemLp (X j) 2 (sampleLaw θ n) :=
        (dyadicPilotErrorField_point_moment_facts CE θ hθe n j.val x hx z y (m j.val) (hdegree j)).1
      have hE (j : Fin (J + 1)) : (∫ t, X j t ^ 2 ∂sampleLaw θ n) ≤ B * ((2 : ℝ) ^ j.val) ^ 2 := by
        have h := (h_dyadicPilotErrorField_point_second_of_variance) n j.val L ((Nat.le_of_lt_succ j.isLt).trans hJL)
          x hx z hz hc y hy (m j.val) (hdegree j) Λ hΛ (hΛn j)
        apply h.trans
        rw [dyadicPilotRowCap_square]
        calc
          _ ≤ (((anchoredDimension d CE.order ) * D) ^ 2 * d *
              ((2 ^ L)⁻¹) ^ 2 * (2 ^ j.val) ^ 2) * H :=
            mul_le_mul_of_nonneg_left (by apply le_trans _ (dyadicSeriesEnvelope_level_le CE A Λ J m j); exact le_mul_of_one_le_right (dyadicPilotSeries_nonneg CE A Λ hΛ.le j.val (m j.val)) (le_max_left _ _)) (by positivity)
          _ = _ := by dsimp [B]; ring
      have h := secondMoment_dyadic_sum_le (sampleLaw θ n) J X hX B hB hE
      apply h.trans_eq
      dsimp [B, dyadicMultilevelBudget]
      ring
    exact h_dyadicMultilevelErrorField_point_second_of_variance
      n J L hJL x hx z hz hc y hy m hdegree Λ hΛ hΛn
  · intro ν hν
    have h_dyadicMultilevelErrorField_test_second_of_variance (htest : ∀ n j J : ℕ, j ≤ J → ∀ y : ℝ, |y| ≤ CE.holderBound → ∀ m : ℕ, m + anchoredDimension d CE.order + 1 ≤ n → ∀ Λ : ℝ, 0 < Λ → Λ ≤ (n : ℝ) - (m + anchoredDimension d CE.order + 1) + 1 → ∀ ν : Covariate d × Covariate d → ℝ, MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)) → variance (fun z => ∫ w, ν w * dyadicPilotErrorField CE θ n j y m z w ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)) (sampleLaw θ n) ≤ (CE.densityUpper ^ 2 / dyadicPilotScale d (j - 1)) * ((dyadicPilotRowCap d CE.order j J * D) ^ 2 * ∑ r : Fin (m + anchoredDimension d CE.order + 1), ((r.val + 1).factorial : ℝ) * (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d CE.order)) * preconditionedPilotMomentConstant CE CE.order * dyadicPilotScale d j) / Λ) ^ (r.val + 1)) * (∫ w, ν w ^ 2 ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity))) : ∀ n J L : ℕ, J ≤ L → ∀ y : ℝ, |y| ≤ CE.holderBound → ∀ m : ℕ → ℕ,
        (∀ j : Fin (J + 1), m j.val + anchoredDimension d CE.order + 1 ≤ n) →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ j : Fin (J + 1), Λ ≤ ↑n - (m j.val + anchoredDimension d CE.order + 1) + 1) →
        ∀ ν : Covariate d × Covariate d → ℝ,
        MemLp ν 2 (regularPairDesignMeasure θ (2 ^ L) (by positivity)) →
        (∫ t, (∫ w, ν w * dyadicMultilevelErrorField CE θ n J y m t w
          ∂regularPairDesignMeasure θ (2 ^ L) (by positivity)) ^ 2 ∂sampleLaw θ n) ≤
          (4 * CE.densityUpper ^ 2 * 2 ^ d *
            ((anchoredDimension d CE.order ) * D) ^ 2 * d *
              dyadicMultilevelBudget (dyadicSeriesEnvelope CE A Λ J m) J L / Λ) *
            (∫ w, ν w ^ 2 ∂regularPairDesignMeasure θ (2 ^ L) (by positivity)) := by
      intro n J L hJL y hy m hdegree Λ hΛ hΛn ν hν
      let := sampleLaw_isProbability CE θ hθe n
      let M := regularPairDesignMeasure θ (2 ^ L) (by positivity)
      let H := dyadicSeriesEnvelope CE A Λ J m
      have : 0 ≤ H := dyadicSeriesEnvelope_nonneg CE A Λ hΛ.le J m
      let I := ∫ w, ν w ^ 2 ∂M
      let B := CE.densityUpper ^ 2 * 2 ^ d *
        ((anchoredDimension d CE.order ) * D) ^ 2 * d *
          ((2 ^ L)⁻¹) ^ 2 * (H / Λ) * I
      let X (j : Fin (J + 1)) (t : Fin n → Observation d) :=
        ∫ w, ν w * dyadicPilotErrorField CE θ n j.val y (m j.val) t w ∂M
      have hf (j : Fin (J + 1)) := dyadicPilotErrorField_test_moment_facts CE θ hθe n j.val L
        ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy (m j.val) (hdegree j) ν hν
      have hE (j : Fin (J + 1)) : (∫ t, X j t ^ 2 ∂sampleLaw θ n) ≤ B * (2 ^ j.val) ^ 2 := by
        have h := htest n j.val L ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy
          (m j.val) (hdegree j) Λ hΛ (hΛn j) ν hν
        rw [variance_of_integral_eq_zero (hf j).1.aemeasurable (hf j).2] at h
        apply h.trans
        change (CE.densityUpper ^ 2 / dyadicPilotScale d (j.val - 1)) *
          ((dyadicPilotRowCap d CE.order j.val L * D) ^ 2 * dyadicPilotSeries CE A Λ j.val (m j.val)) * I ≤ _
        rw [dyadicPilotRowCap_square]
        have hratio : dyadicPilotScale d j.val / dyadicPilotScale d (j.val - 1) ≤ ↑2 ^ d :=
          (div_le_iff₀ (dyadicPilotScale_pos _ _)).mpr dyadicPilotScale_parent_ratio_le
        have h_dyadicPilotSeries_div_scale_le_envelope : dyadicPilotSeries CE A Λ j.val (m j.val) / dyadicPilotScale d j.val ≤
          dyadicSeriesEnvelope CE A Λ J m / Λ := by
          have h := (mul_le_mul_of_nonneg_left (le_max_right 1 (Λ / dyadicPilotScale d j.val)) (dyadicPilotSeries_nonneg CE A Λ hΛ.le j.val (m j.val))).trans
            (dyadicSeriesEnvelope_level_le CE A Λ J m j)
          apply (le_div_iff₀ hΛ).mpr
          convert h using 1 <;> ring
        have hs := h_dyadicPilotSeries_div_scale_le_envelope
        have hsnon := div_nonneg (dyadicPilotSeries_nonneg CE A Λ hΛ.le j.val (m j.val))
          (dyadicPilotScale_pos d j.val).le
        calc
          _ = (CE.densityUpper ^ 2 * ((anchoredDimension d CE.order ) * D) ^ 2 *
              d * ((2 ^ L)⁻¹) ^ 2 * (2 ^ j.val) ^ 2) *
              (dyadicPilotScale d j.val / dyadicPilotScale d (j.val - 1)) *
              (dyadicPilotSeries CE A Λ j.val (m j.val) / dyadicPilotScale d j.val) * I := by
            field_simp [(dyadicPilotScale_pos d j.val).ne', (dyadicPilotScale_pos d (j.val - 1)).ne']
          _ ≤ (CE.densityUpper ^ 2 * ((anchoredDimension d CE.order ) * D) ^ 2 *
              d * ((2 ^ L)⁻¹) ^ 2 * (2 ^ j.val) ^ 2) *
              2 ^ d * (H / Λ) * I := by
            apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun _ => sq_nonneg _))
            exact mul_le_mul (mul_le_mul_of_nonneg_left hratio (by positivity)) hs hsnon (by positivity)
          _ = _ := by dsimp [B]; ring
      have h := secondMoment_dyadic_sum_le (sampleLaw θ n) J X (fun j => (hf j).1) B (by dsimp [B]; positivity) hE
      have heq : (fun t => ∑ j, X j t) =
          (fun t => ∫ w, ν w * dyadicMultilevelErrorField CE θ n J y m t w ∂M) := by
        funext t
        exact (dyadicMultilevelErrorField_test_integral_sum CE θ hθe n J L hJL y hy m hdegree ν hν t).symm
      have heqpoint (t : Fin n → Observation d) := congrFun heq t
      simp_rw [heqpoint] at h
      apply h.trans_eq
      dsimp [B, dyadicMultilevelBudget]
      ring
    exact (h_dyadicMultilevelErrorField_test_second_of_variance (h_dyadicPilotErrorField_test_variance_of_raw_budget))
      n J L hJL y hy m hdegree Λ hΛ hΛn ν hν
end NearlyMinimax
