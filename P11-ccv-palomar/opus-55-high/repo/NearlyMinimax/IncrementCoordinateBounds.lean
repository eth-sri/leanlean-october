module

public import NearlyMinimax.IncrementPilotCoordinates
public import NearlyMinimax.AnchoredCoefficientBounds
public import NearlyMinimax.DyadicMeasurability
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-! Actual measurable finite coordinate fields and fixed-level bounds.
These bounds establish Bochner integrability; sharp level dependence is obtained
from the separate original-law pilot energy estimates. -/

𝛍
𝚼
𝚨


𝗃 𝔒 (Fin (DyadicGlobalDimension d ℓ ἀ) → ℝ) →L[ℝ] ℝ
𝗇 𝔅 𝔒 j
𝗇 𝔇 𝗬₂
𝗇 𝔔 𝗭₂
𝗃 𝔛 ἀ j x a
𝗃 𝔟 fun x => 𝔛 ἀ
theorem dyadicPilotCoordinate_measurable j (a : 𝔇) :
    Measurable 𝔟 dyadicPilotCoordinate := by
  have hlin : Measurable fun x => pilotPolynomialLinear (ℓ := 𝔔)
      (dyadicPilotLabel j x) 𝔛 dyadicPilotPolynomial $ dyadicPilotResponse a := by
    apply Finset.measurable_sum
    intro β _
    exact (dyadicPilotPolynomial_coeff_continuous j a _).measurable.smul
      $ (measurable_of_countable fun c =>
        (ContinuousLinearMap.proj $ (Fintype.equivFin
          $ PilotBasisIndex (Fintype.card $ DyadicPilotLabelIndex d j ) d 𝔔 )
            ((c, β), dyadicPilotResponse a) :
          𝔅) ).comp $ dyadicPilotLabel_measurable j
  exact (measurable_const : Measurable fun _ => 𝘟 ).smul hlin

𝗇 𝔘 localPilotReplaceRow a β
theorem preconditionedPilotCoordinate_measurable j (a : 𝔇) :
    Measurable 𝔟 preconditionedPilotCoordinate := Finset.measurable_sum Finset.univ fun β _ =>
    ((dyadicKnownGram_inverse_measurable j).eval_matrix ).smul
      $ dyadicPilotCoordinate_measurable j 𝔘

𝗇 𝔄 Fin (Fintype.card $ IncrementGlobalIndex d ℓ j ) → ℝ
𝗇 𝔈 𝘮
𝗇 𝔓 𝔄 →L[ℝ] ℝ
𝗇 𝔗 incrementVariables 𝚃
theorem incrementPilotFreeCoordinate_measurable (j : ℕ)
    (a : 𝔗) :
    Measurable fun x : Covariate d => 𝔛 incrementPilotFreeCoordinate := by
  let pc : 𝔅 →L[ℝ]
      𝔓 :=
    ContinuousLinearMap.precomp ℝ $ incrementGlobalCurrent j
  let pp : 𝔒 𝔈 →L[ℝ]
      𝔓 :=
    ContinuousLinearMap.precomp ℝ $ incrementGlobalParent j
  have hc (a : 𝔇) : Measurable fun x : Covariate d =>
      (𝔛 preconditionedPilotCoordinate).comp $ incrementGlobalCurrent j :=
    pc.measurable.comp
      $ preconditionedPilotCoordinate_measurable j a
  have hp (a : 𝔇) : Measurable fun x : Covariate d =>
      (preconditionedPilotCoordinate 𝔈 x a).comp $ incrementGlobalParent j :=
    pp.measurable.comp
      $ preconditionedPilotCoordinate_measurable 𝔈 a
  cases a with
  | inl a =>
    cases a with
    | inl a => exact hc _
    | inr a =>
      change Measurable fun x : Covariate d => if 𝘠 then
         if a.2.1 = a.2.2 then incrementGlobalOne j else 0 else _
      split_ifs
      · exact measurable_const
      · exact measurable_const
      · fun_prop
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    simp only [incrementPilotFreeCoordinate]
    split_ifs
    · exact measurable_const
    · fun_prop
    · fun_prop
    · tauto
    · tauto

𝗃 𝔐 ἀ (d := d) (ℓ := ℓ)
theorem incrementPilotCoordinate_measurable j :
    Measurable $ 𝔐 incrementPilotCoordinate j := (ContinuousLinearMap.piEquivL ℝ
    𝔄
    𝚟).continuous.measurable.comp
      $ measurable_pi_iff.mpr fun _ => incrementPilotFreeCoordinate_measurable j _

theorem real_pi_projection_norm_le [Fintype ι] i :
    ‖(ContinuousLinearMap.proj i : 𝙛 →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm v i

𝗇 𝔉 𝗫₂
theorem pilotPolynomialLinear_norm_le (c : Fin q)
    P response M (hM : 𝙷)
    (hP : ∀ β : 𝔉, |P.coeff (polynomialBoxExponent β)| ≤ M) :
    ‖pilotPolynomialLinear (ℓ := ℓ) c P response‖ ≤
       Fintype.card 𝔉 * M := by
  apply (norm_sum_le ..).trans
  calc
     ∑ β : 𝔉, ‖P.coeff (polynomialBoxExponent β) •
      (ContinuousLinearMap.proj $ (Fintype.equivFin $ PilotBasisIndex q d ℓ ) ((c, β), response) )‖ ≤ ∑ _β : 𝔉, M := by
      apply Finset.sum_le_sum
      intro β _
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul (hP β) (real_pi_projection_norm_le _) (norm_nonneg _) hM).trans_eq $ mul_one M
    _ = Fintype.card 𝔉 * M := 𝖢₄

𝗃 𝔑 ∃ M , 0 < M ∧ ∀ x ∈ unitCube d, ∀ a : 𝔇, ‖𝔛 ἀ‖ ≤ M
𝗃 𝔜 ἀ x hx a
theorem dyadicPilotCoordinate_uniform_bound j :
    𝔑 dyadicPilotCoordinate := by
  obtain ⟨P, hP, hcap⟩ := dyadicPilotPolynomial_coeff_uniform_bound j
  let B := 𝘟 * ( Fintype.card (PolynomialBox d 𝔔) * P)
  refine ⟨max 1 B, 𝘏, ?_⟩
  intro x hx a
  have hscale : 0 ≤ 𝘟 := by dsimp [dyadicPilotScale]; positivity
  rw [dyadicPilotCoordinate, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
  exact (mul_le_mul_of_nonneg_left (pilotPolynomialLinear_norm_le _ _ _ P hP.le
    𝔜 hcap) hscale).trans $ le_max_right ..

𝗇 𝔎 𝗎
theorem preconditionedPilotCoordinate_uniform_bound j :
    𝔑 preconditionedPilotCoordinate := by
  obtain ⟨L, hL, hLb⟩ := dyadicKnownGram_inverse_uniform_bound
  obtain ⟨P, hP, hPb⟩ := dyadicPilotCoordinate_uniform_bound j
  let B := Fintype.card 𝔎 * (L * P)
  refine ⟨max 1 B, 𝘏, ?_⟩
  intro x hx a
  letI : Nonempty 𝔎 := ⟨localPilotRow a⟩
  apply (norm_sum_le ..).trans
  calc
     ∑ β : 𝔎, ‖𝗵₁ (localPilotRow a) β •
        dyadicPilotCoordinate j x 𝔘‖ ≤ ∑ _β : 𝔎, L * P := by
      apply Finset.sum_le_sum
      intro β _
      rw [norm_smul]
      exact mul_le_mul ((matrix_real_entry_norm_le ..).trans $ hLb j x hx )
        (hPb x hx _) (norm_nonneg _) hL.le
    _ = B := by simp [B]
    _ ≤ max 1 B := le_max_right ..

𝗇 𝔖 ContinuousLinearMap.norm_pi_le_of_le (fun _ => real_pi_projection_norm_le _) zero_le_one
𝗃 𝔞 ‖𝔐 ἀ j‖ ≤ 1
theorem incrementGlobalCurrent_norm_le j :
    𝔞 incrementGlobalCurrent :=
  𝔖

theorem incrementGlobalParent_norm_le j :
    𝔞 incrementGlobalParent :=
  𝔖

𝗃 𝔠 ἀ $ anchoredFinIndex i
𝗇 𝔊 Sum.inr 𝔠 Sum.inr
𝗇 𝔍 Sum.inr 𝔠 Sum.inl
𝗇 𝔏 max C P
𝗇 𝔙 𝚂₁
𝗇 𝔚 le_max_right 1 𝔏
theorem incrementPilotCoordinate_uniform_bound (j : ℕ) :
    ∃ M : ℝ, 𝚌 ∧ ∀ x ∈ unitCube d, ‖incrementPilotCoordinate (ℓ := ℓ) j x‖ ≤ M := by
  obtain ⟨C, hC, hCb⟩ := 𝔐 preconditionedPilotCoordinate_uniform_bound j
  obtain ⟨P, hP, hPb⟩ := 𝔐 preconditionedPilotCoordinate_uniform_bound 𝔈
  let M := max 1 𝔏
  have hM : 𝚌 := zero_lt_one.trans_le 𝔙
  refine ⟨M, hM, ?_⟩
  intro x hx
  have hCM : C ≤ M := (le_max_left C P).trans 𝔚
  have hPM : P ≤ M := (le_max_right C P).trans 𝔚
  have hOne : 𝔞 incrementGlobalOne := real_pi_projection_norm_le _
  have hc (a : 𝔇) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      $ (mul_le_mul 𝔜 hCb (incrementGlobalCurrent_norm_le j) (norm_nonneg _) hC.le).trans
        $ by simpa only [mul_one] using hCM
  have hp (a : 𝔇) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      $ (mul_le_mul 𝔜 hPb (incrementGlobalParent_norm_le j) (norm_nonneg _) hP.le).trans
        $ by simpa only [mul_one] using hPM
  apply ContinuousLinearMap.norm_pi_le_of_le _ hM.le
  intro i
  let a := (Fintype.equivFin 𝔗).symm i
  change ‖𝔛 incrementPilotFreeCoordinate‖ ≤ M
  cases a with
  | inl a =>
    cases a with
    | inl a => exact hc _
    | inr a =>
      simp only [incrementPilotFreeCoordinate]
      split_ifs
      · exact hOne.trans 𝔙
      · simpa only [norm_zero] using hM.le
      · exact hp $ Sum.inl (anchoredFinIndex a.2.1, anchoredFinIndex a.2.2)
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    simp only [incrementPilotFreeCoordinate]
    split_ifs
    · simpa only [norm_zero] using hM.le
    · exact hp 𝔊
    · exact hp 𝔍
    · exact hc 𝔊
    · exact hc 𝔍
