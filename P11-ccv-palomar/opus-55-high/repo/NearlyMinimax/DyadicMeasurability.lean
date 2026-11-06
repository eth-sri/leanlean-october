module

public import NearlyMinimax.DyadicApproximation
public import NearlyMinimax.IncrementPilotFeatures
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Joint Borel measurability of the actual anchored charts and pilot fields. -/

𝛎
𝚺
𝚨

theorem dyadicNormalizedAnchor_measurable j :
    Measurable $ dyadicNormalizedAnchor (d := d) j := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_const.mul $ (measurable_pi_apply i).sub
    $ (measurable_of_countable fun c => regularGridCorner 𝘷 c i ).comp
      $ regular_grid_cell_measurable _ 𝖠₃

theorem dyadicAnchoredFeature_joint_measurable j (γ : 𝗎) :
    Measurable fun z : 𝙩 => dyadicAnchoredFeature j z.1 z.2 γ := by
  apply Continuous.measurable
  apply 𝙰₁
  fun_prop

theorem dyadic_cell_pair_measurable j :
    MeasurableSet {z : 𝙩 | z.2 ∈ dyadicPilotCell j z.1} := measurableSet_eq_fun ((regular_grid_cell_measurable _ 𝖠₃ ).comp measurable_snd)
    $ (regular_grid_cell_measurable _ 𝖠₃ ).comp measurable_fst

theorem matrix_nonsing_inverse_measurable [Fintype ι] [DecidableEq ι] :
    Measurable fun A : Matrix ι ι ℝ => A⁻¹ := by
  apply Measurable.of_eval_matrix
  intro i k
  have hd : Measurable fun A : Matrix ι ι ℝ => A.det := continuous_id.matrix_det.measurable
  convert hd.inv.mul continuous_id.matrix_adjugate.measurable.eval_matrix using 1
  funext A
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rfl

theorem dyadicKnownGram_measurable j :
    Measurable $ dyadicKnownGram (d := d) (ℓ := ℓ) j := by
  rw [ funext $ dyadicKnownGram_eq_normalized j ]
  exact anchoredGram_continuous.measurable.comp $ dyadicNormalizedAnchor_measurable j

𝗃 𝔈 ἀ (ℓ := ℓ)
theorem dyadicKnownGram_inverse_measurable j :
    Measurable fun x : Covariate d => (𝔈 dyadicKnownGram j x)⁻¹ :=
  matrix_nonsing_inverse_measurable.comp $ dyadicKnownGram_measurable j

𝗇 𝔄 Covariate d × Observation d
𝗃 𝔅 Measurable fun v : 𝔄 => ἀ j v.1 a v.2
section

variable (j)
    (a : 𝗬₂)

𝗇 𝔇 measurable_fst.prodMk $ measurable_fst.comp measurable_snd
theorem dyadicPilotScalar_joint_measurable :
    𝔅 dyadicPilotScalar := by
  have hpair : Measurable fun v : 𝔄 => (v.1, v.2.1) :=
    𝔇
  have hφ (γ : 𝗎) := (dyadicAnchoredFeature_joint_measurable j γ).comp hpair
  cases a with
  | inl a => exact (hφ a.1).mul $ hφ a.2
  | inr a =>
    cases a with
    | inl γ => exact (measurable_snd.comp measurable_snd).mul $ hφ γ
    | inr γ => exact hφ γ

theorem dyadicPilotFeature_joint_measurable :
    𝔅 dyadicPilotFeature := by
  let S := {v : 𝔄 | v.2.1 ∈ dyadicPilotCell j v.1}
  have hS : MeasurableSet S := (dyadic_cell_pair_measurable j).preimage
    𝔇
  have h : Measurable fun v => 𝘟 *
      S.indicator (fun v => dyadicPilotScalar j v.1 a v.2) v :=
    measurable_const.mul $ (dyadicPilotScalar_joint_measurable j a).indicator hS
  assumption

theorem preconditionedPilotFeature_joint_measurable :
    𝔅 preconditionedPilotFeature := by
  apply Finset.measurable_sum
  intro β _
  exact (((dyadicKnownGram_inverse_measurable j).eval_matrix ).comp
    measurable_fst).mul $ dyadicPilotFeature_joint_measurable j $ localPilotReplaceRow a β

end

theorem dyadicIncrementFeature_joint_measurable j
    (a : incrementVariables 𝚃) :
    𝔅 dyadicIncrementFeature := by
  cases a with
  | inl a =>
    cases a with
    | inl a => exact preconditionedPilotFeature_joint_measurable j _
    | inr a =>
      change Measurable fun v : 𝔄 => if 𝘠 then
         if a.2.1 = a.2.2 then 1 else 0 else
        preconditionedPilotFeature 𝘮 v.1
          (Sum.inl (anchoredFinIndex a.2.1, anchoredFinIndex a.2.2)) v.2
      split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_joint_measurable ..
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    change Measurable fun v : 𝔄 => if parent && j == 0 then 0 else
      preconditionedPilotFeature (if parent then 𝘮 else j) v.1
        (if response then Sum.inr $ Sum.inr $ anchoredFinIndex i
          else Sum.inr $ Sum.inl $ anchoredFinIndex i ) v.2
    split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_joint_measurable ..

theorem dyadicIncrementRawVector_joint_measurable j :
    Measurable fun v : 𝔄 => 𝔈 dyadicIncrementRawVector j v.1 v.2 :=
  measurable_pi_iff.mpr fun _ => dyadicIncrementFeature_joint_measurable j _

theorem dyadicIncrementRawMean_measurable C
    (θ : RegressionParameter d) (hθ : 𝙟) j :
    Measurable $ 𝔈 dyadicIncrementRawMean θ j := by
  let := 𝙱
  apply measurable_pi_iff.mpr
  intro a
  exact (((dyadicIncrementRawVector_joint_measurable j).eval ).stronglyMeasurable.integral_prod_right'
    ).measurable
