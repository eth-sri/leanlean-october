module
public import Mathlib
public import NearlyMinimax.SaddleAsymptotics
public import NearlyMinimax.PaperGoals
public import NearlyMinimax.DyadicPilotRows
public import NearlyMinimax.PairPilotAssumptions
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
section
section
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
variable {d ℓ : ℕ}
theorem bounded_rpow_le_linear (r M s : ℝ) (hr : 0 ≤ r) (hrM : r ≤ M) (hs : 1 ≤ s) :
    r ^ s ≤ max 1 (M ^ s) * r := by
  by_cases hr1 : r ≤ 1
  · exact (Real.rpow_le_self_of_le_one hr hr1 hs).trans
      (by simpa using mul_le_mul_of_nonneg_right (le_max_left 1 (M ^ s)) hr)
  · have h1r  := le_of_not_ge hr1
    calc
      r ^ s ≤ M ^ s := Real.rpow_le_rpow hr hrM (zero_le_one.trans hs)
      _ ≤ M ^ s * r := by simpa using mul_le_mul_of_nonneg_left h1r (Real.rpow_nonneg (hr.trans hrM) s)
      _ ≤ max 1 (M ^ s) * r := mul_le_mul_of_nonneg_right (le_max_right _ _) hr
theorem anchoredTransport_euclidean_norm  (c ) :
    ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredTransport d ℓ *ᵥ c)‖ ≤
      (1 / 2) * ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ := by
  have h := Matrix.l2_opNorm_mulVec (anchoredTransport d ℓ)
    ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c)
  have h' : ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredTransport d ℓ *ᵥ c)‖ ≤
      ‖anchoredTransport d ℓ‖ * ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ := by
    simpa [EuclideanSpace.equiv] using h
  apply h'.trans
  have h_anchoredTransport_norm_le_half : ‖anchoredTransport d ℓ‖ ≤ 1 / 2 := by
    classical
    rw [anchoredTransport, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
    intro γ
    have h_anchoredTransport_entry_bound : |(2 : ℝ) ^ (-(anchoredDegree γ : ℤ))| ≤ 1 / 2 := by
      rw [_root_.zpow_neg, zpow_natCast, abs_inv, abs_pow,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hpow : (2 : ℝ) ≤ 2 ^ anchoredDegree γ := by
        simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (show 1 ≤ anchoredDegree γ from γ.property.1)
      simpa only [one_div] using
        (inv_le_inv₀ (by norm_num : (0 : ℝ) < 2 ^ anchoredDegree γ) (by norm_num)).mpr hpow
    exact h_anchoredTransport_entry_bound
  exact mul_le_mul_of_nonneg_right h_anchoredTransport_norm_le_half (norm_nonneg _)
def dyadicPopulationIncrement  (θ : RegressionParameter d) (x : Covariate d) :
    ℕ → AnchoredIndex d ℓ → ℝ := anchoredIncrement (fun j => dyadicPopulationFit θ j x)
theorem dyadicPopulationIncrement_error_identity  (θ x c j) :
    dyadicPopulationIncrement θ x (j + 1) =
      dyadicPopulationFit θ (j + 1) x - dyadicTaylorCoefficients c (j + 1) -
        anchoredTransport d ℓ *ᵥ (dyadicPopulationFit θ j x - dyadicTaylorCoefficients c j) := by
  rw [dyadicTaylorCoefficients_succ, Matrix.mulVec_sub]
  unfold dyadicPopulationIncrement anchoredIncrement
  abel
theorem dyadic_inverse_scale_succ (j ) :
    ((2 : ℝ) ^ j)⁻¹ = 2 * ((2 : ℝ) ^ (j + 1))⁻¹ := by
  rw [pow_succ]
  field_simp
theorem dyadicPopulationIncrement_telescope  (θ : RegressionParameter d)
    (x z : Covariate d) (J : ℕ) :
    dyadicAnchoredFeature J x z ⬝ᵥ dyadicPopulationFit (ℓ := ℓ) θ J x =
      ∑ j ∈ Finset.range (J + 1), dyadicAnchoredFeature j x z ⬝ᵥ dyadicPopulationIncrement (ℓ := ℓ) θ x j :=
  (anchored_increment_telescope (fun j => dyadicPopulationFit θ j x) x z J).symm
theorem dyadicCellAffine_same_cell  (j : ℕ) (x y : Covariate d)
    (hcell : y ∈ dyadicPilotCell j x) :
    dyadicCellAffine j x (dyadicNormalizedAnchor j y) = y := by
  have hc : regularGridCell (↑2 ^ j) (by positivity) y =
      regularGridCell (2 ^ j) (by positivity) x := hcell
  have h_dyadicCellAffine_anchor : dyadicCellAffine j y (dyadicNormalizedAnchor j y) = y := by
    funext i
    simp only [dyadicCellAffine, gridAffine, dyadicNormalizedAnchor, gridNormalizedAnchor,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  simpa only [dyadicCellAffine, hc] using h_dyadicCellAffine_anchor
theorem dyadicPopulationFit_physical_evaluation  (j )
    (x y : Covariate d) (hcell : y ∈ dyadicPilotCell j x) (c : AnchoredIndex d ℓ → ℝ) :
    anchoredFitPolynomial (dyadicNormalizedAnchor j x) c (dyadicNormalizedAnchor j y) =
      dyadicAnchoredFeature j x y ⬝ᵥ c := by
  apply Finset.sum_congr rfl
  intro γ _
  have h := dyadicAnchoredFeature_affine j x (dyadicNormalizedAnchor j y) γ
  change dyadicAnchoredFeature j x (dyadicCellAffine j x (dyadicNormalizedAnchor j y)) γ = _ at h
  rw [dyadicCellAffine_same_cell j x y hcell] at h
  change dyadicAnchoredFeature j x y γ =
    anchoredFeature (dyadicNormalizedAnchor j x) (dyadicNormalizedAnchor j y) γ at h
  rw [h]
  ring
theorem positive_rpow_times_distance (h s r : ℝ) (hh : 0 < h) :
    h ^ s * r = h * r * h ^ (s - 1) := by
  have he : s = s - 1 + 1 := by ring
  conv_lhs => rw [he, Real.rpow_add hh, Real.rpow_one]
  ring
theorem dyadicAnchoredFeature_joint_measurable  (j : ℕ) (γ : AnchoredIndex d ℓ) :
    Measurable (fun z : Covariate d × Covariate d => dyadicAnchoredFeature j z.1 z.2 γ) := by
  apply Continuous.measurable
  apply (anchoredMonomial_continuous γ).comp
  apply continuous_pi
  intro i
  exact continuous_const.mul (((continuous_apply i).comp continuous_snd).sub
    ((continuous_apply i).comp continuous_fst))
theorem matrix_nonsing_inverse_measurable {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun A : Matrix ι ι ℝ => A⁻¹) := by
  apply Measurable.of_eval_matrix
  intro i k
  have hd : Measurable (fun A : Matrix ι ι ℝ => A.det) := continuous_id.matrix_det.measurable
  have ha : Measurable (fun A : Matrix ι ι ℝ => A.adjugate i k) :=
    continuous_id.matrix_adjugate.measurable.eval_matrix
  convert hd.inv.mul ha using 1
  funext A
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rfl
theorem dyadicKnownGram_inverse_measurable  (j ) :
    Measurable (fun x : Covariate d => (dyadicKnownGram (ℓ := ℓ) j x)⁻¹) :=
  have h_dyadicKnownGram_measurable {d} : Measurable (dyadicKnownGram (d := d) (ℓ := ℓ) j) := by
    rw [funext (dyadicKnownGram_eq_normalized j)]
    have h_dyadicNormalizedAnchor_measurable {d} : Measurable (dyadicNormalizedAnchor (d := d) j) := by
      apply measurable_pi_iff.mpr
      intro i
      exact measurable_const.mul ((measurable_pi_apply i).sub
        ((measurable_of_countable (fun c => regularGridCorner (2 ^ j) c i)).comp
          (regular_grid_cell_measurable _ (by positivity))))
    exact anchoredGram_continuous.measurable.comp h_dyadicNormalizedAnchor_measurable
  matrix_nonsing_inverse_measurable.comp h_dyadicKnownGram_measurable
theorem preconditionedPilotFeature_joint_measurable  (j : ℕ) (a : LocalPilotIndex d ℓ) :
    Measurable (fun v : Covariate d × Observation d => preconditionedPilotFeature j v.1 a v.2) := by
  apply Finset.measurable_sum
  intro β _
  have h_dyadicPilotFeature_joint_measurable {d : ℕ} {ℓ : ℕ} (a : LocalPilotIndex d ℓ) : Measurable (fun v : Covariate d × Observation d => dyadicPilotFeature j v.1 a v.2) := by
    let S := {v : Covariate d × Observation d | v.2.1 ∈ dyadicPilotCell j v.1}
    have h_dyadic_cell_pair_measurable : MeasurableSet {z : Covariate d × Covariate d | z.2 ∈ dyadicPilotCell j z.1} := by
      exact measurableSet_eq_fun ((regular_grid_cell_measurable _ (by positivity)).comp measurable_snd)
        ((regular_grid_cell_measurable _ (by positivity)).comp measurable_fst)
    have hS : MeasurableSet S := h_dyadic_cell_pair_measurable.preimage
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h_dyadicPilotScalar_joint_measurable : Measurable (fun v : Covariate d × Observation d => dyadicPilotScalar j v.1 a v.2) := by
      have hpair : Measurable (fun v : Covariate d × Observation d => (v.1, v.2.1)) :=
        measurable_fst.prodMk (measurable_fst.comp measurable_snd)
      have hφ (γ : AnchoredIndex d ℓ) := (dyadicAnchoredFeature_joint_measurable j γ).comp hpair
      cases a with
      | inl a => exact (hφ a.1).mul (hφ a.2)
      | inr a =>
        cases a with
        | inl γ => exact (measurable_snd.comp measurable_snd).mul (hφ γ)
        | inr γ => exact hφ γ
    have h : Measurable (fun v : Covariate d × Observation d => dyadicPilotScale d j *
        S.indicator (fun v => dyadicPilotScalar j v.1 a v.2) v) :=
      measurable_const.mul (h_dyadicPilotScalar_joint_measurable.indicator hS)
    convert h using 1
    funext v
    by_cases hv : v.2.1 ∈ dyadicPilotCell j v.1 <;> simp [dyadicPilotFeature, S, hv]
  exact (((dyadicKnownGram_inverse_measurable j).eval_matrix (i := localPilotRow a) (j := β)).comp
    measurable_fst).mul (h_dyadicPilotFeature_joint_measurable (localPilotReplaceRow a β))
theorem dyadicIncrementFeature_joint_measurable  (j )
    (a : incrementVariables (anchoredDimension d ℓ)) :
    Measurable (fun v : Covariate d × Observation d => dyadicIncrementFeature j v.1 a v.2) := by
  cases a with
  | inl a =>
    cases a with
    | inl a => exact preconditionedPilotFeature_joint_measurable j _
    | inr a =>
      change Measurable (fun v : Covariate d × Observation d => if j = 0 then
        (if a.2.1 = a.2.2 then ↑1 else 0) else
        preconditionedPilotFeature (j - 1) v.1
          (Sum.inl (anchoredFinIndex a.2.1, anchoredFinIndex a.2.2)) v.2)
      split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_joint_measurable _ _
  | inr a =>
    rcases a with ⟨parent, response, i⟩
    change Measurable (fun v : Covariate d × Observation d => if parent && (j == 0) then ↑0 else
      preconditionedPilotFeature (if parent then j - 1 else j) v.1
        (if response then Sum.inr (Sum.inr (anchoredFinIndex i))
          else Sum.inr (Sum.inl (anchoredFinIndex i))) v.2)
    split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_joint_measurable _ _
theorem dyadicIncrementRawVector_joint_measurable  (j : ℕ) :
    Measurable (fun v : Covariate d × Observation d => dyadicIncrementRawVector (ℓ := ℓ) j v.1 v.2) :=
  measurable_pi_iff.mpr (fun _ => dyadicIncrementFeature_joint_measurable j _)
theorem dyadicIncrementRawMean_measurable  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) :
    Measurable (dyadicIncrementRawMean (ℓ := ℓ) θ j) := by
  let := observationLaw_isProbability C θ hθ
  apply measurable_pi_iff.mpr
  intro a
  exact (((dyadicIncrementRawVector_joint_measurable (ℓ := ℓ) j).eval (a := a)).stronglyMeasurable.integral_prod_right'
    (ν := observationLaw θ)).measurable
end NearlyMinimax
end
section
open Set Filter
open scoped BigOperators Topology
namespace NearlyMinimax
def quadraticProfile (S z : ℝ) : ℝ := S / 4 + (S - z) ^ 2 / S
theorem quadraticProfile_lower  (hS : 0 < S) :
    S / 4 ≤ quadraticProfile S z := le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hS.le)
theorem quadraticProfile_degree_scale_bound {L S z c C : ℝ}
    (hL : 1 ≤ L) (hc : 0 < c) (hC : 0 ≤ C)
    (hSl : c * Real.sqrt L ≤ S) (hSu : S ≤ C * Real.sqrt L)
    (hzl : -L ≤ z) (hzu : z ≤ S) :
    quadraticProfile S z ≤ (C / 4 + (C + 1) ^ 2 / c) * L ^ (3 / 2 : ℝ) := by
  have hL₀  := lt_of_lt_of_le zero_lt_one hL
  have hdenom  := mul_pos hc (Real.sqrt_pos.2 hL₀)
  have : S ≤ C * L := hSu.trans (mul_le_mul_of_nonneg_left ((Real.sqrt_le_left hL₀.le).2 (by nlinarith)) hC)
  have : (S - z) ^ 2 / S ≤ ((C + 1) ^ 2 / c) * (L * Real.sqrt L) := by
    have h_sq_div_sqrt_eq_mul_sqrt : L ^ 2 / Real.sqrt L = L * Real.sqrt L := by
      apply (div_eq_iff (Real.sqrt_pos.2 hL₀).ne').2
      rw [mul_assoc, Real.mul_self_sqrt hL₀.le]
      ring
    calc
      _ ≤ (S - z) ^ 2 / (c * Real.sqrt L) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hdenom hSl
      _ ≤ ((C + 1) * L) ^ 2 / (c * Real.sqrt L) :=
        div_le_div_of_nonneg_right ((sq_le_sq₀ (sub_nonneg.2 hzu) (by positivity)).2 (by nlinarith)) hdenom.le
      _ = ((C + 1) ^ 2 / c) * (L ^ 2 / Real.sqrt L) := by ring
      _ = _ := by rw [h_sq_div_sqrt_eq_mul_sqrt]
  have : S / 4 ≤ (C / 4) * (L * Real.sqrt L) := by
    have := mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ C * Real.sqrt L / 4)
    nlinarith
  unfold quadraticProfile
  have h_mul_sqrt_eq_three_halves_power : L * Real.sqrt L = L ^ (3 / 2 : ℝ) := by
    calc
      L * Real.sqrt L = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = L ^ (1 + 1 / 2 : ℝ) := (Real.rpow_add hL₀ 1 (1 / 2)).symm
      _ = L ^ (3 / 2 : ℝ) := by norm_num
  rw [← h_mul_sqrt_eq_three_halves_power]
  nlinarith
def allocationDegreeCoefficient (a β : ℝ) : ℝ :=
  β * ((2 * a) / 4 + (2 * a + 1) ^ 2 / (a / 2))
theorem eventually_allocation_degree_bound {a β : ℝ} (ha : 0 < a) (hβ : 0 ≤ β)
    (C : ℝ) (A : ℝ → Finset ℕ) (z : ℝ → ℕ → ℝ)
    (hrange : ∀ᶠ x : ℝ in atTop, ∀ j ∈ A x,
      -Real.log x ≤ z x j ∧ z x j ≤ allocationWidth a C x) :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ A x,
      (Nat.floor (β * quadraticProfile (allocationWidth a C x) (z x j)) : ℝ) ≤
        allocationDegreeCoefficient a β * (Real.log x) ^ (3 / 2 : ℝ) := by
  have h_eventually_allocationWidth_comparable : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x ∧
      (a / 2) * Real.sqrt (Real.log x) ≤ allocationWidth a C x ∧
        allocationWidth a C x ≤ 2 * a * Real.sqrt (Real.log x) := by
    have ht := allocationWidth_div_sqrt_log_limit a C
    filter_upwards [ht.eventually (lt_mem_nhds (by linarith : a / 2 < a)),
      ht.eventually (gt_mem_nhds (by linarith : a < 2 * a)),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop ↑1)] with x hlo hhi hx
    have hp : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hx)
    exact ⟨hx, ((lt_div_iff₀ hp).1 hlo).le, ((div_lt_iff₀ hp).1 hhi).le⟩
  filter_upwards [h_eventually_allocationWidth_comparable, hrange] with x hx hz
  intro j hj
  have hp := quadraticProfile_degree_scale_bound hx.1 (by positivity : 0 < a / 2)
    (by positivity : 0 ≤ 2 * a) hx.2.1 hx.2.2 (hz j hj).1 (hz j hj).2
  have hS : 0 < allocationWidth a C x :=
    (mul_pos (by positivity : 0 < a / 2) (Real.sqrt_pos.2 (by linarith : 0 < Real.log x))).trans_le hx.2.1
  have hQ : 0 ≤ quadraticProfile (allocationWidth a C x) (z x j) :=
    (by positivity : ↑0 ≤ allocationWidth a C x / 4).trans (quadraticProfile_lower hS)
  unfold allocationDegreeCoefficient
  exact (Nat.floor_le (mul_nonneg hβ hQ)).trans (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hp hβ))
def terminalAllocationLevel (δ a C H γ x : ℝ) : ℕ :=
  Nat.floor ((Real.log x + candidateTerminalDepth a C H γ x) / δ)
def allocationLevelPosition (δ a C H x : ℝ) (j : ℕ) : ℝ :=
  δ * ↑j - Real.log x + Real.log (H * allocationWidth a C x)
theorem eventually_actual_allocation_level_range {δ a H γ : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hH : 0 < H) (hγ : 0 ≤ γ) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ j ∈ Finset.range (terminalAllocationLevel δ a C H γ x + 1),
      -Real.log x ≤ allocationLevelPosition δ a C H x j ∧
        allocationLevelPosition δ a C H x j ≤ allocationWidth a C x := by
  have hw := allocationWidth_tendsto_atTop ha C
  filter_upwards [hw.eventually (eventually_ge_atTop ↑1),
    (hw.const_mul_atTop hH).eventually (eventually_ge_atTop ↑1),
    eventually_terminal_cell_log_nonneg ha hH C γ] with x hx hHx hLT
  intro j hj
  have := Finset.mem_range.1 hj
  have : 0 ≤ Real.log (H * allocationWidth a C x) := Real.log_nonneg hHx
  have hjreal : ↑j ≤ (terminalAllocationLevel δ a C H γ x : ℝ) := by exact_mod_cast (by omega)
  have hum := mul_le_mul_of_nonneg_left (Nat.floor_le (div_nonneg hLT hδ.le)) hδ.le
  have hmj := mul_le_mul_of_nonneg_left hjreal hδ.le
  have he : δ * ((Real.log x + candidateTerminalDepth a C H γ x) / δ) =
      Real.log x + candidateTerminalDepth a C H γ x := by field_simp
  rw [he] at hum
  unfold terminalAllocationLevel at hmj
  unfold allocationLevelPosition
  constructor
  · linarith [mul_nonneg hδ.le (Nat.cast_nonneg j)]
  · unfold candidateTerminalDepth at hum hmj
    linarith [mul_nonneg hγ (Real.log_nonneg hx)]
end NearlyMinimax
end
set_option backward.isDefEq.respectTransparency false
namespace NearlyMinimax.GaussianSum
open MeasureTheory Set
open scoped BigOperators
theorem gaussian_sum_range_le (c ) (hc : 0 < c) (N ) :
    (∑ k ∈ Finset.range N, Real.exp (-c * k ^ 2)) ≤
      1 + Real.sqrt (Real.pi / c) / 2 := by
  cases N with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
  | succ N =>
      rw [Finset.sum_range_succ']
      have hf : AntitoneOn (fun x => Real.exp (-c * x ^ 2))
          (Icc 0 (0 + N)) := by
        have h_gaussian_antitone : AntitoneOn (fun x => Real.exp (-c * x ^ 2)) (Ici 0) := by
          intro x hx y hy hxy
          apply Real.exp_le_exp.mpr
          have hs  := (sq_le_sq₀ hx hy).2 hxy
          nlinarith [mul_le_mul_of_nonneg_left hs hc.le]
        simpa using h_gaussian_antitone.mono (Icc_subset_Ici_self :
          Icc (0 : ℝ) (N : ℝ) ⊆ Ici 0)
      have hcomp' := hf.sum_le_integral
      have hInt : (∫ x in 0..N, Real.exp (-c * x ^ 2)) ≤
          (∫ x in Ioi 0, Real.exp (-c * x ^ 2)) := by
        rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
        apply setIntegral_mono_set (integrable_exp_neg_mul_sq hc).integrableOn
          (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
        exact Filter.Eventually.of_forall fun x hx => hx.1
      have hcomp : (∑ k ∈ Finset.range N,
          Real.exp (-c * ((k + 1 ) : ℝ) ^ 2)) ≤
          (∫ x in Ioi 0, Real.exp (-c * x ^ 2)) := by
        simpa using (by simpa using hcomp' :
          (∑ k ∈ Finset.range N, Real.exp (-c * ((k + 1 ) : ℝ) ^ 2)) ≤
            (∫ x in 0..N, Real.exp (-c * x ^ 2))).trans hInt
      calc
        (∑ k ∈ Finset.range N, Real.exp (-c * ((k + 1 : ℕ) : ℝ) ^ 2)) +
            Real.exp (-c * ((0 : ℕ) : ℝ) ^ 2)
          ≤ (∫ x in Ioi (0 : ℝ), Real.exp (-c * x ^ 2)) + 1 := by
              simpa using add_le_add_right hcomp 1
        _ = 1 + Real.sqrt (Real.pi / c) / 2 := by
              rw [integral_gaussian_Ioi]
              ring
theorem gaussian_centered_sum (S : Finset ℝ) {δ c : ℝ} (a )
    (hδ : 0 < δ) (hc : 0 < c)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, Real.exp (-c * (x - a) ^ 2)) ≤
      2 + Real.sqrt (Real.pi / c) / δ := by
  have h_gaussian_half_sum (S : Finset ℝ) (hδ : 0 < δ) (hc : 0 < c) (hnonneg : ∀ x ∈ S, 0 ≤ x) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) : (∑ x ∈ S, Real.exp (-c * x ^ 2)) ≤
      1 + Real.sqrt (Real.pi / c) / δ / 2 := by
    have h_separated_gaussian_sum_le : ∑ x ∈ S, Real.exp (-c * x ^ 2) ≤
        ∑ k ∈ Finset.range S.card, Real.exp (-(c * δ ^ 2) * k ^ 2) := by
      have hsum : ∑ x ∈ S, Real.exp (-c * x ^ 2) =
          ∑ k : Fin S.card, Real.exp (-c * (S.orderEmbOfFin rfl k) ^ 2) := by
        simpa only [Finset.sum_map, RelEmbedding.coe_toEmbedding] using
          congrArg (fun t => ∑ x ∈ t, Real.exp (-c * x ^ 2))
            (S.map_orderEmbOfFin_univ (k := S.card) rfl).symm
      rw [hsum]
      calc
        (∑ k : Fin S.card, Real.exp (-c * (S.orderEmbOfFin rfl k) ^ 2)) ≤
            ∑ k : Fin S.card, Real.exp (-(c * δ ^ 2) * k.val ^ 2) := by
          apply Finset.sum_le_sum
          intro k _
          apply Real.exp_le_exp.mpr
          have hn := hnonneg _ (S.orderEmbOfFin_mem rfl k)
          have hrank : ∀ (n : ℕ) (hn : n < S.card),
              n * δ ≤ S.orderEmbOfFin rfl ⟨n, hn⟩ := by
            intro n
            induction n with
            | zero =>
              intro hn
              simpa using hnonneg _ (S.orderEmbOfFin_mem rfl ⟨0, hn⟩)
            | succ n ih =>
              intro hn
              have hn' : n < S.card := Nat.lt_trans (Nat.lt_succ_self n) hn
              have hlt : S.orderEmbOfFin rfl ⟨n, hn'⟩ <
                  S.orderEmbOfFin rfl ⟨n + 1, hn⟩ :=
                (S.orderEmbOfFin rfl).strictMono (by simp)
              have hstep := hsep _ (S.orderEmbOfFin_mem rfl ⟨n + 1, hn⟩)
                _ (S.orderEmbOfFin_mem rfl ⟨n, hn'⟩) (ne_of_gt hlt)
              rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)] at hstep
              have := ih hn'
              push_cast
              linarith
          have hk := (hrank k.val k.isLt)
          have := (sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg _) hδ.le) hn).mpr hk
          nlinarith
        _ = ∑ k ∈ Finset.range S.card, Real.exp (-(c * δ ^ 2) * k ^ 2) := by
          rw [Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro k hk
          simp [Finset.mem_range.mp hk]
    calc
      _ ≤ ∑ k ∈ Finset.range S.card,
            Real.exp (-(c * δ ^ 2) * k ^ 2) :=
          h_separated_gaussian_sum_le
      _ ≤ 1 + Real.sqrt (Real.pi / (c * δ ^ 2)) / 2 :=
          gaussian_sum_range_le (c * δ ^ 2) (by positivity) S.card
      _ = 1 + Real.sqrt (Real.pi / c) / δ / 2 := by
          have h_gaussian_constant_spacing : Real.sqrt (Real.pi / (c * δ ^ 2)) = Real.sqrt (Real.pi / c) / δ := by
            have halg : Real.pi / (c * δ ^ 2) = (Real.pi / c) / δ ^ 2 := by
              field_simp
            rw [halg, Real.sqrt_div (div_nonneg Real.pi_pos.le hc.le),
              Real.sqrt_sq_eq_abs, abs_of_pos hδ]
          rw [h_gaussian_constant_spacing]
  classical
  let P := S.filter (fun x => a ≤ x)
  let N := S.filter (fun x => ¬a ≤ x)
  have hPsep : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hxy
    exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  have hNsep : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hxy
    exact hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  have h_separated_translate : ∀ u ∈ P.image (fun x => x - a), ∀ v ∈ P.image (fun x => x - a),
      u ≠ v → δ ≤ |u - v| := by
    classical
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    have hxy : x ≠ y := by
      intro h
      exact huv (congrArg (fun z => z - a) h)
    have h := hPsep x hx y hy hxy
    convert h using 1
    congr 1
    ring
  have hP := h_gaussian_half_sum (P.image (fun x => x - a)) hδ hc (by intro u hu; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu; exact sub_nonneg.mpr (Finset.mem_filter.mp hx).2)
    h_separated_translate
  have h_separated_reflect : ∀ u ∈ N.image (fun x => a - x), ∀ v ∈ N.image (fun x => a - x),
      u ≠ v → δ ≤ |u - v| := by
    classical
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    have hxy : x ≠ y := by
      intro h
      exact huv (congrArg (fun z => a - z) h)
    have h := hNsep x hx y hy hxy
    rw [abs_sub_comm x y] at h
    convert h using 1
    congr 1
    ring
  have hN := h_gaussian_half_sum (N.image (fun x => a - x)) hδ hc (by intro u hu; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu; exact sub_nonneg.mpr (not_le.mp (Finset.mem_filter.mp hx).2).le)
    h_separated_reflect
  rw [Finset.sum_image (by intro x hx y hy h; linarith)] at hP
  rw [Finset.sum_image (by intro x hx y hy h; linarith)] at hN
  have : (∑ x ∈ N, Real.exp (-c * (x - a) ^ 2)) ≤
      1 + Real.sqrt (Real.pi / c) / δ / 2 := by
    convert hN using 1
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    ring
  have hsplit  := (Finset.sum_filter_add_sum_filter_not S (fun x => a ≤ x)
      (fun x => Real.exp (-c * (x - a) ^ 2))).symm
  rw [hsplit]
  linarith
theorem normalized_gaussian_lattice_sum_le (A : Finset ℕ) (u₀ a b S )
    (ha : 0 < a) (hb : 0 < b) (hS : 1 ≤ S) :
    (∑ j ∈ A, Real.exp (-a * (u₀ + j * b) ^ 2 / S)) / Real.sqrt S ≤
      2 + Real.sqrt (Real.pi / a) / b := by
  have h_gaussian_lattice_sum_le : (∑ j ∈ A, Real.exp (-a * (u₀ + j * b) ^ 2 / S)) ≤
      (2 + Real.sqrt (Real.pi / a) / b) * Real.sqrt S := by
    classical
    have hS₀  := lt_of_lt_of_le zero_lt_one hS
    have h_arithmetic_lattice_separated : ∀ x ∈ A.image (fun j : ℕ => u₀ + j * b),
        ∀ y ∈ A.image (fun j : ℕ => u₀ + ↑j * b),
          x ≠ y → b ≤ |x - y| := by
      classical
      intro x hx y hy hxy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have hij : i ≠ j := by intro he; apply hxy; rw [he]
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
        have hdiff : b ≤ u₀ + (j : ℝ) * b - (u₀ + (i : ℝ) * b) := by nlinarith
        exact hdiff.trans (le_abs_self _ |>.trans_eq (abs_sub_comm _ _))
      · have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
        have hdiff : b ≤ u₀ + (i : ℝ) * b - (u₀ + (j : ℝ) * b) := by nlinarith
        exact hdiff.trans (le_abs_self _)
    have hgauss := gaussian_centered_sum
      (A.image (fun j : ℕ => u₀ + ↑j * b)) ↑0 hb (div_pos ha hS₀)
      h_arithmetic_lattice_separated
    have hinj : Set.InjOn (fun j : ℕ => u₀ + ↑j * b) A := by
      intro i hi j hj he
      have hcast : (i : ℝ) = (j : ℝ) := by nlinarith
      exact_mod_cast hcast
    rw [Finset.sum_image hinj] at hgauss
    simp only [sub_zero] at hgauss
    have hsum : (∑ j ∈ A, Real.exp (-a * (u₀ + j * b) ^ 2 / S)) =
        ∑ j ∈ A, Real.exp (-(a / S) * (u₀ + j * b) ^ 2) := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      ring
    rw [hsum]
    have halg : Real.pi / (a / S) = Real.pi / a * S := by field_simp
    rw [halg, Real.sqrt_mul (div_nonneg Real.pi_pos.le ha.le)] at hgauss
    have  := Real.one_le_sqrt.2 hS
    calc
      _ ≤ 2 + Real.sqrt (Real.pi / a) * Real.sqrt S / b := hgauss
      _ ≤ (2 + Real.sqrt (Real.pi / a) / b) * Real.sqrt S := by
        rw [show Real.sqrt (Real.pi / a) * Real.sqrt S / b =
          (Real.sqrt (Real.pi / a) / b) * Real.sqrt S by ring]
        nlinarith
  exact (div_le_iff₀ (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hS))).2 h_gaussian_lattice_sum_le
end NearlyMinimax.GaussianSum
namespace NearlyMinimax
open Set Matrix MeasureTheory MvPolynomial Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology RealInnerProductSpace
variable {d ℓ : ℕ} {S β θ τ : ℝ}
abbrev TotalDegreeIndex (d ℓ : ℕ) :=
  {γ : PolynomialBox d ℓ // (∑ i, (γ i).val) ≤ ℓ}
def totalDegreeSlackEquiv (d ℓ ) :
    TotalDegreeIndex d ℓ ≃ {v : Option (Fin d) → ℕ // ∑ i, v i = ℓ} where
  toFun γ := ⟨fun i => i.casesOn (ℓ - ∑ j, (γ.val j).val) (fun j => (γ.val j).val), by
    rw [Fintype.sum_option]
    exact Nat.sub_add_cancel γ.property⟩
  invFun v := ⟨fun i => ⟨v.val (some i), by
    have hi : v.val (some i) ≤ ∑ j, v.val j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ _)
    rw [v.property] at hi
    omega⟩, by
      have h := v.property
      rw [Fintype.sum_option] at h
      exact Nat.le.intro (by simpa [Nat.add_comm] using h)⟩
  left_inv γ := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl
  right_inv v := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      change ℓ - ∑ j, v.val (some j) = v.val none
      have h := v.property
      rw [Fintype.sum_option] at h
      omega
    | some i => rfl
def anchoredNonzeroEquiv (d ℓ ) : AnchoredIndex d ℓ ≃
    {γ : TotalDegreeIndex d ℓ // ¬ (∑ i, (γ.val i).val) = 0} where
  toFun γ := ⟨⟨γ.val, γ.property.2⟩, ne_of_gt γ.property.1⟩
  invFun γ := ⟨γ.val.val, Nat.pos_of_ne_zero γ.property, γ.val.property⟩
  left_inv γ := by rfl
  right_inv γ := by rfl
theorem anchoredIndex_card (d ℓ ) :
    Fintype.card (AnchoredIndex d ℓ) = (d + ℓ).choose d - 1 := by
  classical
  letI : Unique {γ : TotalDegreeIndex d ℓ // (∑ i, (γ.val i).val) = 0} :=
    { default := ⟨⟨fun _ => 0, by simp⟩, by simp⟩
      uniq := fun γ => by
        apply Subtype.ext
        apply Subtype.ext
        funext i
        apply Fin.ext
        have hi  :=
          Finset.single_le_sum (f := fun j => (γ.val.val j).val)
            (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        rw [γ.property] at hi
        exact Nat.eq_zero_of_le_zero hi }
  have h_totalDegreeIndex_card : Fintype.card (TotalDegreeIndex d ℓ) = (d + ℓ).choose d := by
    rw [Fintype.card_congr ((totalDegreeSlackEquiv d ℓ).trans (Sym.equivNatSumOfFintype (Option (Fin d)) ℓ).symm), Sym.card_sym_eq_choose]
    simp only [Fintype.card_option, Fintype.card_fin]
    have h : d + 1 + ℓ - 1 = d + ℓ := by omega
    rw [h]
    have hc := Nat.choose_symm (show ℓ ≤ d + ℓ by omega)
    simpa only [Nat.add_sub_cancel] using hc.symm
  rw [Fintype.card_congr (anchoredNonzeroEquiv d ℓ),
    Fintype.card_subtype_compl, h_totalDegreeIndex_card, Fintype.card_unique]
theorem anchoredIndex_nonempty_of_one_lt_smoothness  (C : ModelConstants d)
    (hs : 1 < C.smoothness) : Nonempty (AnchoredIndex d C.order) := by
  have horder : 0 < C.order := by
    by_contra h
    have hz : C.order = 0 := by omega
    have hle := C.smoothness_le_order_add_one
    simp only [hz, Nat.cast_zero, zero_add] at hle
    linarith
  exact anchoredIndex_nonempty C.dimension_pos horder
def anchoredFinVector  (v : AnchoredIndex d ℓ → ℝ) :
    Fin (anchoredDimension d ℓ) → ℝ := fun i => v (anchoredFinIndex i)
theorem anchoredFinVector_norm  (v ) :
    ‖(EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm (anchoredFinVector v)‖ =
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm v‖ := by
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin (AnchoredIndex d ℓ))
  have he : e ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm v) =
      (EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm (anchoredFinVector v) := by
    ext i
    rfl
  rw [← he]
  exact e.norm_map _
theorem anchoredFinReindex_mulVec 
    (A v) :
    anchoredFinReindex d ℓ A *ᵥ anchoredFinVector v = anchoredFinVector (A *ᵥ v) := by
  ext i
  simp only [anchoredFinReindex, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
    anchoredFinVector, anchoredFinIndex, Matrix.mulVec, dotProduct]
  exact (Fintype.equivFin (AnchoredIndex d ℓ)).symm.sum_comp
    (fun γ => A (anchoredFinIndex i) γ * v γ)
theorem anchoredFinVector_sub  (v w : AnchoredIndex d ℓ → ℝ) :
    anchoredFinVector (v - w) = anchoredFinVector v - anchoredFinVector w := rfl
theorem dyadicFinPilot_fit  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j x) (hx : x ∈ unitCube d) :
    (dyadicFinPilotGram (ℓ := ℓ) θ j x)⁻¹ *ᵥ
      (dyadicFinPilotMoments θ j x false - θ.regression x • dyadicFinPilotMoments θ j x true) =
        anchoredFinVector (dyadicPopulationFit θ j x) := by
  have h_dyadicFinPilotMoments_eq_actual (t) : dyadicFinPilotMoments (ℓ := ℓ) θ j x t = anchoredFinVector
      ((dyadicKnownGram j x)⁻¹ *ᵥ (if t then dyadicConstantMoment θ j x else dyadicResponseMoment θ j x)) := by
    ext i
    cases t
    all_goals simp only [dyadicFinPilotMoments, Bool.false_eq_true, ↓reduceIte,
      anchoredFinVector]
    all_goals rw [preconditionedPilotPopulation_eq_sum C θ hθ j x hx]
    all_goals simp only [localPilotRow, localPilotReplaceRow, Matrix.mulVec, dotProduct,
      dyadicPilotPopulation_response C θ hθ j x hx, dyadicPilotPopulation_constant C θ hθ]
  rw [h_dyadicFinPilotMoments_eq_actual false,
    h_dyadicFinPilotMoments_eq_actual true]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have h_anchoredFinVector_smul (a : ℝ) (v : AnchoredIndex d ℓ → ℝ) : anchoredFinVector (a • v) = a • anchoredFinVector v := rfl
  rw [← h_anchoredFinVector_smul, ← anchoredFinVector_sub,
    ← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
  have h_anchoredFinReindex_inv (A : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) : (anchoredFinReindex d ℓ A)⁻¹ = anchoredFinReindex d ℓ A⁻¹ := Matrix.inv_reindex _ _ A
  have h_dyadicPopulationFit_preconditioner_cancels j (x : Covariate d) : (dyadicPreconditionedGram (ℓ := ℓ) θ j x)⁻¹ *ᵥ
      ((dyadicKnownGram j x)⁻¹ *ᵥ (dyadicResponseMoment θ j x - θ.regression x • dyadicConstantMoment θ j x)) =
        dyadicPopulationFit θ j x := by
    letI := (dyadicKnownGram_posDef (ℓ := ℓ) j x).isUnit.invertible
    unfold dyadicPreconditionedGram dyadicPopulationFit
    rw [Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible, Matrix.mulVec_mulVec,
      Matrix.mul_assoc _ (dyadicKnownGram j x) (dyadicKnownGram j x)⁻¹,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (dyadicKnownGram_posDef (ℓ := ℓ) j x).isUnit), Matrix.mul_one]
  rw [dyadicFinPilotGram, h_anchoredFinReindex_inv, anchoredFinReindex_mulVec,
    h_dyadicPopulationFit_preconditioner_cancels]
theorem dyadicFinite_increment_eq_actual  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j )
    (x : Covariate d) (hx : x ∈ unitCube d) :
    (dyadicFinPilotGram (ℓ := ℓ) θ j x)⁻¹ *ᵥ
      (dyadicFinPilotMoments θ j x false - θ.regression x • dyadicFinPilotMoments θ j x true) -
      anchoredFinTransport d ℓ *ᵥ
        ((if j = 0 then 1 else dyadicFinPilotGram θ (j - 1) x)⁻¹ *ᵥ
          ((if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x) false -
            θ.regression x • (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x) true)) =
        anchoredFinVector (dyadicPopulationIncrement θ x j) := by
  rw [dyadicFinPilot_fit C θ hθ j x hx]
  cases j with
  | zero => simp [dyadicPopulationIncrement, anchoredIncrement]
  | succ j =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel_right]
    rw [dyadicFinPilot_fit C θ hθ j x hx, anchoredFinTransport, anchoredFinReindex_mulVec, ← anchoredFinVector_sub]
    rfl
theorem incrementFinVector_eval_population  [NeZero r] (a b A B T U V y m) :
    incrementFinVector r a b T y m
      (fun i => incrementValuation A B U V ((Fintype.equivFin (incrementVariables r)).symm i)) =
        fun i => eval (incrementValuation A B U V) (incrementEntryPolynomial r a b T y m i) := by
  ext i
  simp only [incrementFinVector, incrementFinPolynomial, eval_rename, Function.comp_def,
    Equiv.symm_apply_apply]
theorem anchoredNormalized_increment_error  [Nonempty (AnchoredIndex d ℓ)]
    (u v p q) (hpmeas : Measurable p) (hqmeas : Measurable q)
    (a b χ ε ) (ha : 0 < a) (hab : a < b)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)
    (hq : ∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b)
    (hχ : ‖(anchoredFinSimilarityUnit (ℓ := ℓ) u).val‖ *
      ‖((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ)
    (U V y T)
    (hδ : ‖(EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm
      ((anchoredFinNormalizedGram u p)⁻¹ *ᵥ (U false - y • U true) -
        T *ᵥ ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - y • V true)))‖ ≤ ε)
    (m ) :
    ‖(EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm
      ((fun i => eval (incrementValuation (anchoredFinNormalizedGram u p)
        (anchoredFinNormalizedGram v q) U V)
          (incrementEntryPolynomial (anchoredDimension d ℓ) a b T y m i)) -
        ((anchoredFinNormalizedGram u p)⁻¹ *ᵥ (U false - y • U true) -
          T *ᵥ ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - y • V true))))‖ ≤
      χ ^ 2 * b ^ (anchoredDimension d ℓ + 1) * parentInverseErrorConstant a b (anchoredDimension d ℓ) * ε *
        ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d ℓ * Real.exp (-m * exteriorTau ((a + b) / (b - a))) := by
  let Q := anchoredFinSimilarityUnit (ℓ := ℓ) u
  let R := anchoredFinSimilarityUnit (ℓ := ℓ) v
  let G := anchoredFinNormalizedGram (ℓ := ℓ) u p
  let H := anchoredFinNormalizedGram (ℓ := ℓ) v q
  have hG : matrixSimilarity Q (matrixSimilarity Q⁻¹ G) = G := by
    simp [matrixSimilarity, Matrix.mul_assoc]
  have hH : matrixSimilarity R (matrixSimilarity R⁻¹ H) = H := by
    simp [matrixSimilarity, Matrix.mul_assoc]
  have he := incrementEntryPolynomial_error a b ha hab
    (matrixSimilarity Q⁻¹ G) (matrixSimilarity R⁻¹ H) T
    (anchoredFin_similarity_isHermitian u p) (anchoredFin_similarity_isHermitian v q)
    (anchoredFin_similarity_spectrum u p hpmeas a b ha.le hp)
    (anchoredFin_similarity_spectrum v q hqmeas a b ha.le hq)
    Q R χ hχ U V y ε (by simpa only [hG, hH] using hδ) m
  simpa only [hG, hH] using he
def incrementFinRawVector (r ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (response : Bool) (m : ℕ) :
    (Fin (Fintype.card (incrementVariables r)) → ℝ) → Fin r → ℝ :=
  fun x i => MvPolynomial.eval x
    (MvPolynomial.rename (Fintype.equivFin (incrementVariables r))
      (rawIncrementEntryPolynomial r a b T response m i))
theorem incrementFinVector_affine (r a b T y m) :
    incrementFinVector r a b T y m = incrementFinRawVector r a b T false m -
      y • incrementFinRawVector r a b T true m := by
  funext x i
  have h_incrementEntryPolynomial_affine (i) : incrementEntryPolynomial r a b T y m i =
      rawIncrementEntryPolynomial r a b T false m i - C y *
        rawIncrementEntryPolynomial r a b T true m i := by
    unfold incrementEntryPolynomial numeratorPolynomial rawIncrementEntryPolynomial
    simp_rw [mul_sub, mul_left_comm _ _ _]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [incrementFinVector, incrementFinPolynomial, incrementFinRawVector,
    MvPolynomial.eval_rename, h_incrementEntryPolynomial_affine,
    map_sub, map_mul, MvPolynomial.eval_C, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
theorem paperTau_pos  (C : ModelConstants d) : 0 < paperTau C := by
  have : 0 < Real.sqrt C.densityLower := Real.sqrt_pos.mpr C.densityLower_pos
  apply Real.log_pos
  apply (one_lt_div (sub_pos.mpr (Real.sqrt_lt_sqrt C.densityLower_pos.le (C.densityLower_lt_one.trans C.one_lt_densityUpper)))).mpr
  linarith
theorem anchoredFinVector_dotProduct  (u v : AnchoredIndex d ℓ → ℝ) :
    anchoredFinVector u ⬝ᵥ anchoredFinVector v = u ⬝ᵥ v := by
  simp only [dotProduct, anchoredFinVector, anchoredFinIndex]
  exact (Fintype.equivFin (AnchoredIndex d ℓ)).symm.sum_comp
    (fun γ : AnchoredIndex d ℓ => u γ * v γ)
theorem dyadicPilotRow_dot_coefficients  (j : ℕ)
    (x y : Covariate d) (v : AnchoredIndex d ℓ → ℝ) :
    dyadicPilotRow j x y ⬝ᵥ anchoredFinVector v = dyadicAnchoredFeature j x y ⬝ᵥ v :=
  anchoredFinVector_dotProduct _ _
theorem finite_row_abs_dot_le_euclidean_norm  [Fintype ι]
    (row v ) :
    |row ⬝ᵥ v| ≤ (∑ i, |row i|) * ‖(EuclideanSpace.equiv ι ℝ).symm v‖ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ i, |row i * v i|) ≤ ∑ i, |row i| * ‖(EuclideanSpace.equiv ι ℝ).symm v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa [EuclideanSpace.equiv, Real.norm_eq_abs] using
        PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℝ).symm v) i
    _ = _ := by rw [Finset.sum_mul]
theorem dyadic_scale_rpow_cancel (j : ℕ) (s : ℝ) :
    (2 : ℝ) ^ j * (((2 : ℝ) ^ j)⁻¹) ^ s = (((2 : ℝ) ^ j)⁻¹) ^ (s - 1) := by
  simpa only [inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ j ≠ 0), one_mul, mul_comm] using (positive_rpow_times_distance (((2 : ℝ) ^ j)⁻¹) s ((2 : ℝ) ^ j) (by positivity))
def dyadicPopulationPolynomial  (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ) : Fin (anchoredDimension d C.order) → ℝ :=
  incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m (dyadicIncrementRawMean θ j x)
def dyadicPopulationBiasBudget  (C : ModelConstants d) (J : ℕ) (m : ℕ → ℕ) : ℝ :=
  ((2 ^ J)⁻¹) ^ (C.smoothness - 1) +
    ∑ j ∈ Finset.range (J + 1), ((2 ^ j)⁻¹) ^ (C.smoothness - 1) *
      ((m j + 1 ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-m j  * paperTau C)
def dyadicPopulationResidual  (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : ℕ → ℕ) (x y : Covariate d) : ℝ :=
  θ.regression y - θ.regression x - ∑ j ∈ Finset.range (J + 1),
    dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)
theorem dyadicIncrementRawMean_eq_with_virtual_parent  (C θ) (hθ : Admissible C θ) (j x) (hx : x ∈ unitCube d) :
    dyadicIncrementRawMean (ℓ := ℓ) θ j x = fun a =>
      incrementValuation
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x))
        (anchoredFinNormalizedGram (dyadicNormalizedAnchor (j - 1) x)
          (if j = 0 then (fun _ => 1) else dyadicNormalizedDensity θ (j - 1) x))
        (dyadicFinPilotMoments θ j x) (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)
        ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) := by
  rw [dyadicIncrementRawMean_eq_population C θ hθ j x hx]
  unfold dyadicIncrementPopulation
  rw [dyadicFinPilotGram_eq_normalized C θ hθ j x]
  by_cases hj : j = 0
  · simp [hj, anchoredFinNormalizedGram_one]
  · simp only [hj, ite_false]
    rw [dyadicFinPilotGram_eq_normalized C θ hθ (j - 1) x]
def dyadicPopulationRawPolynomial  (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (t : Bool) (m : ℕ) : Fin (anchoredDimension d C.order) → ℝ :=
  incrementFinRawVector (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) t m (dyadicIncrementRawMean θ j x)
theorem dyadicPopulationPolynomial_affine  (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ) :
    dyadicPopulationPolynomial C θ j x y m = dyadicPopulationRawPolynomial C θ j x false m -
      y • dyadicPopulationRawPolynomial C θ j x true m := congrFun (incrementFinVector_affine _ _ _ _ y m) (dyadicIncrementRawMean θ j x)
def dyadicPopulationPilotSum  (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : ℕ → ℕ) (t : Bool) (w : Covariate d × Covariate d) : ℝ :=
  ∑ j ∈ Finset.range (J + 1),
    dyadicPilotRow j w.1 w.2 ⬝ᵥ dyadicPopulationRawPolynomial C θ j w.1 t (m j)
def dyadicPopulationCoefficients  (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : ℕ → ℕ) (w : Covariate d × Covariate d) : PairVector :=
  WithLp.toLp 2 ![1, -1 + dyadicPopulationPilotSum C θ J m true w,
    -dyadicPopulationPilotSum C θ J m false w]
theorem dyadic_geometric_sum_le (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ (J + 1) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ, pow_succ _ (J + 1)]
    linarith
theorem dyadicPopulationCoefficients_measurable  (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (J : ℕ) (m : ℕ → ℕ) :
    Measurable (dyadicPopulationCoefficients C θ J m) := by
  have h_dyadicPopulationPilotSum_measurable (t : Bool) : Measurable (dyadicPopulationPilotSum C θ J m t) := by
    apply Finset.measurable_sum
    intro j _
    apply Finset.measurable_sum
    intro i _
    have h_dyadicPopulationRawPolynomial_measurable : Measurable (fun x => dyadicPopulationRawPolynomial C θ j x t (m j)) := by
      apply measurable_pi_iff.mpr
      intro i
      exact (MvPolynomial.continuous_eval (MvPolynomial.rename
        (Fintype.equivFin (incrementVariables (anchoredDimension d C.order)))
          (rawIncrementEntryPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) t (m j) i))).measurable.comp
          (dyadicIncrementRawMean_measurable C θ hθ j)
    exact (dyadicAnchoredFeature_joint_measurable j (anchoredFinIndex i)).mul
      ((h_dyadicPopulationRawPolynomial_measurable.eval (a := i)).comp measurable_fst)
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  fin_cases i
  · exact measurable_const
  · exact measurable_const.add (h_dyadicPopulationPilotSum_measurable true)
  · exact (h_dyadicPopulationPilotSum_measurable false).neg
theorem finite_row_abs_dot_le_pi_norm {ι : Type*} [Fintype ι] (row v : ι → ℝ) :
    |row ⬝ᵥ v| ≤ (∑ i, |row i|) * ‖v‖ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ i, |row i * v i|) ≤ ∑ i, |row i| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
        (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]
theorem dyadicPilotRow_total_abs_le  (J : ℕ) (x y : Covariate d)
    (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) (hc : y ∈ dyadicPilotCell J x) :
    (∑ j ∈ Finset.range (J + 1), ∑ i, |dyadicPilotRow (ℓ := ℓ) j x y i|) ≤
      2 * (anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1),
      (anchoredDimension d ℓ : ℝ) * (2 : ℝ) ^ j * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      exact dyadicPilotRow_sum_abs_le_fine_cell j J (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x y hx hy hc
    _ = (anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹ *
      ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹ * (2 : ℝ) ^ (J + 1) :=
      mul_le_mul_of_nonneg_left (dyadic_geometric_sum_le J) (by positivity)
    _ = _ := by rw [pow_succ]; field_simp
def polynomialGaussianConstant (r : ℕ) (a : ℝ) : ℝ :=
  r.factorial / (a / 2) ^ r * Real.exp (a / 2)
theorem polynomial_gaussian_absorption (r ) {a S u : ℝ}
    (ha : 0 < a) (hS : 0 < S) :
    (1 + u ^ 2 / S) ^ r * Real.exp (-a * u ^ 2 / S) ≤
      polynomialGaussianConstant r a * Real.exp (-(a / 2) * u ^ 2 / S) := by
  have h_polynomial_exp_absorption {t : ℝ} (ht : 0 ≤ t) : (1 + t) ^ r * Real.exp (-a * t) ≤
      polynomialGaussianConstant r a * Real.exp (-(a / 2) * t) := by
    have hδ : 0 < a / 2 := by positivity
    have hf : 0 < (r.factorial : ℝ) := by positivity
    have hh := Real.pow_div_factorial_le_exp (a / 2 * (1 + t))
      (by positivity : 0 ≤ a / 2 * (1 + t)) r
    have hp : (1 + t) ^ r ≤
        (r.factorial : ℝ) / (a / 2) ^ r * Real.exp (a / 2 * (1 + t)) := by
      have hb := (div_le_iff₀ hf).1 hh
      rw [mul_pow] at hb
      calc
        (1 + t) ^ r ≤ Real.exp (a / 2 * (1 + t)) * r.factorial / (a / 2) ^ r := by
          apply (le_div_iff₀ (pow_pos hδ r)).2
          simpa [mul_comm] using hb
        _ = r.factorial / (a / 2) ^ r * Real.exp (a / 2 * (1 + t)) := by ring
    have hs := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-a * t)).le
    apply hs.trans_eq
    unfold polynomialGaussianConstant
    have he : Real.exp (a / 2 * (1 + t)) * Real.exp (-a * t) =
        Real.exp (a / 2) * Real.exp (-(a / 2) * t) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      (r.factorial / (a / 2) ^ r * Real.exp (a / 2 * (1 + t))) * Real.exp (-a * t) =
          r.factorial / (a / 2) ^ r *
            (Real.exp (a / 2 * (1 + t)) * Real.exp (-a * t)) := by ring
      _ = _ := by rw [he]; ring
  have h := h_polynomial_exp_absorption (div_nonneg (sq_nonneg u) hS.le)
  have h₁ : -a * (u ^ 2 / S) = -a * u ^ 2 / S := by ring
  have h₂ : -(a / 2) * (u ^ 2 / S) = -(a / 2) * u ^ 2 / S := by ring
  rwa [h₁, h₂] at h
theorem profile_approximation_degree_bounds  (q )
    (hβQ : 0 ≤ β * Q) (hq : q ≤ Nat.floor (β * Q)) :
    β * Q - q - 1 ≤ ((Nat.floor (β * Q) - q : ℕ) : ℝ) ∧
      ((Nat.floor (β * Q) - q : ℕ) : ℝ) + 1 ≤ β * Q + 1 := by
  have := Nat.floor_le hβQ
  have := Nat.lt_floor_add_one (β * Q)
  rw [Nat.cast_sub hq]
  constructor <;> linarith [(Nat.cast_nonneg q : 0 ≤ q)]
def allocationBiasTermConstant (r q : ℕ) (β θ τ : ℝ) : ℝ :=
  (1 + 3 * β / 2) ^ r * Real.exp (τ * (q + 1)) * polynomialGaussianConstant r θ
theorem allocationBiasTermConstant_pos (r q ) 
    (hβ : 0 ≤ β) (hθ : 0 < θ) : 0 < allocationBiasTermConstant r q β θ τ := by
  have h_polynomialGaussianConstant_pos {a} (ha : 0 < a) : 0 < polynomialGaussianConstant r a := by
    unfold polynomialGaussianConstant
    positivity
  exact mul_pos (mul_pos (by positivity) (Real.exp_pos _))
    (h_polynomialGaussianConstant_pos hθ)
def allocationBiasSumConstant (r q : ℕ) (β θ τ b : ℝ) : ℝ :=
  allocationBiasTermConstant r q β θ τ * (2 + Real.sqrt (Real.pi / (θ / 2)) / b)
theorem profile_coordinate_order_admissible (q : ℕ) {β S z : ℝ}
    (hβ : 0 ≤ β) (hS : 0 < S) (hthreshold : (q : ℝ) ≤ β * S / 4) :
    q ≤ Nat.floor (β * quadraticProfile S z) := by
  apply Nat.le_floor
  have := mul_le_mul_of_nonneg_left (quadraticProfile_lower (z := z) hS) hβ
  linarith
theorem raw_allocation_bias_sum_bound (A : Finset ℕ) (r q : ℕ)
    (u₀ b β θ τ S ell T Kstar : ℝ) (K : ℕ → ℝ) (m : ℕ → ℕ)
    (hb : 0 < b) (hβ : 0 ≤ β) (hθ : 0 < θ) (hτ : 0 < τ) (hS : 1 ≤ S)
    (hθβ : τ * β = θ) (hKstar : 0 < Kstar)
    (hK : ∀ j ∈ A, 0 < K j)
    (hlog : ∀ j ∈ A, Real.log (K j) - Real.log Kstar =
      u₀ + (j : ℝ) * b + S / 2 - ell - T)
    (hreserve : ((r : ℝ) + 1 / 2) * Real.log S ≤ θ * (S - ell - T))
    (hml : ∀ j ∈ A, β * quadraticProfile S (u₀ + (j : ℝ) * b + S / 2) - (q : ℝ) - 1 ≤ (m j : ℝ))
    (hmu : ∀ j ∈ A, (m j : ℝ) + 1 ≤ β * quadraticProfile S (u₀ + (j : ℝ) * b + S / 2) + 1) :
    (∑ j ∈ A, (K j) ^ (-θ) * ((m j : ℝ) + 1) ^ r * (Real.exp (-τ)) ^ (m j)) ≤
      allocationBiasSumConstant r q β θ τ b * Kstar ^ (-θ) := by
  have he (j : ℕ) (hj : j ∈ A) : (K j) ^ (-θ) * (Real.exp (-τ)) ^ (m j) =
      Kstar ^ (-θ) * Real.exp (-θ * (u₀ + (j : ℝ) * b + S / 2 - ell - T) - τ * (m j : ℝ)) := by
    rw [Real.rpow_def_of_pos (hK j hj), Real.rpow_def_of_pos hKstar,
      ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    have hlogeq : Real.log (K j) = Real.log Kstar +
        (u₀ + (j : ℝ) * b + S / 2 - ell - T) := by linarith [hlog j hj]
    rw [hlogeq]
    ring
  have h_finite_allocation_bias_sum_bound : (∑ j ∈ A, Real.exp (-θ * (u₀ + (j : ℝ) * b + S / 2 - ell - T) - τ * (m j : ℝ)) *
      ((m j : ℝ) + 1) ^ r) ≤
        allocationBiasTermConstant r q β θ τ * (2 + Real.sqrt (Real.pi / (θ / 2)) / b) := by
    have h_allocation_bias_term_bound {z : ℝ} {m : ℝ} (hmpos : 0 ≤ m + 1) (hml : β * quadraticProfile S z - (q : ℝ) - 1 ≤ m) (hmu : m + 1 ≤ β * quadraticProfile S z + 1) : Real.exp (-θ * (z - ell - T) - τ * m) * (m + 1) ^ r ≤
        allocationBiasTermConstant r q β θ τ / Real.sqrt S *
          Real.exp (-(θ / 2) * (z - S / 2) ^ 2 / S) := by
      have hS₀  := lt_of_lt_of_le zero_lt_one hS
      have h_allocation_bias_mass_bound : Real.exp (-θ * (z - ell - T) - τ * m) ≤
          Real.exp (τ * (q + 1)) *
            Real.exp (-(r + 1 / 2) * Real.log S) *
              Real.exp (-θ * (z - S / 2) ^ 2 / S) := by
        have hml := mul_le_mul_of_nonneg_left hml hτ.le
        have hrewrite : τ * (β * quadraticProfile S z - q - 1) =
            θ * quadraticProfile S z - τ * (q + 1) := by
          rw [← hθβ]
          ring
        rw [hrewrite] at hml
        have hid : θ * (z + quadraticProfile S z - S) = θ * (z - S / 2) ^ 2 / S := by
          have h_quadraticProfile_bias_identity : z + quadraticProfile S z - S = (z - S / 2) ^ 2 / S := by
            dsimp [quadraticProfile]
            field_simp
            ring
          rw [h_quadraticProfile_bias_identity]
          ring
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.2
        ring_nf at hml hreserve hid ⊢
        linarith
      have hm := h_allocation_bias_mass_bound
      have h_profile_polynomial_prefactor_bound : (m + 1) ^ r ≤ (1 + 3 * β / 2) ^ r * S ^ r *
          (1 + (z - S / 2) ^ 2 / S) ^ r := by
        have hS₀  := lt_of_lt_of_le zero_lt_one hS
        have h_quadraticProfile_gaussian_upper : quadraticProfile S z ≤ S + 3 * (z - S / 2) ^ 2 / (2 * S) := by
          have : S + 3 * (z - S / 2) ^ 2 / (2 * S) - quadraticProfile S z =
              (z + S / 2) ^ 2 / (2 * S) := by
            dsimp [quadraticProfile]
            field_simp
            ring
          have : 0 ≤ (z + S / 2) ^ 2 / (2 * S) := by positivity
          linarith
        have hQ := h_quadraticProfile_gaussian_upper
        have ht : 0 ≤ (z - S / 2) ^ 2 / S := div_nonneg (sq_nonneg _) hS₀.le
        have hupper : m + 1 ≤ (1 + 3 * β / 2) * S *
            (1 + (z - S / 2) ^ 2 / S) := by
          rw [show 3 * (z - S / 2) ^ 2 / (2 * S) =
            3 / 2 * ((z - S / 2) ^ 2 / S) by ring] at hQ
          have hb := mul_le_mul_of_nonneg_left hQ hβ
          have := mul_nonneg hβ (mul_nonneg (sub_nonneg.mpr hS) ht)
          nlinarith [mul_nonneg hS₀.le ht, mul_nonneg hβ hS₀.le]
        have hp := pow_le_pow_left₀ hmpos hupper r
        simpa only [mul_pow, mul_assoc] using hp
      have hp := h_profile_polynomial_prefactor_bound
      have ha := polynomial_gaussian_absorption r hθ (u := z - S / 2) hS₀
      have hc : 0 ≤ (1 + 3 * β / 2) ^ r * Real.exp (τ * (↑q + 1)) := by positivity
      have hb : 0 ≤ S ^ r * Real.exp (-(r + 1 / 2) * Real.log S) := by positivity
      calc
        _ ≤ (Real.exp (τ * (q + 1)) *
            Real.exp (-(r + 1 / 2) * Real.log S) *
              Real.exp (-θ * (z - S / 2) ^ 2 / S)) *
                ((1 + 3 * β / 2) ^ r * S ^ r * (1 + (z - S / 2) ^ 2 / S) ^ r) :=
          mul_le_mul hm hp (pow_nonneg hmpos r) (by positivity)
        _ = (1 + 3 * β / 2) ^ r * Real.exp (τ * (↑q + 1)) *
            (S ^ r * Real.exp (-(r + 1 / 2) * Real.log S)) *
              ((1 + (z - S / 2) ^ 2 / S) ^ r * Real.exp (-θ * (z - S / 2) ^ 2 / S)) := by ring
        _ ≤ ((1 + 3 * β / 2) ^ r * Real.exp (τ * (q + 1))) *
            (S ^ r * Real.exp (-(↑r + 1 / 2) * Real.log S)) *
              (polynomialGaussianConstant r θ * Real.exp (-(θ / 2) * (z - S / 2) ^ 2 / S)) :=
          mul_le_mul_of_nonneg_left ha (mul_nonneg hc hb)
        _ = _ := by
          have h_pow_mul_log_factor_eq_inv_sqrt : S ^ r * Real.exp (-(↑r + 1 / 2) * Real.log S) = 1 / Real.sqrt S := by
            have hsqrt  := Real.sqrt_pos.2 hS₀
            rw [← Real.exp_log (pow_pos hS₀ r), Real.log_pow, ← Real.exp_add]
            simp only [one_div]
            rw [← Real.exp_log hsqrt, ← Real.exp_neg]
            congr 1
            rw [Real.log_sqrt hS₀.le]
            ring
          rw [h_pow_mul_log_factor_eq_inv_sqrt]
          unfold allocationBiasTermConstant
          ring
    have hterm j (hj : j ∈ A) := h_allocation_bias_term_bound (by positivity : 0 ≤ (m j : ℝ) + 1) (hml j hj) (hmu j hj)
    have hsum : (∑ j ∈ A, Real.exp (-θ * (u₀ + ↑j * b + S / 2 - ell - T) - τ * (m j : ℝ)) *
        ((m j : ℝ) + 1) ^ r) ≤
          ∑ j ∈ A, allocationBiasTermConstant r q β θ τ / Real.sqrt S *
            Real.exp (-(θ / 2) * (u₀ + ↑j * b) ^ 2 / S) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [add_sub_cancel_right] using hterm j hj
    apply hsum.trans
    rw [← Finset.mul_sum]
    have hgauss := GaussianSum.normalized_gaussian_lattice_sum_le A u₀ (θ / 2) b S
      (by positivity) hb hS
    have hc := (allocationBiasTermConstant_pos r q hβ hθ (τ := τ)).le
    have hh := mul_le_mul_of_nonneg_left hgauss hc
    simpa only [div_mul_eq_mul_div, mul_div_assoc] using hh
  calc
    _ = ∑ j ∈ A, Kstar ^ (-θ) *
        (Real.exp (-θ * (u₀ + ↑j * b + S / 2 - ell - T) - τ * (m j : ℝ)) * ((m j : ℝ) + 1) ^ r) := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _ = (K j) ^ (-θ) * (Real.exp (-τ)) ^ (m j) * ((m j : ℝ) + 1) ^ r := by ring
        _ = _ := by rw [he j hj]; ring
    _ = Kstar ^ (-θ) * ∑ j ∈ A,
        Real.exp (-θ * (u₀ + ↑j * b + S / 2 - ell - T) - τ * (m j : ℝ)) * ((m j : ℝ) + 1) ^ r := by
      rw [Finset.mul_sum]
    _ ≤ Kstar ^ (-θ) *
        (allocationBiasTermConstant r q β θ τ * (2 + Real.sqrt (Real.pi / (θ / 2)) / b)) :=
      mul_le_mul_of_nonneg_left (h_finite_allocation_bias_sum_bound) (Real.rpow_pos_of_pos hKstar _).le
    _ = _ := by unfold allocationBiasSumConstant; ring
def allocatedApproximationDegree (β S z : ℝ) (q : ℕ) : ℕ :=
  Nat.floor (β * quadraticProfile S z) - q
def actualApproximationDegree (δ a C H β x : ℝ) (j q : ℕ) : ℕ :=
  allocatedApproximationDegree β (allocationWidth a C x) (allocationLevelPosition δ a C H x j) q
theorem eventually_actual_allocation_bias_sum (r q : ℕ) (δ a C H γ β θ τ : ℝ)
    (hδ : 0 < δ) (ha : 0 < a) (hH : 0 < H) (hβ : 0 < β) (hθ : 0 < θ) (hτ : 0 < τ)
    (hθβ : τ * β = θ) (hθγ : θ * γ = (r : ℝ) + 1 / 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℝ in atTop,
      (∑ j ∈ Finset.range (terminalAllocationLevel δ a C H γ x + 1),
        (Real.exp (δ * ↑j)) ^ (-θ) * ((actualApproximationDegree δ a C H β x j q : ℝ) + 1) ^ r *
          (Real.exp (-τ)) ^ (actualApproximationDegree δ a C H β x j q)) ≤
        B * (Real.exp (δ * (terminalAllocationLevel δ a C H γ x : ℝ))) ^ (-θ) := by
  have h_allocationBiasSumConstant_pos {b : ℝ} {β : ℝ} (hβ : 0 ≤ β) (hb : 0 < b) : 0 < allocationBiasSumConstant r q β θ τ b := mul_pos (allocationBiasTermConstant_pos r q hβ hθ) (by positivity)
  refine ⟨allocationBiasSumConstant r q β θ τ δ,
    (h_allocationBiasSumConstant_pos hβ.le hδ), ?_⟩
  filter_upwards [(allocationWidth_tendsto_atTop ha C).eventually (eventually_ge_atTop ↑1),
    eventually_terminal_cell_log_nonneg ha hH C γ,
    eventually_width_degree_threshold ha hβ C q] with x hS hLT hdegree
  let J := terminalAllocationLevel δ a C H γ x
  let S := allocationWidth a C x
  let ell := Real.log (H * S)
  let T := δ * ↑J - Real.log x
  let u₀ := -Real.log x + ell - S / 2
  let Kstar := Real.exp (δ * ↑J)
  have hu := (roundedTerminalDepth_bounds hδ hLT).2
  change T ≤ S - ell - γ * Real.log S at hu
  have := mul_le_mul_of_nonneg_left hu hθ.le
  have : θ * γ * Real.log S = (↑r + 1 / 2) * Real.log S := by rw [hθγ]
  have hz (j : ℕ) : u₀ + (j : ℝ) * δ + S / 2 = allocationLevelPosition δ a C H x j := by
    unfold allocationLevelPosition
    dsimp [u₀, ell, S]
    ring
  have h_floored_raw_allocation_bias_sum_bound (A : Finset ℕ) (K : ℕ → ℝ) (hKstar : 0 < Kstar) (hK : ∀ j ∈ A, 0 < K j) (hlog : ∀ j ∈ A, Real.log (K j) - Real.log Kstar = u₀ + (j : ℝ) * δ + S / 2 - ell - T) (hq : ∀ j ∈ A, q ≤ Nat.floor (β * quadraticProfile S (u₀ + (j : ℝ) * δ + S / 2))) : (∑ j ∈ A, (K j) ^ (-θ) *
      ((allocatedApproximationDegree β S (u₀ + (j : ℝ) * δ + S / 2) q : ℝ) + 1) ^ r *
        (Real.exp (-τ)) ^ (allocatedApproximationDegree β S (u₀ + (j : ℝ) * δ + S / 2) q)) ≤
      allocationBiasSumConstant r q β θ τ δ * Kstar ^ (-θ) := by
    have hbounds j (hj : j ∈ A) := profile_approximation_degree_bounds q
      (mul_nonneg hβ.le ((by positivity : (0 : ℝ) ≤ S / 4).trans (quadraticProfile_lower (lt_of_lt_of_le zero_lt_one hS)))) (hq j hj)
    exact raw_allocation_bias_sum_bound A r q u₀ δ β θ τ S ell T Kstar K
      (fun j => allocatedApproximationDegree β S (u₀ + (j : ℝ) * δ + S / 2) q)
      hδ hβ.le hθ hτ hS hθβ hKstar hK hlog (by nlinarith)
      (fun j hj => (hbounds j hj).1) (fun j hj => (hbounds j hj).2)
  have hbound := (h_floored_raw_allocation_bias_sum_bound (Finset.range (J + 1)) (fun j : ℕ => Real.exp (δ * (j : ℝ))) (Real.exp_pos _) (fun j hj => Real.exp_pos _) (by
      intro j hj
      rw [Real.log_exp, Real.log_exp]
      ring) (by
      intro j hj
      exact profile_coordinate_order_admissible q hβ.le (by linarith : 0 < S) (by change ↑q + 2 ≤ β * S / 4 at hdegree; linarith)))
  simp_rw [hz] at hbound
  simpa [actualApproximationDegree, J, Kstar] using hbound
def paperDyadicStep  (_C : ModelConstants d) : ℝ := d * Real.log 2
def paperSpatialExponent  (C : ModelConstants d) : ℝ := (C.smoothness - 1) / d
def paperDegreeSlope  (C : ModelConstants d) : ℝ := paperSpatialExponent C / paperTau C
def paperDegreeReserve  (C : ModelConstants d) : ℝ :=
  ((anchoredDimension d C.order ) + 1 / 2) / paperSpatialExponent C
def paperDyadicTerminalLevel  (C : ModelConstants d) (a offset H n : ℝ) : ℕ :=
  terminalAllocationLevel (paperDyadicStep C) a offset H (paperDegreeReserve C) n
def paperDyadicApproximationDegree  (C : ModelConstants d) (a offset H n : ℝ) (j : ℕ) : ℕ :=
  actualApproximationDegree (paperDyadicStep C) a offset H (paperDegreeSlope C) n j (paperPolynomialDimension C)
theorem paperDyadicStep_pos  (C : ModelConstants d) : 0 < paperDyadicStep C :=
  mul_pos (Nat.cast_pos.mpr C.dimension_pos) (Real.log_pos (by norm_num))
theorem paperSpatialExponent_pos  (C : ModelConstants d) (hs : 1 < C.smoothness) :
    0 < paperSpatialExponent C := div_pos (sub_pos.mpr hs) (Nat.cast_pos.mpr C.dimension_pos)
theorem dyadicPilotScale_eq_exp  (C : ModelConstants d) (j : ℕ) :
    dyadicPilotScale d j = Real.exp (paperDyadicStep C * ↑j) := by
  have hl : Real.log (dyadicPilotScale d j) = paperDyadicStep C * ↑j := by
    unfold dyadicPilotScale paperDyadicStep
    rw [Real.log_pow, Real.log_pow]
    ring
  rw [← hl, Real.exp_log (dyadicPilotScale_pos d j)]
theorem exp_negative_nat_eq_pow (τ ) (m : ℕ) :
    Real.exp (-↑m * τ) = (Real.exp (-τ)) ^ m := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring
end NearlyMinimax
end
open MeasureTheory Filter Set Matrix
open scoped ENNReal BigOperators Topology RealInnerProductSpace Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
section
variable {d n m : ℕ}
def sampleBlockIndexEquiv (a b c ) :
    ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin (a + b + c) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin c))).trans finSumFinEquiv
def sampleBlockSplitEquiv (d a b c ) :
    (Fin (a + b + c) → Observation d) ≃ᵐ
      (((Fin a → Observation d) × (Fin b → Observation d)) × (Fin c → Observation d)) :=
  (MeasurableEquiv.piCongrLeft
    (fun _ => Observation d)
    (sampleBlockIndexEquiv a b c).symm).trans
  ((MeasurableEquiv.sumPiEquivProdPi
    (fun _ => Observation d)).trans
  (MeasurableEquiv.prodCongr
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => Observation d))
    (MeasurableEquiv.refl (Fin c → Observation d))))
theorem sampleBlockSplit_measurePreserving  (C θ) (hθ : Admissible C θ) (a b c ) :
    MeasurePreserving (sampleBlockSplitEquiv d a b c) (sampleLaw θ (a + b + c))
      (((sampleLaw θ a).prod (sampleLaw θ b)).prod (sampleLaw θ c)) := by
  let := observationLaw_isProbability C θ hθ
  let := sampleLaw_isProbability C θ hθ c
  have h1 := measurePreserving_piCongrLeft
    (fun _ : (Fin a ⊕ Fin b) ⊕ Fin c => observationLaw θ) (sampleBlockIndexEquiv a b c).symm
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : (Fin a ⊕ Fin b) ⊕ Fin c => observationLaw θ)
  have h3 := (measurePreserving_sumPiEquivProdPi
    (fun _ : Fin a ⊕ Fin b => observationLaw θ)).prod (MeasurePreserving.id (sampleLaw θ c))
  exact h3.comp (h2.comp h1)
def initialSampleSplitEquiv (d m r ) :
    (Fin (m + r) → Observation d) ≃ᵐ ((Fin m → Observation d) × (Fin r → Observation d)) :=
  (MeasurableEquiv.piCongrLeft (fun _ => Observation d)
    (finSumFinEquiv : (Fin m ⊕ Fin r) ≃ Fin (m + r)).symm).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ => Observation d))
def initialSampleBlock (d m r ) (z : Fin (m + r) → Observation d) : Fin m → Observation d :=
  (initialSampleSplitEquiv d m r z).1
def sampleBlocksWithRemainder (d a b c r )
    (z : Fin (a + b + c + r) → Observation d) :
      ((Fin a → Observation d) × (Fin b → Observation d)) × (Fin c → Observation d) :=
  sampleBlockSplitEquiv d a b c (initialSampleBlock d (a + b + c) r z)
theorem sampleBlocksWithRemainder_measurePreserving  (C θ) (hθ : Admissible C θ) (a b c r ) :
    MeasurePreserving (sampleBlocksWithRemainder d a b c r) (sampleLaw θ (a + b + c + r))
      (((sampleLaw θ a).prod (sampleLaw θ b)).prod (sampleLaw θ c)) :=
  have h_initialSampleBlock_measurePreserving (m) : MeasurePreserving (initialSampleBlock d m r) (sampleLaw θ (m + r)) (sampleLaw θ m) := by
    let := observationLaw_isProbability C θ hθ
    let := sampleLaw_isProbability C θ hθ m
    let := sampleLaw_isProbability C θ hθ r
    have h1 := measurePreserving_piCongrLeft
      (fun _ => observationLaw θ)
      (finSumFinEquiv : (Fin m ⊕ Fin r) ≃ Fin (m + r)).symm
    have h2 := measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin r => observationLaw θ)
    have hf : MeasurePreserving
        (Prod.fst : ((Fin m → Observation d) × (Fin r → Observation d)) → (Fin m → Observation d))
        ((sampleLaw θ m).prod (sampleLaw θ r)) (sampleLaw θ m) := measurePreserving_fst
    exact hf.comp (h2.comp h1)
  (sampleBlockSplit_measurePreserving C θ hθ a b c).comp
    (h_initialSampleBlock_measurePreserving (a + b + c))
def blockEstimatorWithRemainder {d a b c r : ℕ}
    (T : (((Fin a → Observation d) × (Fin b → Observation d)) × (Fin c → Observation d)) → ℝ)
    (hmT : Measurable T) : Estimator d (a + b + c + r) :=
  ⟨fun z => T (sampleBlocksWithRemainder d a b c r z),
    hmT.comp ((sampleBlockSplitEquiv d a b c).measurable.comp
      (measurable_fst.comp (initialSampleSplitEquiv d (a + b + c) r).measurable))⟩
theorem blockEstimatorWithRemainder_risk_eq  (C )
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (T : (((Fin a → Observation d) × (Fin b → Observation d)) × (Fin c → Observation d)) → ℝ)
    (hmT : Measurable T) :
    meanSquaredRisk (blockEstimatorWithRemainder (r := r) T hmT) θ =
      ∫⁻ z, ENNReal.ofReal ((T z - θ.variance) ^ 2)
        ∂((sampleLaw θ a).prod (sampleLaw θ b)).prod (sampleLaw θ c) := by
  exact (sampleBlocksWithRemainder_measurePreserving C θ hθ a b c r).lintegral_comp
    (((hmT.sub measurable_const).pow_const 2).ennreal_ofReal)
def threeBlockSize (n : ℕ) : ℕ := n / 3
def threeBlockRemainder (n : ℕ) : ℕ := n - (threeBlockSize n + threeBlockSize n + threeBlockSize n)
theorem threeBlockSize_two_le  (hn : 6 ≤ n) : 2 ≤ threeBlockSize n := by
  unfold threeBlockSize
  omega
theorem threeBlockSize_fraction  (hn : 6 ≤ n) :
    (1 / 4 : ℝ) * n ≤ threeBlockSize n := by
  have : ↑n ≤ 4 * (threeBlockSize n : ℝ) := by exact_mod_cast (by unfold threeBlockSize; omega)
  linarith
def castEstimator  (h : n = m) (T : Estimator d m) : Estimator d n := h.symm ▸ T
theorem castEstimator_risk_eq  (h : n = m) (T : Estimator d m)
    (θ : RegressionParameter d) : meanSquaredRisk (castEstimator h T) θ = meanSquaredRisk T θ := by
  subst m
  rfl
def threeBlockEstimator 
    (T : (((Fin (threeBlockSize n) → Observation d) × (Fin (threeBlockSize n) → Observation d)) ×
      (Fin (threeBlockSize n) → Observation d)) → ℝ) (hmT : Measurable T) : Estimator d n :=
  castEstimator (by simp only [threeBlockSize, threeBlockRemainder]; omega)
    (blockEstimatorWithRemainder (r := threeBlockRemainder n) T hmT)
end
def dyadicPilotSeries  (C : ModelConstants d) (A Λ : ℝ) (j m : ℕ) : ℝ :=
  ∑ k : Fin (m + anchoredDimension d C.order + 1),
    ((k.val + 1).factorial : ℝ) *
      (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
        preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ (k.val + 1)
theorem dyadicPilotSeries_nonneg  (C : ModelConstants d) (A Λ )
    (hΛ : 0 ≤ Λ) (j m ) : 0 ≤ dyadicPilotSeries C A Λ j m := by
  unfold dyadicPilotSeries
  have := preconditionedPilotMomentConstant_pos C C.order
  have := dyadicPilotScale_pos d j
  positivity
def dyadicSeriesEnvelope  (C : ModelConstants d) (A Λ : ℝ)
    (J : ℕ) (m : ℕ → ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j : Fin (J + 1) =>
    dyadicPilotSeries C A Λ j.val (m j.val) * max 1 (Λ / dyadicPilotScale d j.val))
theorem dyadicSeriesEnvelope_level_le {d : ℕ} (C : ModelConstants d) (A Λ : ℝ)
    (J : ℕ) (m : ℕ → ℕ) (j : Fin (J + 1)) :
    dyadicPilotSeries C A Λ j.val (m j.val) * max 1 (Λ / dyadicPilotScale d j.val) ≤
      dyadicSeriesEnvelope C A Λ J m :=
  Finset.le_sup' (fun j : Fin (J + 1) =>
    dyadicPilotSeries C A Λ j.val (m j.val) * max 1 (Λ / dyadicPilotScale d j.val)) (Finset.mem_univ j)
theorem dyadicSeriesEnvelope_nonneg {d : ℕ} (C : ModelConstants d) (A Λ : ℝ)
    (hΛ : 0 ≤ Λ) (J : ℕ) (m : ℕ → ℕ) : 0 ≤ dyadicSeriesEnvelope C A Λ J m := by
  apply le_trans _ (dyadicSeriesEnvelope_level_le C A Λ J m ⟨0, by omega⟩)
  exact mul_nonneg (dyadicPilotSeries_nonneg C A Λ hΛ _ _) (zero_le_one.trans (le_max_left _ _))
theorem dyadicPilotScale_parent_ratio_le  :
    dyadicPilotScale d j ≤ 2 ^ d * dyadicPilotScale d (j - 1) := by
  cases j with
  | zero => simpa [dyadicPilotScale] using one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  | succ j => simp only [Nat.add_sub_cancel, dyadicPilotScale, pow_succ, mul_pow]; exact le_of_eq (by ring)
variable {D d : ℕ} {x z β C₀ C_D S η varpi δ a γ : ℝ}
def factorialSeries (D : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range D, ((k + 1).factorial : ℝ) * x ^ (k + 1)
theorem factorialSeries_nonneg (D : ℕ)  (hx : 0 ≤ x) :
    0 ≤ factorialSeries D x := Finset.sum_nonneg fun k hk => by positivity
theorem factorialSeries_coarse_bound  
    (hx : 0 ≤ x) (hD : (D : ℝ) * x ≤ 1 / 2) :
    factorialSeries D x ≤ 2 * x := by
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := D)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  calc
    _ ≤ ∑ k ∈ Finset.range D, x * (1 / 2 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have h_factorial_term_le_geometric {k : ℕ} (hk : k < D) : ((k + 1).factorial : ℝ) * x ^ (k + 1) ≤ x * (1 / 2 : ℝ) ^ k := by
        induction k with
        | zero => simp
        | succ k ih =>
          have hcast : ((k + 2 : ℕ) : ℝ) ≤ ↑D := by exact_mod_cast (by omega : k + 2 ≤ D)
          have hratio := (mul_le_mul_of_nonneg_right hcast hx).trans hD
          have hprev := ih (by omega)
          calc
            (((k + 1 + 1).factorial : ℕ) : ℝ) * x ^ (k + 1 + 1) =
                ((k + 2 : ℕ) : ℝ) * x * (((k + 1).factorial : ℝ) * x ^ (k + 1)) := by
              rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
              push_cast
              ring
            _ ≤ (1 / 2 : ℝ) * (x * (1 / 2 : ℝ) ^ k) :=
              mul_le_mul hratio hprev (by positivity) (by norm_num)
            _ = x * (1 / 2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      exact h_factorial_term_le_geometric (Finset.mem_range.1 hk)
    _ = x * ∑ k ∈ Finset.range D, (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
    _ ≤ x * 2 := mul_le_mul_of_nonneg_left (by convert h using 1 <;> norm_num) hx
    _ = 2 * x := mul_comm _ _
theorem factorial_cast_le_degree_pow {D k : ℕ} (hk : k ≤ D) :
    ↑k.factorial ≤ (D : ℝ) ^ k := by
  exact_mod_cast ((Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left hk k))
theorem factorialSeries_fine_bound  {x z B A : ℝ}
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hDx : (D : ℝ) * x ≤ Real.exp z)
    (hDz : (D : ℝ) * z ≤ B) (hDA : (D : ℝ) ≤ A) :
    factorialSeries D x ≤ A * Real.exp B := by
  calc
    _ ≤ ∑ k ∈ Finset.range D, Real.exp B := by
      apply Finset.sum_le_sum
      intro k hk
      have hkD  := Finset.mem_range.1 hk
      calc
        ((k + 1).factorial : ℝ) * x ^ (k + 1) ≤
            (D : ℝ) ^ (k + 1) * x ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (factorial_cast_le_degree_pow hkD) (by positivity)
        _ = ((D : ℝ) * x) ^ (k + 1) := by rw [mul_pow]
        _ ≤ (Real.exp z) ^ (k + 1) := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg D) hx) hDx (k + 1)
        _ = Real.exp (((k + 1 : ℕ) : ℝ) * z) := (Real.exp_nat_mul z (k + 1)).symm
        _ ≤ Real.exp B := Real.exp_le_exp.2
          ((mul_le_mul_of_nonneg_right (by exact_mod_cast hkD) hz).trans hDz)
    _ = (D : ℝ) * Real.exp B := by simp
    _ ≤ A * Real.exp B := mul_le_mul_of_nonneg_right hDA (Real.exp_pos B).le
theorem factorialSeries_fine_weighted  {z β C₀ C_D S M : ℝ}
    (hz : 0 ≤ z) (_hC : 0 ≤ C₀) (hCS : 0 < C_D * S)
    (hD : (D : ℝ) ≤ C_D * S) (hDz : (D : ℝ) * z ≤ β * S ^ 2 / 4)
    (hM : 0 ≤ M) (hMb : M ≤ C₀ * C_D * S) :
    factorialSeries D (Real.exp z / (C_D * S)) * M ≤
      C₀ * C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by
  have h_factorialSeries_fine_allocation : factorialSeries D (Real.exp z / (C_D * S)) ≤
      C_D * S * Real.exp (β * S ^ 2 / 4) := by
    apply factorialSeries_fine_bound (div_nonneg (Real.exp_pos z).le hCS.le) hz _ hDz hD
    have hd := mul_le_mul_of_nonneg_right hD (div_nonneg (Real.exp_pos z).le hCS.le)
    have he : (C_D * S) * (Real.exp z / (C_D * S)) = Real.exp z := by
      rw [← mul_div_assoc, mul_comm (C_D * S), mul_div_cancel_right₀ _ hCS.ne']
    rwa [he] at hd
  apply (mul_le_mul (h_factorialSeries_fine_allocation) hMb hM (mul_nonneg hCS.le (Real.exp_pos _).le)).trans_eq
  ring
theorem quadratic_allocation_budget {β H t S : ℝ}
    (hβ : 0 < β) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (hdef : S = t - (1 + 2 * H / β)) :
    β * S ^ 2 / 4 + H * S ≤ β * t ^ 2 / 4 := by
  have ht : t = S + (1 + 2 * H / β) := by linarith
  have : β * t ^ 2 / 4 - (β * S ^ 2 / 4 + H * S) =
      β * (1 + 2 * H / β) ^ 2 / 4 + β * S / 2 := by
    rw [ht]
    field_simp
    ring
  have : 0 ≤ β * (1 + 2 * H / β) ^ 2 / 4 + β * S / 2 := by positivity
  linarith
theorem allocation_budget_reserve {β S η varpi L T : ℝ}
    (hbudget : β * S ^ 2 / 4 + (η + 2) * S ≤ 2 * varpi * L)
    (hη : 0 ≤ η) (hT : T ≤ S) :
    Real.exp (-2 * varpi * L + η * T) ≤ Real.exp (-β * S ^ 2 / 4 - 2 * S) := by
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_left hT hη
  linarith
def profileVarianceArgument (C_D S z : ℝ) : ℝ := Real.exp z / (C_D * S)
def profileVarianceDegree (β S z : ℝ) : ℕ := Nat.floor (β * quadraticProfile S z)
def profileVarianceWeight (C₀ C_D β S z : ℝ) : ℝ :=
  factorialSeries (profileVarianceDegree β S z) (profileVarianceArgument C_D S z) *
    max 1 (C₀ / profileVarianceArgument C_D S z)
theorem profileVarianceWeight_uniform_bound 
    (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D) (hDβ : 4 * β ≤ C_D)
    (hβ : 0 ≤ β) (hS : 2 ≤ S) (hz : z ≤ S) :
    profileVarianceWeight C₀ C_D β S z ≤
      2 * C₀ * C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by
  have hS₀ : 0 < S := by linarith
  have hC₀ : 0 < C₀ := by linarith
  have hD₀ : 0 < C_D := by linarith
  have hCS1 : 1 ≤ C_D * S := by nlinarith
  have : 1 ≤ C_D ^ 2 * S ^ 2 := by nlinarith [sq_nonneg (C_D * S - 1)]
  have : 1 ≤ Real.exp (β * S ^ 2 / 4) := Real.one_le_exp_iff.2 (by positivity)
  have hfactor : 1 ≤ C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by nlinarith
  rcases le_or_gt z 0 with hz0 | hz0
  have h_profileVarianceWeight_coarse_bound : profileVarianceWeight C₀ C_D β S z ≤ 2 * C₀ := by
    have hC₀ : 0 < C₀ := by linarith
    have hS₀ : 0 < S := by linarith
    have hD₀ : 0 < C_D := by linarith
    have hCS : 0 < C_D * S := mul_pos hD₀ hS₀
    have hCS1 : 1 ≤ C_D * S := by nlinarith
    have hx : 0 < profileVarianceArgument C_D S z := div_pos (Real.exp_pos z) hCS
    have he : Real.exp z ≤ 1 := Real.exp_le_one_iff.2 hz0
    have hx1 : profileVarianceArgument C_D S z ≤ 1 := (div_le_one hCS).2 (he.trans hCS1)
    have hxC := hx1.trans hC
    have hm : 1 ≤ C₀ / profileVarianceArgument C_D S z :=
      (le_div_iff₀ hx).2 (by simpa using hxC)
    have h_profileVariance_coarse_ratio : (profileVarianceDegree β S z ) * profileVarianceArgument C_D S z ≤ 1 / 2 := by
      have hS₀ : 0 < S := by linarith
      have hD₀ : 0 < C_D := by linarith
      have hCS : 0 < C_D * S := mul_pos hD₀ hS₀
      have hQ : 0 ≤ quadraticProfile S z :=
        (by positivity : 0 ≤ S / 4).trans (quadraticProfile_lower hS₀)
      have hf := Nat.floor_le (mul_nonneg hβ hQ)
      have := mul_le_mul_of_nonneg_right hf (Real.exp_pos z).le
      have h_quadraticProfile_coarse_bound : Real.exp z * quadraticProfile S z ≤ 5 * S / 4 := by
        let f : ℝ → ℝ := fun x => Real.exp x * quadraticProfile S x
        have hd x : HasDerivAt f
            (Real.exp x * (quadraticProfile S x + 2 * (x - S) / S)) x := by
          have h_quadraticProfile_hasDerivAt : HasDerivAt (quadraticProfile S) (2 * (x - S) / S) x := by
            convert (hasDerivAt_const x (S / 4)).add
              (((hasDerivAt_const x S).sub (hasDerivAt_id x)).pow 2 |>.div_const S) using 1
            · funext x
              simp [quadraticProfile, div_eq_mul_inv]
            · simp only [Pi.sub_apply, id_eq]
              ring
          convert (Real.hasDerivAt_exp x).mul h_quadraticProfile_hasDerivAt using 1
          ring
        have hm : MonotoneOn f (Iic 0) := by
          apply monotoneOn_of_deriv_nonneg (convex_Iic 0)
            (fun x hx => (hd x).continuousAt.continuousWithinAt)
            (fun x hx => (hd x).differentiableAt.differentiableWithinAt)
          intro x hx
          rw [(hd x).deriv]
          have : x ≤ 0 := by simpa using (interior_subset hx)
          have : 0 ≤ (S - x) * (S - x - 2) := by
            apply mul_nonneg <;> linarith
          have hid : quadraticProfile S x + 2 * (x - S) / S =
              ((S - x) * (S - x - 2) + S ^ 2 / 4) / S := by
            dsimp [quadraticProfile]
            field_simp
            ring
          rw [hid]
          positivity
        have h := hm hz0 (by simp) hz0
        have hzero : f 0 = 5 * S / 4 := by
          dsimp [f, quadraticProfile]
          rw [Real.exp_zero, one_mul]
          field_simp
          ring
        rw [hzero] at h
        exact h
      have := mul_le_mul_of_nonneg_left h_quadraticProfile_coarse_bound hβ
      have := mul_le_mul_of_nonneg_right hDβ hS₀.le
      unfold profileVarianceDegree profileVarianceArgument
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hCS).2
      nlinarith [mul_nonneg hβ hS₀.le]
    have hs := factorialSeries_coarse_bound hx.le
      h_profileVariance_coarse_ratio
    unfold profileVarianceWeight
    rw [max_eq_right hm]
    calc
      _ ≤ 2 * profileVarianceArgument C_D S z * (C₀ / profileVarianceArgument C_D S z) :=
        mul_le_mul_of_nonneg_right hs (div_nonneg hC₀.le hx.le)
      _ = 2 * C₀ := by field_simp
  · apply h_profileVarianceWeight_coarse_bound.trans
    have hm := mul_le_mul_of_nonneg_left hfactor (by positivity : 0 ≤ 2 * C₀)
    simpa only [mul_one, mul_assoc] using hm
  have h_profileVarianceWeight_fine_bound : profileVarianceWeight C₀ C_D β S z ≤
      C₀ * C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by
    have hC₀ : 0 < C₀ := by linarith
    have hS₀ : 0 < S := by linarith
    have hD₀ : 0 < C_D := by linarith
    have hCS : 0 < C_D * S := mul_pos hD₀ hS₀
    have : 1 ≤ C_D * S := by nlinarith
    have hx : 0 < profileVarianceArgument C_D S z := div_pos (Real.exp_pos z) hCS
    have h_profileVariance_fine_degree_bounds : (profileVarianceDegree β S z ) ≤ C_D * S ∧
        (profileVarianceDegree β S z ) * z ≤ β * S ^ 2 / 4 := by
      have hQ : 0 ≤ quadraticProfile S z :=
        (by positivity : 0 ≤ S / 4).trans (quadraticProfile_lower hS₀)
      have hf := Nat.floor_le (mul_nonneg hβ hQ)
      have h_quadraticProfile_fine_upper : quadraticProfile S z ≤ 5 * S / 4 := by
        have hs : (S - z) ^ 2 ≤ S ^ 2 := by
          nlinarith [mul_nonneg hz0.le (sub_nonneg.mpr hz)]
        dsimp [quadraticProfile]
        have hd := (div_le_div_iff_of_pos_right hS₀).mpr hs
        have he : S ^ 2 / S = S := by field_simp
        rw [he] at hd
        linarith
      have := mul_le_mul_of_nonneg_left h_quadraticProfile_fine_upper hβ
      have h_quadraticProfile_fine_factorization : S ^ 2 / 4 - z * quadraticProfile S z =
          (S - z) * (2 * z - S) ^ 2 / (4 * S) := by
        dsimp [quadraticProfile]
        field_simp
        ring
      have := h_quadraticProfile_fine_factorization
      have : 0 ≤ (S - z) * (2 * z - S) ^ 2 / (4 * S) := by
        exact div_nonneg (mul_nonneg (sub_nonneg.mpr hz) (sq_nonneg _)) (by positivity)
      have := mul_le_mul_of_nonneg_left (by linarith) hβ
      have := mul_le_mul_of_nonneg_right hDβ hS₀.le
      unfold profileVarianceDegree
      constructor
      · nlinarith [mul_nonneg hβ hS₀.le]
      · have := mul_le_mul_of_nonneg_right hf hz0.le
        nlinarith
    obtain ⟨hdeg, hprod⟩ := h_profileVariance_fine_degree_bounds
    have he : (C_D * S) * profileVarianceArgument C_D S z = Real.exp z := by
      unfold profileVarianceArgument
      rw [← mul_div_assoc, mul_comm (C_D * S), mul_div_cancel_right₀ _ hCS.ne']
    have hweight : max 1 (C₀ / profileVarianceArgument C_D S z) ≤ C₀ * C_D * S := by
      apply max_le
      · nlinarith
      · apply (div_le_iff₀ hx).2
        have hm := mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.2 hz0.le) hC₀.le
        calc
          C₀ ≤ C₀ * Real.exp z := by simpa using hm
          _ = C₀ * C_D * S * profileVarianceArgument C_D S z := by rw [← he]; ring
    unfold profileVarianceWeight profileVarianceArgument
    exact factorialSeries_fine_weighted hz0.le hC₀.le hCS hdeg hprod
      (by positivity) hweight
  · apply h_profileVarianceWeight_fine_bound.trans
    have : 0 ≤ C₀ * C_D ^ 2 * S ^ 2 * Real.exp (β * S ^ 2 / 4) := by positivity
    nlinarith
def actualVarianceMaximum (δ a C C₀ C_D γ β x : ℝ) : ℝ :=
  (Finset.range (terminalAllocationLevel δ a C (C₀ * C_D) γ x + 1)).sup'
    ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (fun j =>
      profileVarianceWeight C₀ C_D β (allocationWidth a C x)
        (allocationLevelPosition δ a C (C₀ * C_D) x j))
def actualAllocationVarianceRatio (δ a C C₀ C_D γ β η varpi x : ℝ) : ℝ :=
  Real.exp (-2 * varpi * Real.log x + η *
    roundedTerminalDepth δ (Real.log x) (candidateTerminalDepth a C (C₀ * C_D) γ x)) *
      actualVarianceMaximum δ a C C₀ C_D γ β x
set_option maxHeartbeats 600000 in
theorem eventually_actualAllocationVarianceRatio_bound 
    (hδ : 0 < δ) (ha : 0 < a) (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D)
    (hDβ : 4 * β ≤ C_D) (hβ : 0 < β) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (C ) (hshift : C = 1 + 2 * (η + 2) / β) (hcoef : β * a ^ 2 / 4 = 2 * varpi) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ actualAllocationVarianceRatio δ a C C₀ C_D γ β η varpi x ∧
      actualAllocationVarianceRatio δ a C C₀ C_D γ β η varpi x ≤
        2 * C₀ * C_D ^ 2 * (allocationWidth a C x) ^ 2 * Real.exp (-2 * allocationWidth a C x) := by
  have hH : 0 < C₀ * C_D := by positivity
  have : 0 < C_D := by linarith
  have hw := allocationWidth_tendsto_atTop ha C
  have h_eventually_actualVarianceMaximum_bound : ∀ᶠ x : ℝ in atTop,
      actualVarianceMaximum δ a C C₀ C_D γ β x ≤
        2 * C₀ * C_D ^ 2 * (allocationWidth a C x) ^ 2 *
          Real.exp (β * (allocationWidth a C x) ^ 2 / 4) := by
    have hH : 0 < C₀ * C_D := by positivity
    filter_upwards [(allocationWidth_tendsto_atTop ha C).eventually (eventually_ge_atTop 2),
      eventually_actual_allocation_level_range hδ ha hH hγ C] with x hx hz
    unfold actualVarianceMaximum
    apply Finset.sup'_le
    intro j hj
    exact profileVarianceWeight_uniform_bound hC hD1 hDβ hβ.le hx (hz j hj).2
  filter_upwards [hw.eventually (eventually_ge_atTop 2),
    (hw.const_mul_atTop hH).eventually (eventually_ge_atTop 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 0),
    eventually_terminal_cell_log_nonneg ha hH C γ,
    h_eventually_actualVarianceMaximum_bound]
    with x hS hHS hL hLT hmax
  have hS₀ : 0 < allocationWidth a C x := by linarith
  have h_actualVarianceMaximum_nonneg : 0 ≤ actualVarianceMaximum δ a C C₀ C_D γ β x := by
    have hw : 0 ≤ profileVarianceWeight C₀ C_D β (allocationWidth a C x)
        (allocationLevelPosition δ a C (C₀ * C_D) x 0) := by
      unfold profileVarianceWeight
      apply mul_nonneg
      · apply factorialSeries_nonneg
        unfold profileVarianceArgument
        positivity
      · exact zero_le_one.trans (le_max_left _ _)
    apply hw.trans
    unfold actualVarianceMaximum
    exact Finset.le_sup' (s := Finset.range (terminalAllocationLevel δ a C (C₀ * C_D) γ x + 1))
      (b := 0) (fun j => profileVarianceWeight C₀ C_D β (allocationWidth a C x)
        (allocationLevelPosition δ a C (C₀ * C_D) x j)) (Finset.mem_range.2 (Nat.succ_pos _))
  have hn : 0 ≤ actualVarianceMaximum δ a C C₀ C_D γ β x :=
    h_actualVarianceMaximum_nonneg
  have hdef : allocationWidth a C x =
      a * Real.sqrt (Real.log x) - (1 + 2 * (η + 2) / β) := by unfold allocationWidth; rw [hshift]
  have hbudget := quadratic_allocation_budget hβ (by linarith) hS₀.le hdef
  have hbase : β * (a * Real.sqrt (Real.log x)) ^ 2 / 4 = 2 * varpi * Real.log x := by
    rw [mul_pow, Real.sq_sqrt hL]
    calc
      β * (a ^ 2 * Real.log x) / 4 = (β * a ^ 2 / 4) * Real.log x := by ring
      _ = _ := by rw [hcoef]
  rw [hbase] at hbudget
  have ht := (roundedTerminalDepth_bounds hδ hLT).2
  have hr : Real.exp (-2 * varpi * Real.log x + η *
      roundedTerminalDepth δ (Real.log x) (candidateTerminalDepth a C (C₀ * C_D) γ x)) ≤
      Real.exp (-β * (allocationWidth a C x) ^ 2 / 4 - 2 * allocationWidth a C x) :=
    allocation_budget_reserve (β := β) (S := allocationWidth a C x)
      (η := η) (varpi := varpi) (L := Real.log x)
      (T := roundedTerminalDepth δ (Real.log x) (candidateTerminalDepth a C (C₀ * C_D) γ x))
      hbudget hη (ht.trans (by unfold candidateTerminalDepth; have : 0 ≤ Real.log ((C₀ * C_D) * allocationWidth a C x) := Real.log_nonneg hHS; have hlogS : 0 ≤ Real.log (allocationWidth a C x) := Real.log_nonneg (by linarith); linarith [mul_nonneg hγ hlogS]))
  constructor
  · unfold actualAllocationVarianceRatio
    exact mul_nonneg (Real.exp_pos _).le hn
  · unfold actualAllocationVarianceRatio
    calc
      _ ≤ Real.exp (-β * (allocationWidth a C x) ^ 2 / 4 - 2 * allocationWidth a C x) *
          (2 * C₀ * C_D ^ 2 * (allocationWidth a C x) ^ 2 *
            Real.exp (β * (allocationWidth a C x) ^ 2 / 4)) :=
        mul_le_mul hr hmax hn (Real.exp_pos _).le
      _ = 2 * C₀ * C_D ^ 2 * (allocationWidth a C x) ^ 2 *
          (Real.exp (-β * (allocationWidth a C x) ^ 2 / 4 - 2 * allocationWidth a C x) *
            Real.exp (β * (allocationWidth a C x) ^ 2 / 4)) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring
theorem actualAllocationVarianceRatio_tends_zero 
    (hδ : 0 < δ) (ha : 0 < a) (hC : 1 ≤ C₀) (hD1 : 1 ≤ C_D)
    (hDβ : 4 * β ≤ C_D) (hβ : 0 < β) (hγ : 0 ≤ γ) (hη : 0 ≤ η)
    (C ) (hshift : C = 1 + 2 * (η + 2) / β) (hcoef : β * a ^ 2 / 4 = 2 * varpi) :
    Tendsto (actualAllocationVarianceRatio δ a C C₀ C_D γ β η varpi) atTop (𝓝 0) := by
  have hb := eventually_actualAllocationVarianceRatio_bound hδ ha hC hD1 hDβ hβ hγ hη C hshift hcoef
  apply squeeze_zero' (hb.mono fun x hx => hx.1) (hb.mono fun x hx => hx.2)
  have h_tendsto_allocation_reserve_bound : Tendsto (fun S : ℝ => 2 * C₀ * C_D ^ 2 * S ^ 2 * Real.exp (-2 * S))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ↑2 2 (by norm_num)).const_mul
      (2 * C₀ * C_D ^ 2)
    convert h using 1 <;> simp [mul_assoc]
  exact h_tendsto_allocation_reserve_bound.comp (allocationWidth_tendsto_atTop ha C)
def paperDyadicTotalDegree  (C : ModelConstants d) (a offset H n : ℝ) (j : ℕ) : ℕ :=
  paperDyadicApproximationDegree C a offset H n j + anchoredDimension d C.order + 1
theorem eventually_paper_total_degree_eq_floor  (C : ModelConstants d)
    (hs : 1 < C.smoothness) (a offset H : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℝ in atTop, ∀ j : ℕ,
      paperDyadicTotalDegree C a offset H n j =
      Nat.floor (paperDegreeSlope C * quadraticProfile (allocationWidth a offset n)
        (allocationLevelPosition (paperDyadicStep C) a offset H n j)) := by
  have hβ : 0 < paperDegreeSlope C := div_pos (paperSpatialExponent_pos C hs) (paperTau_pos C)
  filter_upwards [eventually_width_degree_threshold ha hβ offset (paperPolynomialDimension C),
    (allocationWidth_tendsto_atTop ha offset).eventually (eventually_gt_atTop ↑0)]
    with n hn hS
  intro j
  unfold paperDyadicTotalDegree paperDyadicApproximationDegree actualApproximationDegree allocatedApproximationDegree
  have h_paperPolynomialDimension_eq_anchoredDimension_add_one : paperPolynomialDimension C = anchoredDimension d C.order + 1 := by
    unfold paperPolynomialDimension anchoredDimension
    rw [anchoredIndex_card]
    have : 0 < (d + C.order).choose d := Nat.choose_pos (by omega)
    omega
  rw [Nat.add_assoc, ← h_paperPolynomialDimension_eq_anchoredDimension_add_one]
  exact Nat.sub_add_cancel (profile_coordinate_order_admissible _ hβ.le hS (by linarith))
theorem eventually_paper_degree_three_block_guards  (C : ModelConstants d)
    (hs : 1 < C.smoothness) (a offset H : ℝ) (ha : 0 < a) (hH : 0 < H) :
    ∀ᶠ n : ℕ in atTop, ∀ j ≤ paperDyadicTerminalLevel C a offset H n,
      paperDyadicTotalDegree C a offset H n j ≤ threeBlockSize n ∧
      0 < (threeBlockSize n : ℝ) / 2 ∧
      (threeBlockSize n : ℝ) / 2 ≤
        (threeBlockSize n : ℝ) - (paperDyadicTotalDegree C a offset H n j : ℝ) + 1 := by
  have h_eventually_paper_total_degree_lt_fraction {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n : ℝ in atTop, ∀ j ≤ paperDyadicTerminalLevel C a offset H n,
      (paperDyadicTotalDegree C a offset H n j : ℝ) < ε * n := by
    have h_eventually_paper_total_degree_log_bound : ∀ᶠ n : ℝ in atTop, ∀ j ≤ paperDyadicTerminalLevel C a offset H n,
        (paperDyadicTotalDegree C a offset H n j : ℝ) ≤
          allocationDegreeCoefficient a (paperDegreeSlope C) * (Real.log n) ^ (3 / 2 : ℝ) := by
      have hβ  := (div_pos (paperSpatialExponent_pos C hs) (paperTau_pos C)).le
      have hγ : 0 ≤ paperDegreeReserve C := by
        exact div_nonneg (by positivity) (paperSpatialExponent_pos C hs).le
      have hb := eventually_allocation_degree_bound ha hβ offset
        (fun n => Finset.range (terminalAllocationLevel (paperDyadicStep C) a offset H (paperDegreeReserve C) n + 1))
        (allocationLevelPosition (paperDyadicStep C) a offset H)
        (eventually_actual_allocation_level_range (paperDyadicStep_pos C) ha hH hγ offset)
      filter_upwards [eventually_paper_total_degree_eq_floor C hs a offset H ha, hb] with n he hn
      intro j hj
      rw [he]
      exact hn j (Finset.mem_range.mpr (by change j < paperDyadicTerminalLevel C a offset H n + 1; omega))
    filter_upwards [h_eventually_paper_total_degree_log_bound,
      eventually_log_power_lt_sample (3 / 2) (allocationDegreeCoefficient a (paperDegreeSlope C)) hε]
      with n hn he
    intro j hj
    exact (hn j hj).trans_lt he
  have hb : ∀ᶠ n : ℕ in atTop, ∀ j ≤ paperDyadicTerminalLevel C a offset H n,
      (paperDyadicTotalDegree C a offset H n j : ℝ) < (1 / 8 : ℝ) * n :=
    tendsto_natCast_atTop_atTop.eventually
      (h_eventually_paper_total_degree_lt_fraction (by norm_num))
  filter_upwards [hb, eventually_ge_atTop ↑6] with n hn h6
  intro j hj
  have := threeBlockSize_fraction h6
  have := hn j hj
  have hhalf : (paperDyadicTotalDegree C a offset H n j : ℝ) ≤ (threeBlockSize n : ℝ) / 2 := by
    linarith
  have : 0 < (threeBlockSize n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < ↑2) (threeBlockSize_two_le h6))
  refine ⟨?_, by positivity, by linarith⟩
  exact_mod_cast (hhalf.trans (by linarith : (threeBlockSize n : ℝ) / 2 ≤ threeBlockSize n))
def paperPilotMomentFactor  (C : ModelConstants d) (A : ℝ) : ℝ :=
  A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
    preconditionedPilotMomentConstant C C.order)
theorem paperPilotMomentFactor_nonneg  (C : ModelConstants d) (A : ℝ) :
    0 ≤ paperPilotMomentFactor C A := mul_nonneg (sq_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos C _).le)
theorem factorialSeries_mono_argument (D ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    factorialSeries D x ≤ factorialSeries D y := by
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy _) (Nat.cast_nonneg _)
theorem paper_pilot_series_weight_le_profile  (C : ModelConstants d) (A a offset : ℝ)
    {n Λ C₀ C_D : ℝ} (hn : 0 < n) (hΛ : n / 12 ≤ Λ) (hΛn : Λ ≤ n)
    (hC : 0 < C₀) (hD : 0 < C_D) (hS : 0 < allocationWidth a offset n)
    (hcoef : 12 * paperPilotMomentFactor C A ≤ C₀) (j : ℕ)
    (hdegree : paperDyadicTotalDegree C a offset (C₀ * C_D) n j =
      Nat.floor (paperDegreeSlope C * quadraticProfile (allocationWidth a offset n)
        (allocationLevelPosition (paperDyadicStep C) a offset (C₀ * C_D) n j))) :
    dyadicPilotSeries C A Λ j (paperDyadicApproximationDegree C a offset (C₀ * C_D) n j) *
        max 1 (Λ / dyadicPilotScale d j) ≤
      profileVarianceWeight C₀ C_D (paperDegreeSlope C) (allocationWidth a offset n)
        (allocationLevelPosition (paperDyadicStep C) a offset (C₀ * C_D) n j) := by
  have h_actual_profileVarianceWeight_eq_cell_weight {δ : ℝ} {β : ℝ} {x : ℝ} {a : ℝ} {C : ℝ} (hx : 0 < x) (hS : 0 < allocationWidth a C x) : profileVarianceWeight C₀ C_D β (allocationWidth a C x)
      (allocationLevelPosition δ a C (C₀ * C_D) x j) =
        factorialSeries (profileVarianceDegree β (allocationWidth a C x)
          (allocationLevelPosition δ a C (C₀ * C_D) x j))
          (C₀ * Real.exp (δ * j) / x) * max 1 (x / Real.exp (δ * j)) := by
    unfold profileVarianceWeight
    have h_actual_profileVarianceArgument_eq_cell_fraction : profileVarianceArgument C_D (allocationWidth a C x)
        (allocationLevelPosition δ a C (C₀ * C_D) x j) = C₀ * Real.exp (δ * j) / x := by
      unfold profileVarianceArgument allocationLevelPosition
      rw [Real.exp_add, Real.exp_sub, Real.exp_log hx,
        Real.exp_log (mul_pos (mul_pos hC hD) hS)]
      field_simp
    rw [h_actual_profileVarianceArgument_eq_cell_fraction]
    congr 2
    field_simp
  rw [(h_actual_profileVarianceWeight_eq_cell_weight hn hS), ← dyadicPilotScale_eq_exp C]
  have h_dyadicPilotSeries_eq_factorialSeries (m : ℕ) : dyadicPilotSeries C A Λ j m = factorialSeries (m + anchoredDimension d C.order + 1)
      (paperPilotMomentFactor C A * dyadicPilotScale d j / Λ) := by
    unfold dyadicPilotSeries factorialSeries paperPilotMomentFactor
    simpa only [mul_assoc] using (Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      ((k + 1).factorial : ℝ) *
        (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
          preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ (k + 1))
      (m + anchoredDimension d C.order + 1))
  rw [h_dyadicPilotSeries_eq_factorialSeries]
  have h_paper_pilot_series_argument_le : paperPilotMomentFactor C A * dyadicPilotScale d j / Λ ≤ C₀ * dyadicPilotScale d j / n := by
    have hk := (dyadicPilotScale_pos d j).le
    apply (div_le_div_iff₀ ((div_pos hn (by norm_num)).trans_le hΛ) hn).mpr
    have := mul_le_mul_of_nonneg_right hcoef hk
    have := mul_le_mul_of_nonneg_left hΛ (mul_nonneg ((mul_nonneg (by norm_num) (paperPilotMomentFactor_nonneg C A)).trans hcoef) hk)
    nlinarith
  have hseries := factorialSeries_mono_argument
    (paperDyadicTotalDegree C a offset (C₀ * C_D) n j) (div_nonneg (mul_nonneg (paperPilotMomentFactor_nonneg C A) (dyadicPilotScale_pos _ _).le) ((div_pos hn (by norm_num)).trans_le hΛ).le)
    h_paper_pilot_series_argument_le
  rw [hdegree] at hseries
  change factorialSeries (paperDyadicTotalDegree C a offset (C₀ * C_D) n j) _ * _ ≤ _
  rw [hdegree]
  exact mul_le_mul hseries (max_le_max le_rfl (div_le_div_of_nonneg_right hΛn (dyadicPilotScale_pos _ _).le))
    (by positivity) (factorialSeries_nonneg _
      (div_nonneg (mul_nonneg hC.le (dyadicPilotScale_pos _ _).le) hn.le))
theorem uniform_domain_admissible_dyadicFinPilotMoments_uniform_bound  (C : ModelConstants d) :
    ∃ W : ℝ, 0 < W ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ t : Bool,
        ‖dyadicFinPilotMoments (ℓ := C.order) θ j x t‖ ≤ W := by
  obtain ⟨W, hW, hb⟩ := anchoredFinMomentFamilies_uniform_bound (d := d) (ℓ := C.order)
    C.densityUpper C.holderBound (zero_le_one.trans C.one_lt_densityUpper.le) C.holderBound_pos.le
  refine ⟨W, hW, ?_⟩
  intro Udom θ hθ j x hx t
  rw [dyadicFinPilotMoments_eq_anchored (C.withDomain Udom) θ hθ j x hx]
  exact hb _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx) _ _
    ((dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x).mono
      (fun w hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩))
    (fun w hw => admissible_regression_value_bound (C.withDomain Udom) θ hθ _ (dyadicCellAffine_mem_cube j x w hw)) t
end NearlyMinimax
