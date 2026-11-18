module

public import Mathlib
public import NearlyMinimax.BoundedPairMeanOperators
public import NearlyMinimax.PaperCorollaries
public import NearlyMinimax.PreconditionedPilot

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Matrix MvPolynomial
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.L2Operator

namespace NearlyMinimax

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 1500000

-- 1. Moment families, scalar row functional & affine increment vectors

def anchoredFinMomentFamilies {d ℓ : ℕ} (u : Covariate d)
    (p f : Covariate d → ℝ) : Bool → Fin (anchoredDimension d ℓ) → ℝ :=
  fun t i => anchoredPreconditionedMoment u p (if t then fun _ => 1 else f)
    ((Fintype.equivFin (AnchoredIndex d ℓ)).symm i)

theorem anchoredFinMomentFamilies_uniform_bound {d ℓ : ℕ}
    (b F : ℝ) (hb : 0 ≤ b) (_hF : 0 ≤ F) :
    ∃ W : ℝ, 0 < W ∧ ∀ u ∈ unitCube d, ∀ p f : Covariate d → ℝ,
      (∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) →
      (∀ w ∈ unitCube d, |f w| ≤ F) →
      ∀ t, ‖anchoredFinMomentFamilies (ℓ := ℓ) u p f t‖ ≤ W := by
  obtain ⟨W, hW, hm⟩ := anchoredPreconditionedMoment_uniform_bound
    (d := d) (ℓ := ℓ) b (max 1 F) hb (zero_le_one.trans (le_max_left _ _))
  refine ⟨W, hW, fun u hu p f hp hf t => (pi_norm_le_iff_of_nonneg hW.le).mpr fun i => ?_⟩
  refine (norm_le_pi_norm _ ((Fintype.equivFin (AnchoredIndex d ℓ)).symm i)).trans
    (hm u hu p (if t then fun _ => 1 else f) hp fun w hw => ?_)
  cases t
  · exact (hf w hw).trans (le_max_right _ _)
  · simp

def rowFunctional {r : ℕ} (row : Fin r → ℝ) : (Fin r → ℝ) →L[ℝ] ℝ :=
  ∑ i, row i • (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ)

@[simp] theorem rowFunctional_apply {r : ℕ} (row z : Fin r → ℝ) :
    rowFunctional row z = row ⬝ᵥ z := by
  simp [rowFunctional, dotProduct, _root_.sum_apply, smul_eq_mul]

theorem rowFunctional_norm_le {r : ℕ} (row : Fin r → ℝ) :
    ‖rowFunctional row‖ ≤ ∑ i, |row i| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun z => ?_
  rw [rowFunctional_apply, dotProduct]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans_eq (Finset.sum_mul ..).symm)
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (abs_nonneg _)

def incrementFinScalar (r : ℕ) (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (row : Fin r → ℝ) :
    (Fin (Fintype.card (incrementVariables r)) → ℝ) → ℝ :=
  fun x => row ⬝ᵥ incrementFinVector r lo hi T y m x

theorem incrementFinScalar_iteratedFDeriv (r : ℕ) [NeZero r] (lo hi : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m k : ℕ) (row : Fin r → ℝ)
    (x : Fin (Fintype.card (incrementVariables r)) → ℝ)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    iteratedFDeriv ℝ k (incrementFinScalar r lo hi T y m row) x v =
      rowFunctional row (iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m) x v) := by
  have h := (rowFunctional row).iteratedFDeriv_comp_left (x := x)
    (incrementFinVector_contDiff r lo hi T y m).contDiffAt (show (k : WithTop ℕ∞) ≤ ⊤ from le_top)
  rw [show (rowFunctional row) ∘ incrementFinVector r lo hi T y m = incrementFinScalar r lo hi T y m row from
    funext fun _ => rowFunctional_apply row _] at h
  exact congrArg (fun D => D v) h

def incrementFinRawVector (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (response : Bool) (m : ℕ) :
    (Fin (Fintype.card (incrementVariables r)) → ℝ) → Fin r → ℝ :=
  fun x i => MvPolynomial.eval x
    (MvPolynomial.rename (Fintype.equivFin (incrementVariables r))
      (rawIncrementEntryPolynomial r a b T response m i))

theorem incrementFinVector_affine (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) :
    incrementFinVector r a b T y m = incrementFinRawVector r a b T false m -
      y • incrementFinRawVector r a b T true m := by
  funext x i
  simp only [incrementFinVector, incrementFinPolynomial, incrementFinRawVector,
    MvPolynomial.eval_rename, incrementEntryPolynomial_affine,
    map_sub, map_mul, MvPolynomial.eval_C, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

-- 2. Dyadic fit bounds, physical evaluation & index nonemptiness

theorem bounded_rpow_le_linear (r M s : ℝ) (hr : 0 ≤ r) (hrM : r ≤ M) (hs : 1 ≤ s) :
    r ^ s ≤ max 1 (M ^ s) * r := by
  by_cases hr1 : r ≤ 1
  · exact (Real.rpow_le_self_of_le_one hr hr1 hs).trans
      (by simpa using mul_le_mul_of_nonneg_right (le_max_left 1 (M ^ s)) hr)
  · have h1r : 1 ≤ r := le_of_not_ge hr1
    exact ((Real.rpow_le_rpow hr hrM (zero_le_one.trans hs)).trans
      (by simpa using mul_le_mul_of_nonneg_left h1r (Real.rpow_nonneg (hr.trans hrM) s))).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hr)

theorem anchoredTransport_euclidean_norm {d ℓ : ℕ} (c : AnchoredIndex d ℓ → ℝ) :
    ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredTransport d ℓ *ᵥ c)‖ ≤
      (1 / 2) * ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ := by
  have h : ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredTransport d ℓ *ᵥ c)‖ ≤
      ‖anchoredTransport d ℓ‖ * ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ := by
    simpa [EuclideanSpace.equiv] using
      Matrix.l2_opNorm_mulVec (anchoredTransport d ℓ) ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c)
  exact h.trans (mul_le_mul_of_nonneg_right (anchoredTransport_norm_le_half d ℓ) (norm_nonneg _))

def dyadicPopulationIncrement {d ℓ : ℕ} (θ : RegressionParameter d) (x : Covariate d) :
    ℕ → AnchoredIndex d ℓ → ℝ := anchoredIncrement fun j => dyadicPopulationFit θ j x

theorem dyadicPopulationIncrement_error_identity {d ℓ : ℕ} (θ : RegressionParameter d)
    (x : Covariate d) (c : AnchoredIndex d ℓ → ℝ) (j : ℕ) :
    dyadicPopulationIncrement θ x (j + 1) =
      (dyadicPopulationFit θ (j + 1) x - dyadicTaylorCoefficients c (j + 1)) -
        anchoredTransport d ℓ *ᵥ (dyadicPopulationFit θ j x - dyadicTaylorCoefficients c j) := by
  rw [dyadicTaylorCoefficients_succ, Matrix.mulVec_sub]
  unfold dyadicPopulationIncrement anchoredIncrement; abel

theorem dyadic_inverse_scale_succ (j : ℕ) :
    ((2 : ℝ) ^ j)⁻¹ = 2 * ((2 : ℝ) ^ (j + 1))⁻¹ := by rw [pow_succ]; field_simp

theorem dyadicPopulationIncrement_telescope {d ℓ : ℕ} (θ : RegressionParameter d)
    (x z : Covariate d) (J : ℕ) :
    dyadicAnchoredFeature J x z ⬝ᵥ dyadicPopulationFit (ℓ := ℓ) θ J x =
      ∑ j ∈ Finset.range (J + 1), dyadicAnchoredFeature j x z ⬝ᵥ dyadicPopulationIncrement (ℓ := ℓ) θ x j :=
  (anchored_increment_telescope (fun j => dyadicPopulationFit θ j x) x z J).symm

theorem dyadicCellAffine_same_cell {d : ℕ} (j : ℕ) (x y : Covariate d)
    (hcell : y ∈ dyadicPilotCell j x) :
    dyadicCellAffine j x (dyadicNormalizedAnchor j y) = y := by
  have hc : regularGridCell ((2 : ℕ) ^ j) (by positivity) y =
      regularGridCell ((2 : ℕ) ^ j) (by positivity) x := hcell
  simpa only [dyadicCellAffine, hc] using dyadicCellAffine_anchor j y

theorem dyadicPopulationFit_physical_evaluation {d ℓ : ℕ} (j : ℕ)
    (x y : Covariate d) (hcell : y ∈ dyadicPilotCell j x) (c : AnchoredIndex d ℓ → ℝ) :
    anchoredFitPolynomial (dyadicNormalizedAnchor j x) c (dyadicNormalizedAnchor j y) =
      dyadicAnchoredFeature j x y ⬝ᵥ c := by
  have he := dyadicCellAffine_same_cell j x y hcell
  unfold anchoredFitPolynomial dotProduct
  refine Finset.sum_congr rfl fun γ _ => ?_
  have h := dyadicAnchoredFeature_affine j x (dyadicNormalizedAnchor j y) γ
  change dyadicAnchoredFeature j x (dyadicCellAffine j x (dyadicNormalizedAnchor j y)) γ =
    anchoredFeature (dyadicNormalizedAnchor j x) (dyadicNormalizedAnchor j y) γ at h
  rw [he] at h; rw [h]; ring

theorem positive_rpow_times_distance (h s r : ℝ) (hh : 0 < h) :
    h ^ s * r = (h * r) * h ^ (s - 1) := by
  conv_lhs => rw [show s = (s - 1) + 1 by ring, Real.rpow_add hh, Real.rpow_one]
  ring

private theorem dyadicPopulationFit_preconditioner_cancels {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (_hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    (dyadicPreconditionedGram (ℓ := ℓ) θ j x)⁻¹ *ᵥ
      ((dyadicKnownGram j x)⁻¹ *ᵥ (dyadicResponseMoment θ j x - θ.regression x • dyadicConstantMoment θ j x)) =
        dyadicPopulationFit θ j x := by
  have hB := (Matrix.isUnit_iff_isUnit_det _).mp (dyadicKnownGram_posDef (ℓ := ℓ) j x).isUnit
  letI := (dyadicKnownGram_posDef (ℓ := ℓ) j x).isUnit.invertible
  unfold dyadicPreconditionedGram dyadicPopulationFit
  rw [Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible, Matrix.mulVec_mulVec,
    Matrix.mul_assoc _ (dyadicKnownGram j x) (dyadicKnownGram j x)⁻¹,
    Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]

theorem anchoredIndex_nonempty_of_one_lt_smoothness {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) : Nonempty (AnchoredIndex d C.order) := by
  have horder : 0 < C.order := by
    by_contra h
    have hz : C.order = 0 := by omega
    have hle := C.smoothness_le_order_add_one
    simp only [hz, Nat.cast_zero, zero_add] at hle; linarith
  exact anchoredIndex_nonempty C.dimension_pos horder

-- 3. Increment pilot features, joint measurability, series envelope & sample facts

def anchoredFinIndex {d ℓ : ℕ} (i : Fin (anchoredDimension d ℓ)) : AnchoredIndex d ℓ :=
  (Fintype.equivFin (AnchoredIndex d ℓ)).symm i

def dyadicIncrementFeature {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (v : incrementVariables (anchoredDimension d ℓ)) (z : Observation d) : ℝ :=
  match v with
  | Sum.inl (Sum.inl it) =>
    preconditionedPilotFeature j x (Sum.inl (anchoredFinIndex it.1, anchoredFinIndex it.2)) z
  | Sum.inl (Sum.inr it) =>
    if j = 0 then (if it.2.1 = it.2.2 then 1 else 0) else
      preconditionedPilotFeature (j - 1) x (Sum.inl (anchoredFinIndex it.2.1, anchoredFinIndex it.2.2)) z
  | Sum.inr pri =>
    if pri.1 && (j == 0) then 0 else
      preconditionedPilotFeature (if pri.1 then j - 1 else j) x
        (if pri.2.1 then Sum.inr (Sum.inr (anchoredFinIndex pri.2.2))
          else Sum.inr (Sum.inl (anchoredFinIndex pri.2.2))) z

def dyadicIncrementRawVector {d ℓ : ℕ} (j : ℕ) (x : Covariate d) (z : Observation d) :
    Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ :=
  fun a => dyadicIncrementFeature j x ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) z

def dyadicIncrementRawMean {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ :=
  fun a => ∫ z, dyadicIncrementRawVector j x z a ∂observationLaw θ

theorem dyadicAnchoredFeature_joint_measurable {d ℓ : ℕ} (j : ℕ) (γ : AnchoredIndex d ℓ) :
    Measurable (fun z : Covariate d × Covariate d => dyadicAnchoredFeature j z.1 z.2 γ) :=
  ((anchoredMonomial_continuous γ).comp (continuous_pi fun i =>
    continuous_const.mul (((continuous_apply i).comp continuous_snd).sub
      ((continuous_apply i).comp continuous_fst)))).measurable

private theorem dyadicKnownGram_inverse_measurable {d ℓ : ℕ} (j : ℕ) :
    Measurable (fun x : Covariate d => (dyadicKnownGram (ℓ := ℓ) j x)⁻¹) := by
  have hinv : Measurable (fun A : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ => A⁻¹) := by
    apply Measurable.of_eval_matrix
    intro i k
    have hd : Measurable fun A : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ => A.det :=
      continuous_id.matrix_det.measurable
    have ha : Measurable fun A : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ => A.adjugate i k :=
      continuous_id.matrix_adjugate.measurable.eval_matrix
    convert hd.inv.mul ha using 1
    funext A; rw [Matrix.inv_def, Ring.inverse_eq_inv]; rfl
  have hanc : Measurable (dyadicNormalizedAnchor (d := d) j) :=
    measurable_pi_iff.mpr fun i => measurable_const.mul ((measurable_pi_apply i).sub
      ((measurable_of_countable fun c : Fin d → Fin ((2 : ℕ) ^ j) => regularGridCorner ((2 : ℕ) ^ j) c i).comp
        (regular_grid_cell_measurable _ (by positivity))))
  rw [show dyadicKnownGram (d := d) (ℓ := ℓ) j = anchoredGram ∘ dyadicNormalizedAnchor j from
    funext (dyadicKnownGram_eq_normalized j)]
  exact hinv.comp (anchoredGram_continuous.measurable.comp hanc)

private theorem preconditionedPilotFeature_joint_measurable {d ℓ : ℕ} (j : ℕ) (a : LocalPilotIndex d ℓ) :
    Measurable (fun v : Covariate d × Observation d => preconditionedPilotFeature j v.1 a v.2) := by
  have hpair : Measurable (fun v : Covariate d × Observation d => (v.1, v.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hsc (b : LocalPilotIndex d ℓ) : Measurable (fun v : Covariate d × Observation d => dyadicPilotScalar j v.1 b v.2) := by
    have hφ (γ : AnchoredIndex d ℓ) := (dyadicAnchoredFeature_joint_measurable j γ).comp hpair
    rcases b with ⟨γ, δ⟩ | (γ | γ)
    · exact (hφ γ).mul (hφ δ)
    · exact (measurable_snd.comp measurable_snd).mul (hφ γ)
    · exact hφ γ
  let S := {v : Covariate d × Observation d | v.2.1 ∈ dyadicPilotCell j v.1}
  have hS : MeasurableSet S :=
    (measurableSet_eq_fun ((regular_grid_cell_measurable _ (by positivity)).comp measurable_snd)
      ((regular_grid_cell_measurable _ (by positivity)).comp measurable_fst)).preimage hpair
  have hfeat (b : LocalPilotIndex d ℓ) : Measurable (fun v : Covariate d × Observation d => dyadicPilotFeature j v.1 b v.2) := by
    have h : Measurable fun v : Covariate d × Observation d => dyadicPilotScale d j * S.indicator (fun v => dyadicPilotScalar j v.1 b v.2) v :=
      measurable_const.mul ((hsc b).indicator hS)
    convert h using 1
    funext v; by_cases hv : v.2.1 ∈ dyadicPilotCell j v.1 <;> simp [dyadicPilotFeature, S, hv]
  exact Finset.measurable_sum Finset.univ fun β _ =>
    (((dyadicKnownGram_inverse_measurable j).eval_matrix (i := localPilotRow a) (j := β)).comp measurable_fst).mul
      (hfeat (localPilotReplaceRow a β))

private theorem dyadicIncrementFeature_joint_measurable {d ℓ : ℕ} (j : ℕ)
    (a : incrementVariables (anchoredDimension d ℓ)) :
    Measurable (fun v : Covariate d × Observation d => dyadicIncrementFeature j v.1 a v.2) := by
  rcases a with (it | it) | ⟨parent, response, i⟩
  · exact preconditionedPilotFeature_joint_measurable j _
  · change Measurable (fun v : Covariate d × Observation d => if j = 0 then
      (if it.2.1 = it.2.2 then (1 : ℝ) else 0) else
      preconditionedPilotFeature (j - 1) v.1 (Sum.inl (anchoredFinIndex it.2.1, anchoredFinIndex it.2.2)) v.2)
    split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_joint_measurable _ _
  · change Measurable (fun v : Covariate d × Observation d => if parent && (j == 0) then (0 : ℝ) else
      preconditionedPilotFeature (if parent then j - 1 else j) v.1
        (if response then Sum.inr (Sum.inr (anchoredFinIndex i)) else Sum.inr (Sum.inl (anchoredFinIndex i))) v.2)
    split_ifs <;> first | exact measurable_const | exact preconditionedPilotFeature_joint_measurable _ _

theorem dyadicIncrementRawVector_joint_measurable {d ℓ : ℕ} (j : ℕ) :
    Measurable (fun v : Covariate d × Observation d => dyadicIncrementRawVector (ℓ := ℓ) j v.1 v.2) :=
  measurable_pi_iff.mpr fun _ => dyadicIncrementFeature_joint_measurable j _

theorem dyadicIncrementRawMean_measurable {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) :
    Measurable (dyadicIncrementRawMean (ℓ := ℓ) θ j) := by
  let _ := observationLaw_isProbability C θ hθ
  exact measurable_pi_iff.mpr fun a =>
    (((dyadicIncrementRawVector_joint_measurable (ℓ := ℓ) j).eval (a := a)).stronglyMeasurable.integral_prod_right'
      (ν := observationLaw θ)).measurable

private theorem sampleLaw_vector_facts {d p n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (f : Observation d → Fin p → ℝ) (hm : Measurable f)
    (hL2 : ∀ a, MemLp (fun z => f z a) 2 (observationLaw θ)) :
    iIndepFun (fun i (z : Fin n → Observation d) => f (z i)) (sampleLaw θ n) ∧
    (∀ i : Fin n, Measurable (fun z : Fin n → Observation d => f (z i))) ∧
    (∀ i t : Fin n, IdentDistrib
      (fun z : Fin n → Observation d => f (z i))
      (fun z : Fin n → Observation d => f (z t)) (sampleLaw θ n) (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, MemLp (fun z : Fin n → Observation d => f (z i) a) 2 (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, (∫ z : Fin n → Observation d, f (z i) a ∂sampleLaw θ n) = ∫ z, f z a ∂observationLaw θ) := by
  let _ := observationLaw_isProbability C θ hθ
  have hp (i : Fin n) : MeasurePreserving (fun z : Fin n → Observation d => z i) (sampleLaw θ n) (observationLaw θ) :=
    measurePreserving_eval _ i
  refine ⟨iIndepFun_pi (fun _ : Fin n => hm.aemeasurable),
    fun i => hm.comp (measurable_pi_apply i),
    fun i t => (IdentDistrib.mk (hp i).aemeasurable (hp t).aemeasurable ((hp i).map_eq.trans (hp t).map_eq.symm)).comp hm,
    fun i a => (hL2 a).comp_measurePreserving (hp i),
    fun i a => integral_comp_eval (μ := fun _ : Fin n => observationLaw θ) (i := i) ((hm.eval (a := a)).aestronglyMeasurable)⟩

private theorem dyadicIncrementRawVector_measurable {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    Measurable (dyadicIncrementRawVector (ℓ := ℓ) j x) :=
  measurable_pi_iff.mpr fun a => by
    change Measurable fun z : Observation d => dyadicIncrementFeature j x _ z
    generalize (Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a = v
    rcases v with (it | it) | ⟨parent, response, idx⟩
    · exact preconditionedPilotFeature_measurable j x _
    · by_cases hj : j = 0
      · by_cases hit : it.2.1 = it.2.2 <;> simpa [dyadicIncrementFeature, hj, hit] using measurable_const
      · simpa [dyadicIncrementFeature, hj] using preconditionedPilotFeature_measurable (j - 1) x _
    · cases parent with
      | false =>
        cases response <;> simpa [dyadicIncrementFeature] using preconditionedPilotFeature_measurable j x _
      | true =>
        by_cases hj : j = 0
        · simpa [dyadicIncrementFeature, hj] using measurable_const
        · cases response <;> simpa [dyadicIncrementFeature, hj] using preconditionedPilotFeature_measurable (j - 1) x _

private theorem dyadicIncrementFeature_memLp_and_second {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (v : incrementVariables (anchoredDimension d ℓ)) :
    MemLp (dyadicIncrementFeature j x v) 2 (observationLaw θ) ∧
      (∫ z, dyadicIncrementFeature j x v z ^ 2 ∂observationLaw θ) ≤
        preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
  let _ := observationLaw_isProbability C θ hθ
  have hC := preconditionedPilotMomentConstant_pos C ℓ
  have hroot : 1 ≤ preconditionedPilotMomentConstant C ℓ := le_max_left _ _
  have hK : 1 ≤ dyadicPilotScale d j := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hnon : 0 ≤ preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j :=
    mul_nonneg hC.le (dyadicPilotScale_pos d j).le
  have hpar_sc : dyadicPilotScale d (j - 1) ≤ dyadicPilotScale d j :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.sub_le j 1)) d
  have hpar (a : LocalPilotIndex d ℓ) :=
    (preconditionedPilotFeature_uniform_second_le C θ hθ (j - 1) x hx a).trans
      (mul_le_mul_of_nonneg_left hpar_sc hC.le)
  constructor
  · change MemLp (fun z : Observation d => dyadicIncrementFeature j x v z) 2 (observationLaw θ)
    rcases v with (it | it) | ⟨parent, response, i⟩
    · exact preconditionedPilotFeature_memLp_two C θ hθ j x hx _
    · by_cases hj : j = 0
      · by_cases hit : it.2.1 = it.2.2 <;> simpa [dyadicIncrementFeature, hj, hit] using memLp_const _
      · simpa [dyadicIncrementFeature, hj] using preconditionedPilotFeature_memLp_two C θ hθ (j - 1) x hx _
    · cases parent with
      | false =>
        cases response <;> simpa [dyadicIncrementFeature] using preconditionedPilotFeature_memLp_two C θ hθ j x hx _
      | true =>
        by_cases hj : j = 0
        · simpa [dyadicIncrementFeature, hj] using memLp_const _
        · cases response <;> simpa [dyadicIncrementFeature, hj] using preconditionedPilotFeature_memLp_two C θ hθ (j - 1) x hx _
  · rcases v with (it | it) | ⟨parent, response, i⟩
    · exact preconditionedPilotFeature_uniform_second_le C θ hθ j x hx _
    · by_cases hj : j = 0
      · by_cases hit : it.2.1 = it.2.2
        · simpa [dyadicIncrementFeature, hj, hit] using mul_le_mul hroot hK zero_le_one hC.le
        · simpa [dyadicIncrementFeature, hj, hit] using hnon
      · simpa [dyadicIncrementFeature, hj] using hpar _
    · cases parent with
      | false =>
        cases response <;> simpa [dyadicIncrementFeature] using preconditionedPilotFeature_uniform_second_le C θ hθ j x hx _
      | true =>
        by_cases hj : j = 0
        · simpa [dyadicIncrementFeature, hj] using hnon
        · cases response <;> simpa [dyadicIncrementFeature, hj] using hpar _

theorem dyadicIncrementRawVector_sample_facts {d ℓ n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) :
    iIndepFun (fun i (z : Fin n → Observation d) => dyadicIncrementRawVector (ℓ := ℓ) j x (z i)) (sampleLaw θ n) ∧
    (∀ i : Fin n, Measurable (fun z : Fin n → Observation d => dyadicIncrementRawVector (ℓ := ℓ) j x (z i))) ∧
    (∀ i t : Fin n, IdentDistrib
      (fun z : Fin n → Observation d => dyadicIncrementRawVector (ℓ := ℓ) j x (z i))
      (fun z : Fin n → Observation d => dyadicIncrementRawVector (ℓ := ℓ) j x (z t)) (sampleLaw θ n) (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, MemLp (fun z : Fin n → Observation d => dyadicIncrementRawVector (ℓ := ℓ) j x (z i) a)
      2 (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, (∫ z : Fin n → Observation d, dyadicIncrementRawVector (ℓ := ℓ) j x (z i) a ∂sampleLaw θ n) =
      dyadicIncrementRawMean θ j x a) :=
  sampleLaw_vector_facts C θ hθ (dyadicIncrementRawVector j x) (dyadicIncrementRawVector_measurable j x)
    fun _ => (dyadicIncrementFeature_memLp_and_second C θ hθ j x hx _).1

theorem dyadicIncrementRawVector_sample_second_le {d ℓ n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) (i : Fin n) :
    (∫ z : Fin n → Observation d, ‖dyadicIncrementRawVector (ℓ := ℓ) j x (z i)‖ ^ 2 ∂sampleLaw θ n) ≤
      Fintype.card (incrementVariables (anchoredDimension d ℓ)) *
        preconditionedPilotMomentConstant C ℓ * dyadicPilotScale d j := by
  let _ := observationLaw_isProbability C θ hθ
  have hm := dyadicIncrementRawVector_measurable (ℓ := ℓ) j x
  unfold sampleLaw
  rw [integral_comp_eval (μ := fun _ : Fin n => observationLaw θ) (i := i) ((hm.norm.pow_const 2).aestronglyMeasurable)]
  refine (KernelMomentBounds.vector_second_le_sum_coordinates (dyadicIncrementRawVector j x) hm
    fun _ => (dyadicIncrementFeature_memLp_and_second C θ hθ j x hx _).1).trans ?_
  exact (Finset.sum_le_sum fun _ _ => (dyadicIncrementFeature_memLp_and_second C θ hθ j x hx _).2).trans_eq (by simp [mul_assoc])

def dyadicFinPilotGram {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ :=
  anchoredFinReindex d ℓ (dyadicPreconditionedGram θ j x)

def dyadicFinPilotMoments {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    Bool → Fin (anchoredDimension d ℓ) → ℝ :=
  fun response i => preconditionedPilotPopulation θ j x
    (if response then Sum.inr (Sum.inr (anchoredFinIndex i)) else Sum.inr (Sum.inl (anchoredFinIndex i)))

def dyadicIncrementPopulation {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    incrementVariables (anchoredDimension d ℓ) → ℝ :=
  incrementValuation (dyadicFinPilotGram θ j x)
    (if j = 0 then 1 else dyadicFinPilotGram θ (j - 1) x)
    (dyadicFinPilotMoments θ j x)
    (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)

theorem dyadicIncrementRawMean_eq_population {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) :
    dyadicIncrementRawMean (ℓ := ℓ) θ j x = fun a =>
      dyadicIncrementPopulation θ j x ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a) := by
  let _ := observationLaw_isProbability C θ hθ
  funext a
  change (∫ z, dyadicIncrementFeature j x _ z ∂observationLaw θ) = _
  generalize (Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a = v
  rcases v with (⟨i, t⟩ | it) | ⟨parent, response, i⟩
  · simpa [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation, parentValuation,
      dyadicFinPilotGram, anchoredFinReindex, Matrix.reindexAlgEquiv, Matrix.reindex, anchoredFinIndex,
      preconditionedPilotPopulation] using
      preconditionedPilotPopulation_gram C θ hθ j x hx (anchoredFinIndex i) (anchoredFinIndex t)
  · by_cases hj : j = 0
    · simp [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation, parentValuation, hj, Matrix.one_apply]
    · simpa [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation, parentValuation,
        dyadicFinPilotGram, anchoredFinReindex, Matrix.reindexAlgEquiv, Matrix.reindex, anchoredFinIndex, hj,
        preconditionedPilotPopulation] using
        preconditionedPilotPopulation_gram C θ hθ (j - 1) x hx (anchoredFinIndex it.2.1) (anchoredFinIndex it.2.2)
  · cases parent <;> cases response <;> by_cases hj : j = 0
    all_goals simp [dyadicIncrementFeature, dyadicIncrementPopulation, incrementValuation,
      dyadicFinPilotMoments, hj, preconditionedPilotPopulation]

theorem dyadicFinPilotGram_eq_normalized {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    dyadicFinPilotGram (ℓ := ℓ) θ j x =
      anchoredFinNormalizedGram (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) := by
  unfold dyadicFinPilotGram dyadicPreconditionedGram anchoredFinNormalizedGram
  rw [dyadicKnownGram_eq_normalized, dyadicPopulationGram_eq_normalized C θ hθ]

theorem dyadicFinPilotMoments_eq_anchored {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d)
    (hx : x ∈ unitCube d) :
    dyadicFinPilotMoments (ℓ := ℓ) θ j x = anchoredFinMomentFamilies
      (dyadicNormalizedAnchor j x) (dyadicNormalizedDensity θ j x) (θ.regression ∘ dyadicCellAffine j x) := by
  funext t i
  cases t
  · exact preconditionedPilotPopulation_response C θ hθ j x hx _
  · exact preconditionedPilotPopulation_constant C θ hθ j x hx _

def dyadicPilotSeries {d : ℕ} (C : ModelConstants d) (A Λ : ℝ) (j m : ℕ) : ℝ :=
  ∑ k : Fin (m + anchoredDimension d C.order + 1),
    ((k.val + 1).factorial : ℝ) *
      (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d C.order)) *
        preconditionedPilotMomentConstant C C.order * dyadicPilotScale d j) / Λ) ^ (k.val + 1)

theorem dyadicPilotSeries_nonneg {d : ℕ} (C : ModelConstants d) (A Λ : ℝ)
    (hΛ : 0 ≤ Λ) (j m : ℕ) : 0 ≤ dyadicPilotSeries C A Λ j m := by
  have := preconditionedPilotMomentConstant_pos C C.order
  have := dyadicPilotScale_pos d j
  unfold dyadicPilotSeries; positivity

def dyadicSeriesEnvelope {d : ℕ} (C : ModelConstants d) (A Λ : ℝ) (J : ℕ) (m : ℕ → ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j : Fin (J + 1) =>
    dyadicPilotSeries C A Λ j.val (m j.val) * max 1 (Λ / dyadicPilotScale d j.val)

theorem dyadicSeriesEnvelope_nonneg {d : ℕ} (C : ModelConstants d) (A Λ : ℝ)
    (hΛ : 0 ≤ Λ) (J : ℕ) (m : ℕ → ℕ) : 0 ≤ dyadicSeriesEnvelope C A Λ J m :=
  (mul_nonneg (dyadicPilotSeries_nonneg C A Λ hΛ 0 (m 0)) (zero_le_one.trans (le_max_left _ _))).trans
    (Finset.le_sup' (fun j : Fin (J + 1) => dyadicPilotSeries C A Λ j.val (m j.val) * max 1 (Λ / dyadicPilotScale d j.val))
      (Finset.mem_univ ⟨0, by omega⟩))

theorem dyadicPilotSeries_le_envelope {d : ℕ} (C : ModelConstants d) (A Λ : ℝ)
    (hΛ : 0 ≤ Λ) (J : ℕ) (m : ℕ → ℕ) (j : Fin (J + 1)) :
    dyadicPilotSeries C A Λ j.val (m j.val) ≤ dyadicSeriesEnvelope C A Λ J m :=
  (le_mul_of_one_le_right (dyadicPilotSeries_nonneg C A Λ hΛ j.val (m j.val)) (le_max_left _ _)).trans
    (Finset.le_sup' (fun i : Fin (J + 1) => dyadicPilotSeries C A Λ i.val (m i.val) * max 1 (Λ / dyadicPilotScale d i.val))
      (Finset.mem_univ j))

theorem dyadicPilotSeries_div_scale_le_envelope {d : ℕ} (C : ModelConstants d) (A Λ : ℝ)
    (hΛ : 0 < Λ) (J : ℕ) (m : ℕ → ℕ) (j : Fin (J + 1)) :
    dyadicPilotSeries C A Λ j.val (m j.val) / dyadicPilotScale d j.val ≤
      dyadicSeriesEnvelope C A Λ J m / Λ := by
  have h := (mul_le_mul_of_nonneg_left (le_max_right 1 (Λ / dyadicPilotScale d j.val))
    (dyadicPilotSeries_nonneg C A Λ hΛ.le j.val (m j.val))).trans
    (Finset.le_sup' (fun i : Fin (J + 1) => dyadicPilotSeries C A Λ i.val (m i.val) * max 1 (Λ / dyadicPilotScale d i.val))
      (Finset.mem_univ j))
  exact (le_div_iff₀ hΛ).mpr ((by ring : _ = dyadicPilotSeries C A Λ j.val (m j.val) * (Λ / dyadicPilotScale d j.val)).trans_le h)

theorem dyadicPilotScale_parent_ratio_le {d j : ℕ} :
    dyadicPilotScale d j ≤ (2 : ℝ) ^ d * dyadicPilotScale d (j - 1) := by
  cases j with
  | zero => simpa [dyadicPilotScale] using one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  | succ j => simp only [Nat.add_sub_cancel, dyadicPilotScale, pow_succ, mul_pow]; exact le_of_eq (by ring)

-- 4. Global increment coordinates & coordinate bounds

abbrev DyadicGlobalDimension (d ℓ j : ℕ) :=
  Fintype.card (PilotBasisIndex (Fintype.card (DyadicPilotLabelIndex d j)) d (2 * ℓ))

abbrev IncrementGlobalIndex (d ℓ j : ℕ) :=
  Unit ⊕ (Fin (DyadicGlobalDimension d ℓ j) ⊕ Fin (DyadicGlobalDimension d ℓ (j - 1)))

def incrementGlobalFeature {d ℓ : ℕ} (j : ℕ) (a : IncrementGlobalIndex d ℓ j) (z : Observation d) : ℝ :=
  match a with
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl i) => pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel j) z i
  | Sum.inr (Sum.inr i) => pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel (j - 1)) z i

def incrementGlobalVector {d ℓ : ℕ} (j : ℕ) (z : Observation d) :
    Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ :=
  fun a => incrementGlobalFeature j ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)).symm a) z

def incrementGlobalMean {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) :
    Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ :=
  fun a => ∫ z, incrementGlobalVector (ℓ := ℓ) j z a ∂observationLaw θ

private theorem incrementGlobalVector_measurable {d ℓ : ℕ} (j : ℕ) :
    Measurable (incrementGlobalVector (d := d) (ℓ := ℓ) j) :=
  measurable_pi_iff.mpr fun i => by
    change Measurable (incrementGlobalFeature j _)
    generalize (Fintype.equivFin (IncrementGlobalIndex d ℓ j)).symm i = a
    rcases a with _ | (idx | idx)
    · exact measurable_const
    · exact pilotBasisFeature_measurable _ (dyadicPilotLabel_measurable _) _
    · exact pilotBasisFeature_measurable _ (dyadicPilotLabel_measurable _) _

private theorem incrementGlobalFeature_memLp_two {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
    (a : IncrementGlobalIndex d ℓ j) : MemLp (incrementGlobalFeature j a) 2 (observationLaw θ) := by
  let _ := observationLaw_isProbability C θ hθ
  rcases a with _ | (i | i)
  · exact memLp_const _
  · exact pilotBasisFeature_memLp_two C θ hθ _ (dyadicPilotLabel_measurable _) _
  · exact pilotBasisFeature_memLp_two C θ hθ _ (dyadicPilotLabel_measurable _) _

theorem incrementGlobalVector_sample_facts {d ℓ n : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) :
    iIndepFun (fun i (z : Fin n → Observation d) => incrementGlobalVector (ℓ := ℓ) j (z i)) (sampleLaw θ n) ∧
    (∀ i : Fin n, Measurable (fun z : Fin n → Observation d => incrementGlobalVector (ℓ := ℓ) j (z i))) ∧
    (∀ i t : Fin n, IdentDistrib
      (fun z : Fin n → Observation d => incrementGlobalVector (ℓ := ℓ) j (z i))
      (fun z : Fin n → Observation d => incrementGlobalVector (ℓ := ℓ) j (z t)) (sampleLaw θ n) (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, MemLp (fun z : Fin n → Observation d => incrementGlobalVector (ℓ := ℓ) j (z i) a)
      2 (sampleLaw θ n)) ∧
    (∀ (i : Fin n) a, (∫ z : Fin n → Observation d, incrementGlobalVector (ℓ := ℓ) j (z i) a ∂sampleLaw θ n) =
      incrementGlobalMean θ j a) :=
  sampleLaw_vector_facts C θ hθ (incrementGlobalVector j) (incrementGlobalVector_measurable j)
    fun _ => incrementGlobalFeature_memLp_two C θ hθ j _

def incrementGlobalCurrent {d ℓ : ℕ} (j : ℕ) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] (Fin (DyadicGlobalDimension d ℓ j) → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj
    ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)) (Sum.inr (Sum.inl i)))

def incrementGlobalParent {d ℓ : ℕ} (j : ℕ) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] (Fin (DyadicGlobalDimension d ℓ (j - 1)) → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj
    ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)) (Sum.inr (Sum.inr i)))

def incrementGlobalOne {d ℓ : ℕ} (j : ℕ) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj ((Fintype.equivFin (IncrementGlobalIndex d ℓ j)) (Sum.inl ()))

def preconditionedPilotCoordinate {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
    (a : LocalPilotIndex d ℓ) : (Fin (DyadicGlobalDimension d ℓ j) → ℝ) →L[ℝ] ℝ :=
  ∑ β : AnchoredIndex d ℓ, (dyadicKnownGram j x)⁻¹ (localPilotRow a) β •
    dyadicPilotCoordinate j x (localPilotReplaceRow a β)

def incrementPilotFreeCoordinate {d ℓ : ℕ} (j : ℕ) (x : Covariate d)
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

def incrementPilotCoordinate {d ℓ : ℕ} (j : ℕ) (x : Covariate d) :
    (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ]
      (Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) :=
  ContinuousLinearMap.pi fun a => incrementPilotFreeCoordinate j x
    ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a)

@[simp] private theorem incrementPilotCoordinate_raw {d ℓ : ℕ} (j : ℕ) (x : Covariate d) (z : Observation d) :
    incrementPilotCoordinate j x (incrementGlobalVector j z) = dyadicIncrementRawVector (ℓ := ℓ) j x z := by
  have hcur : incrementGlobalCurrent (ℓ := ℓ) j (incrementGlobalVector j z) = pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel j) z := by
    funext i; simp [incrementGlobalCurrent, incrementGlobalVector, incrementGlobalFeature]
  have hpar : incrementGlobalParent (ℓ := ℓ) j (incrementGlobalVector j z) = pilotRawVector (ℓ := 2 * ℓ) (dyadicPilotLabel (j - 1)) z := by
    funext i; simp [incrementGlobalParent, incrementGlobalVector, incrementGlobalFeature]
  have hone : incrementGlobalOne (ℓ := ℓ) j (incrementGlobalVector j z) = 1 := by
    simp [incrementGlobalOne, incrementGlobalVector, incrementGlobalFeature]
  have hprec (k : ℕ) (b : LocalPilotIndex d ℓ) :
      preconditionedPilotCoordinate k x b (pilotRawVector (dyadicPilotLabel k) z) = preconditionedPilotFeature k x b z := by
    simp [preconditionedPilotCoordinate, preconditionedPilotFeature, smul_eq_mul, dyadicPilotCoordinate_raw_apply]
  funext a
  change incrementPilotFreeCoordinate j x _ (incrementGlobalVector j z) = dyadicIncrementFeature j x _ z
  generalize (Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm a = v
  rcases v with (⟨i, t⟩ | it) | ⟨parent, response, i⟩
  · simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hcur, hprec]
  · by_cases hj : j = 0
    · by_cases hit : it.2.1 = it.2.2 <;> simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj, hit, hone]
    · simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj, hpar, hprec]
  · cases parent <;> cases response <;> by_cases hj : j = 0
    all_goals simp [incrementPilotFreeCoordinate, dyadicIncrementFeature, hj, hcur, hpar, hprec]

private theorem incrementPilotCoordinate_mean {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) :
    incrementPilotCoordinate (ℓ := ℓ) j x (incrementGlobalMean θ j) = dyadicIncrementRawMean θ j x := by
  let _ := observationLaw_isProbability C θ hθ
  have hlp := KernelMomentBounds.vector_memLp_two (incrementGlobalVector (ℓ := ℓ) j)
    (incrementGlobalVector_measurable j) fun _ => incrementGlobalFeature_memLp_two C θ hθ j _
  have hi := hlp.integrable (by norm_num)
  have hm : (∫ z, incrementGlobalVector (ℓ := ℓ) j z ∂observationLaw θ) = incrementGlobalMean θ j :=
    funext fun a => ((ContinuousLinearMap.proj a :
      (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ).integral_comp_comm hi).symm
  rw [← hm, ← (incrementPilotCoordinate (ℓ := ℓ) j x).integral_comp_comm hi]
  simp only [incrementPilotCoordinate_raw]
  funext a
  simpa only [ContinuousLinearMap.proj_apply, incrementPilotCoordinate_raw, dyadicIncrementRawMean] using
    ((ContinuousLinearMap.proj a :
      (Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) → ℝ) →L[ℝ] ℝ).integral_comp_comm
      ((incrementPilotCoordinate (ℓ := ℓ) j x).integrable_comp hi)).symm

private theorem incrementPilotCoordinate_measurable {d ℓ : ℕ} (j : ℕ) :
    Measurable (incrementPilotCoordinate (d := d) (ℓ := ℓ) j) := by
  have hprec_meas (k : ℕ) (b : LocalPilotIndex d ℓ) :
      Measurable (fun x : Covariate d => preconditionedPilotCoordinate k x b) := by
    refine Finset.measurable_sum Finset.univ fun β _ =>
      ((dyadicKnownGram_inverse_measurable k).eval_matrix (i := localPilotRow b) (j := β)).smul ?_
    refine (measurable_const : Measurable fun _ : Covariate d => dyadicPilotScale d k).smul ?_
    exact Finset.measurable_sum _ fun γ _ => (dyadicPilotPolynomial_coeff_continuous k _ _).measurable.smul
      ((measurable_of_countable fun c : Fin (Fintype.card (DyadicPilotLabelIndex d k)) =>
        (ContinuousLinearMap.proj ((Fintype.equivFin (PilotBasisIndex (Fintype.card (DyadicPilotLabelIndex d k)) d (2 * ℓ)))
          ((c, γ), dyadicPilotResponse _)) : (Fin (DyadicGlobalDimension d ℓ k) → ℝ) →L[ℝ] ℝ)).comp (dyadicPilotLabel_measurable k))
  let pc : ((Fin (DyadicGlobalDimension d ℓ j) → ℝ) →L[ℝ] ℝ) →L[ℝ]
      ((Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ (incrementGlobalCurrent j)
  let pp : ((Fin (DyadicGlobalDimension d ℓ (j - 1)) → ℝ) →L[ℝ] ℝ) →L[ℝ]
      ((Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.precomp ℝ (incrementGlobalParent j)
  refine (ContinuousLinearMap.piEquivL ℝ (Fin (Fintype.card (IncrementGlobalIndex d ℓ j)) → ℝ)
    (fun _ : Fin (Fintype.card (incrementVariables (anchoredDimension d ℓ))) => ℝ)).continuous.measurable.comp
    (measurable_pi_iff.mpr fun i => ?_)
  generalize (Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm i = a
  rcases a with (it | it) | ⟨parent, response, idx⟩
  · exact pc.measurable.comp (hprec_meas j _)
  · change Measurable (fun x : Covariate d => if j = 0 then (if it.2.1 = it.2.2 then incrementGlobalOne j else 0) else _)
    split_ifs
    · exact measurable_const
    · exact measurable_const
    · exact pp.measurable.comp (hprec_meas (j - 1) _)
  · simp only [incrementPilotFreeCoordinate]
    split_ifs
    · exact measurable_const
    · exact pp.measurable.comp (hprec_meas (j - 1) _)
    · exact pp.measurable.comp (hprec_meas (j - 1) _)
    · exact pc.measurable.comp (hprec_meas j _)
    · exact pc.measurable.comp (hprec_meas j _)

private theorem real_pi_projection_norm_le {ι : Type*} [Fintype ι] (i : ι) :
    ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simpa using norm_le_pi_norm v i

private theorem incrementPilotCoordinate_uniform_bound {d ℓ : ℕ} (j : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ‖incrementPilotCoordinate (ℓ := ℓ) j x‖ ≤ M := by
  have hlin_bd {q k : ℕ} (c : Fin q) (P : MvPolynomial (Fin d) ℝ) (resp : Bool) (M0 : ℝ) (hM0 : 0 ≤ M0)
      (hP : ∀ γ : PolynomialBox d k, |P.coeff (polynomialBoxExponent γ)| ≤ M0) :
      ‖pilotPolynomialLinear (ℓ := k) c P resp‖ ≤ (Fintype.card (PolynomialBox d k) : ℝ) * M0 := by
    refine ((norm_sum_le _ _).trans (Finset.sum_le_sum (g := fun _ => M0) fun γ _ => ?_)).trans_eq (by simp)
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul (hP γ) (real_pi_projection_norm_le _) (norm_nonneg _) hM0).trans_eq (mul_one M0)
  have hprec_bd (k : ℕ) : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ unitCube d, ∀ a : LocalPilotIndex d ℓ,
      ‖preconditionedPilotCoordinate k x a‖ ≤ M := by
    obtain ⟨L, hL, hLb⟩ := dyadicKnownGram_inverse_uniform_bound (d := d) (ℓ := ℓ)
    obtain ⟨P, hP, hPb⟩ := dyadicPilotPolynomial_coeff_uniform_bound (d := d) (ℓ := ℓ) k
    let C_coord := dyadicPilotScale d k * ((Fintype.card (PolynomialBox d (2 * ℓ)) : ℝ) * P)
    let B := (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (L * C_coord)
    refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), fun x hx a => ?_⟩
    letI : Nonempty (AnchoredIndex d ℓ) := ⟨localPilotRow a⟩
    refine ((norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ => L * C_coord) fun β _ => ?_).trans_eq (by simp [B]))).trans (le_max_right _ _)
    rw [norm_smul]
    refine mul_le_mul ((matrix_real_entry_norm_le _ _ _).trans (hLb k x hx)) ?_ (norm_nonneg _) hL.le
    rw [dyadicPilotCoordinate, norm_smul, Real.norm_eq_abs, abs_of_nonneg (dyadicPilotScale_pos d k).le]
    exact mul_le_mul_of_nonneg_left (hlin_bd _ _ _ P hP.le (hPb x hx _)) (dyadicPilotScale_pos d k).le
  obtain ⟨C0, hC0, hCb⟩ := hprec_bd j
  obtain ⟨P0, hP0, hPb⟩ := hprec_bd (j - 1)
  let M := max 1 (max C0 P0)
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨M, hM, fun x hx => ContinuousLinearMap.norm_pi_le_of_le (fun i => ?_) hM.le⟩
  have hcur_n : ‖incrementGlobalCurrent (d := d) (ℓ := ℓ) j‖ ≤ 1 :=
    ContinuousLinearMap.norm_pi_le_of_le (fun _ => real_pi_projection_norm_le _) zero_le_one
  have hpar_n : ‖incrementGlobalParent (d := d) (ℓ := ℓ) j‖ ≤ 1 :=
    ContinuousLinearMap.norm_pi_le_of_le (fun _ => real_pi_projection_norm_le _) zero_le_one
  have hc (a : LocalPilotIndex d ℓ) : ‖(preconditionedPilotCoordinate j x a).comp (incrementGlobalCurrent j)‖ ≤ M :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (((mul_le_mul (hCb x hx a) hcur_n (norm_nonneg _) hC0.le).trans_eq (mul_one _)).trans
        ((le_max_left C0 P0).trans (le_max_right 1 _)))
  have hp (a : LocalPilotIndex d ℓ) : ‖(preconditionedPilotCoordinate (j - 1) x a).comp (incrementGlobalParent j)‖ ≤ M :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (((mul_le_mul (hPb x hx a) hpar_n (norm_nonneg _) hP0.le).trans_eq (mul_one _)).trans
        ((le_max_right C0 P0).trans (le_max_right 1 _)))
  change ‖incrementPilotFreeCoordinate j x _‖ ≤ M
  generalize (Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm i = a
  rcases a with (it | it) | ⟨parent, response, idx⟩
  · exact hc _
  · simp only [incrementPilotFreeCoordinate]
    split_ifs
    · exact (real_pi_projection_norm_le _).trans (le_max_left _ _)
    · simpa using hM.le
    · exact hp _
  · simp only [incrementPilotFreeCoordinate]
    split_ifs
    · simpa using hM.le
    · exact hp _
    · exact hp _
    · exact hc _
    · exact hc _

-- 5. Pointwise polynomial pilot, parent-block localization & increment kernels

def rowIncrementPolynomial (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (row : Fin r → ℝ) : MvPolynomial (Fin (Fintype.card (incrementVariables r))) ℝ :=
  ∑ i, C (row i) * incrementFinPolynomial r a b T y m i

theorem rowIncrementPolynomial_eval (r : ℕ) (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (row : Fin r → ℝ) (z : Fin (Fintype.card (incrementVariables r)) → ℝ) :
    eval z (rowIncrementPolynomial r a b T y m row) = incrementFinScalar r a b T y m row z := by
  simp [rowIncrementPolynomial, incrementFinScalar, incrementFinVector, dotProduct]

theorem rowIncrementPolynomial_degree (r : ℕ) [NeZero r] (a b : ℝ)
    (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (row : Fin r → ℝ) :
    (rowIncrementPolynomial r a b T y m row).totalDegree ≤ m + r + 1 :=
  totalDegree_finsetSum_le fun i _ => (totalDegree_mul _ _).trans
    (by simpa only [totalDegree_C, zero_add, incrementFinPolynomial] using
      (totalDegree_rename_le _ _).trans (incrementEntryPolynomial_degree r a b T y m i))

theorem anchoredFinNormalizedGram_one {d ℓ : ℕ} (u : Covariate d) :
    anchoredFinNormalizedGram (ℓ := ℓ) u (fun _ => 1) = 1 := by
  have hG : anchoredDensityGram (ℓ := ℓ) u (fun _ => 1) = anchoredGram u := by
    ext γ δ; simp [anchoredDensityGram, anchoredGram]
  unfold anchoredFinNormalizedGram
  rw [hG, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_posDef u).isUnit)]
  exact map_one _

def dyadicPolynomialPilot {d : ℕ} (C : ModelConstants d) (n j : ℕ) (x : Covariate d)
    (y : ℝ) (m : ℕ) (row : Fin (anchoredDimension d C.order) → ℝ) (z : Fin n → Observation d) : ℝ :=
  RoughRegime.Upper.polynomialLift
    (rowIncrementPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
      (anchoredFinTransport d C.order) y m row)
    (fun i z => dyadicIncrementRawVector j x (z i)) z

theorem dyadicPolynomialPilot_moment_facts {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n j : ℕ) (x : Covariate d) (hx : x ∈ unitCube d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (dyadicPolynomialPilot C n j x y m row) 2 (sampleLaw θ n) ∧
    (∫ z, dyadicPolynomialPilot C n j x y m row z ∂sampleLaw θ n) =
      incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
        (anchoredFinTransport d C.order) y m row (dyadicIncrementRawMean θ j x) := by
  let _ := sampleLaw_isProbability C θ hθ n
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := dyadicIncrementRawVector_sample_facts C θ hθ j x hx
  refine ⟨LiftL2.polynomialLift_memLp_two_l2 _ _ (dyadicIncrementRawMean θ j x)
    (rowIncrementPolynomial_degree ..) hdegree hind hmeas hL2, ?_⟩
  rw [← rowIncrementPolynomial_eval]
  exact LiftL2.polynomialLift_expectation_l2 _ _ (dyadicIncrementRawMean θ j x)
    (rowIncrementPolynomial_degree ..) hdegree hind hmeas hid hL2 hmean

theorem regularPairDesignMeasure_parent_block_mass {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k) (j : ℕ)
    (c : Fin d → Fin ((2 : ℕ) ^ (j - 1))) :
    (regularPairDesignMeasure θ k hk).real
      {w : Covariate d × Covariate d | regularGridCell ((2 : ℕ) ^ (j - 1)) (by positivity) w.1 = c} ≤
        C.densityUpper ^ 2 / dyadicPilotScale d (j - 1) := by
  let _ := cubeVolume_isProbability d
  let A : Set (Covariate d) := (regularGridCell ((2 : ℕ) ^ (j - 1)) (by positivity)) ⁻¹' {c}
  have hA : MeasurableSet A := (measurableSet_singleton c).preimage (regular_grid_cell_measurable _ _)
  have hmap := regularPairDesignMeasure_fst_cube_le C θ hθ k hk
  have hfirst : (regularPairDesignMeasure θ k hk).real (Prod.fst ⁻¹' A) ≤
      C.densityUpper ^ 2 * (cubeVolume d).real A := by
    rw [← map_measureReal_apply measurable_fst hA]
    have ht := ENNReal.toReal_mono
      (show (ENNReal.ofReal (C.densityUpper ^ 2) • cubeVolume d) A ≠ ⊤ from
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (cubeVolume d) A)) (hmap A)
    simpa only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg _)] using ht
  have hvol : (cubeVolume d).real A ≤ (1 / ((2 : ℝ) ^ (j - 1))) ^ d := by
    have ht := ENNReal.toReal_mono
      (by finiteness : ENNReal.ofReal (1 / (((2 : ℕ) ^ (j - 1) : ℕ) : ℝ)) ^ d ≠ ⊤)
      (regular_grid_fiber_volume_le ((2 : ℕ) ^ (j - 1)) (by positivity) c)
    simpa [measureReal_def, A, ENNReal.toReal_pow, Nat.cast_pow,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (((2 : ℕ) ^ (j - 1) : ℕ) : ℝ))] using ht
  exact hfirst.trans ((mul_le_mul_of_nonneg_left hvol (sq_nonneg _)).trans_eq
    (by simp [dyadicPilotScale, div_pow, div_eq_mul_inv]))

def dyadicIncrementKernel {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ) (k : ℕ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin k => Fin (Fintype.card (IncrementGlobalIndex d C.order j)) → ℝ) ℝ :=
  (iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
    C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
      (dyadicIncrementRawMean θ j x)).compContinuousLinearMap fun _ => incrementPilotCoordinate j x

theorem dyadicIncrementKernel_raw {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ) (k : ℕ) (z : Fin k → Observation d) :
    dyadicIncrementKernel C θ j x y m row k (fun i => incrementGlobalVector j (z i)) =
      iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
        (dyadicIncrementRawMean θ j x) (fun i => dyadicIncrementRawVector j x (z i)) := by
  simp [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply]

theorem dyadicIncrementKernel_symmetric {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ) (k : ℕ)
    (σ : Equiv.Perm (Fin k)) (v : Fin k → Fin (Fintype.card (IncrementGlobalIndex d C.order j)) → ℝ) :
    dyadicIncrementKernel C θ j x y m row k (fun i => v (σ i)) =
      dyadicIncrementKernel C θ j x y m row k v := by
  let F := rowIncrementPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m row
  have hF : (fun z => eval z F) = incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row :=
    funext fun _ => rowIncrementPolynomial_eval ..
  simp only [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply, ← hF]
  exact (AnalyticOnNhd.eval_mvPolynomial F).analyticOn.iteratedFDeriv_comp_perm
    (fun i => incrementPilotCoordinate j x (v i)) σ

theorem dyadicIncrementKernel_disjoint {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (j k : ℕ) (hk : 0 < k) (x v : Covariate d)
    (hxv : dyadicPilotLabel (j - 1) x ≠ dyadicPilotLabel (j - 1) v)
    (y t : ℝ) (m l : ℕ) (row s : Fin (anchoredDimension d C.order) → ℝ)
    (z : Fin k → Observation d) :
    dyadicIncrementKernel C θ j x y m row k (fun i => incrementGlobalVector j (z i)) *
      dyadicIncrementKernel C θ j v t l s k (fun i => incrementGlobalVector j (z i)) = 0 := by
  have hzero_off {u : Covariate d} {w : Observation d} (hw : w.1 ∉ dyadicPilotCell (j - 1) u) :
      dyadicIncrementRawVector (ℓ := C.order) j u w = 0 := by
    have hj : j ≠ 0 := fun h => by
      subst j; exact hw (Subsingleton.elim (regularGridCell 1 (by positivity) w.1) (regularGridCell 1 (by positivity) u))
    have hcur : w.1 ∉ dyadicPilotCell j u := fun h => hw (dyadicPilotCell_subset_parent j u h)
    have hp0 {lvl : ℕ} (hlvl : w.1 ∉ dyadicPilotCell lvl u) (b : LocalPilotIndex d C.order) :
        preconditionedPilotFeature lvl u b w = 0 := by simp [preconditionedPilotFeature, dyadicPilotFeature, hlvl]
    funext a
    change dyadicIncrementFeature j u _ w = 0
    generalize (Fintype.equivFin (incrementVariables (anchoredDimension d C.order))).symm a = va
    rcases va with (it | it) | ⟨parent, response, idx⟩
    · exact hp0 hcur _
    · simpa only [dyadicIncrementFeature, if_neg hj] using hp0 hw _
    · cases parent <;> cases response <;> simp [dyadicIncrementFeature, hj, hp0 hcur, hp0 hw]
  rw [dyadicIncrementKernel_raw, dyadicIncrementKernel_raw]
  let i0 : Fin k := ⟨0, hk⟩
  by_cases hz : (z i0).1 ∈ dyadicPilotCell (j - 1) x
  · have hzv : (z i0).1 ∉ dyadicPilotCell (j - 1) v := fun h =>
      hxv (((dyadicPilotLabel_eq_iff (j - 1) x (z i0).1).mpr hz).symm.trans
        ((dyadicPilotLabel_eq_iff (j - 1) v (z i0).1).mpr h))
    rw [(iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) t l s)
      (dyadicIncrementRawMean θ j v)).map_coord_zero i0 (hzero_off hzv), mul_zero]
  · rw [(iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row)
      (dyadicIncrementRawMean θ j x)).map_coord_zero i0 (hzero_off hz), zero_mul]

theorem dyadicPolynomialPilot_centered_global {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ)
    (row : Fin (anchoredDimension d C.order) → ℝ)
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
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m row :=
    funext fun _ => rowIncrementPolynomial_eval ..
  have he := LiftL2.polynomialLift_centering_l2 F
    (fun i (z : Fin n → Observation d) => dyadicIncrementRawVector j x (z i))
    (dyadicIncrementRawMean θ j x) (rowIncrementPolynomial_degree ..) hdegree
  change _ = RoughRegime.Upper.polynomialLift F
    (fun i (z : Fin n → Observation d) => dyadicIncrementRawVector j x (z i)) z - _
  rw [he]
  change _ = eval (dyadicIncrementRawMean θ j x) F + _ - _
  rw [rowIncrementPolynomial_eval, add_sub_cancel_left]
  simp only [LiftL2.centeredKernelExpansion, zero_add]
  refine Finset.sum_congr rfl fun r _ => congrArg (_ * ·) (Finset.sum_congr rfl fun e _ => ?_)
  rw [hF]
  simp [dyadicIncrementKernel, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    map_sub, incrementPilotCoordinate_mean C θ hθ]

theorem dyadicPilotCell_subset_coarser {d : ℕ} (j J : ℕ) (hj : j ≤ J) (x : Covariate d) :
    dyadicPilotCell J x ⊆ dyadicPilotCell j x := by
  induction J with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j; exact subset_rfl
  | succ J ih =>
    by_cases he : j = J + 1
    · subst j; exact subset_rfl
    · exact fun z hz => ih (by omega) (by simpa using dyadicPilotCell_subset_parent (J + 1) x hz)

def dyadicPilotRow {d ℓ : ℕ} (j : ℕ) (x z : Covariate d) : Fin (anchoredDimension d ℓ) → ℝ :=
  fun i => dyadicAnchoredFeature j x z (anchoredFinIndex i)

theorem dyadicPilotRow_sum_abs_le_distance {d ℓ : ℕ} (j : ℕ) (x z : Covariate d)
    (hx : x ∈ unitCube d) (hz : z ∈ unitCube d) (hc : z ∈ dyadicPilotCell j x) :
    (∑ i, |dyadicPilotRow (ℓ := ℓ) j x z i|) ≤
      (anchoredDimension d ℓ : ℝ) * (2 : ℝ) ^ j * euclideanNorm (z - x) := by
  refine (Finset.sum_le_sum (g := fun _ => (2 : ℝ) ^ j * euclideanNorm (z - x)) fun idx _ => ?_).trans_eq
    (by simp [mul_assoc])
  have hv (i : Fin d) : |((2 : ℝ) ^ j • (z - x)) i| ≤ 1 := by
    have hr := regular_grid_same_cell_radius ((2 : ℕ) ^ j) (by positivity) z x hz hx hc i
    rw [show (((2 : ℕ) ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j by simp] at hr
    change |(2 : ℝ) ^ j * (z i - x i)| ≤ 1
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans_eq (by field_simp)
  have h := anchoredMonomial_abs_le_euclideanNorm (anchoredFinIndex idx) ((2 : ℝ) ^ j • (z - x)) hv
  rwa [euclideanNorm_smul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j)] at h

theorem dyadicPilotRow_sum_abs_le_fine_cell {d ℓ : ℕ} (j J : ℕ) (hj : j ≤ J)
    (x z : Covariate d) (hx : x ∈ unitCube d) (hz : z ∈ unitCube d) (hc : z ∈ dyadicPilotCell J x) :
    (∑ i, |dyadicPilotRow (ℓ := ℓ) j x z i|) ≤
      (anchoredDimension d ℓ : ℝ) * (2 : ℝ) ^ j * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹ := by
  refine (dyadicPilotRow_sum_abs_le_distance j x z hx hz (dyadicPilotCell_subset_coarser j J hj x hc)).trans ?_
  have hr := euclideanNorm_le_coordinate_radius (z - x) (1 / (((2 : ℕ) ^ J : ℕ) : ℝ))
    (by positivity) (regular_grid_same_cell_radius ((2 : ℕ) ^ J) (by positivity) z x hz hx hc)
  exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans_eq (by simp [mul_assoc])

-- 6. Population increment bias & multiscale population coefficients

def anchoredFinVector {d ℓ : ℕ} (v : AnchoredIndex d ℓ → ℝ) : Fin (anchoredDimension d ℓ) → ℝ :=
  fun i => v (anchoredFinIndex i)

theorem anchoredFinVector_norm {d ℓ : ℕ} (v : AnchoredIndex d ℓ → ℝ) :
    ‖(EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm (anchoredFinVector v)‖ =
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm v‖ := by
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin (AnchoredIndex d ℓ))
  have he : e ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm v) =
      (EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm (anchoredFinVector v) := by
    ext i; rfl
  rw [← he]; exact e.norm_map _

theorem dyadicFinite_increment_eq_actual {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
    (x : Covariate d) (hx : x ∈ unitCube d) :
    (dyadicFinPilotGram (ℓ := ℓ) θ j x)⁻¹ *ᵥ
      (dyadicFinPilotMoments θ j x false - θ.regression x • dyadicFinPilotMoments θ j x true) -
      anchoredFinTransport d ℓ *ᵥ
        ((if j = 0 then 1 else dyadicFinPilotGram θ (j - 1) x)⁻¹ *ᵥ
          ((if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x) false -
            θ.regression x • (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x) true)) =
        anchoredFinVector (dyadicPopulationIncrement θ x j) := by
  have hmulVec (A : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) (v : AnchoredIndex d ℓ → ℝ) :
      anchoredFinReindex d ℓ A *ᵥ anchoredFinVector v = anchoredFinVector (A *ᵥ v) := by
    ext i
    simp only [anchoredFinReindex, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      anchoredFinVector, anchoredFinIndex, Matrix.mulVec, dotProduct]
    exact (Fintype.equivFin (AnchoredIndex d ℓ)).symm.sum_comp fun γ => A (anchoredFinIndex i) γ * v γ
  have hfit (k : ℕ) : (dyadicFinPilotGram (ℓ := ℓ) θ k x)⁻¹ *ᵥ
      (dyadicFinPilotMoments θ k x false - θ.regression x • dyadicFinPilotMoments θ k x true) =
      anchoredFinVector (dyadicPopulationFit θ k x) := by
    have hmom (t : Bool) : dyadicFinPilotMoments (ℓ := ℓ) θ k x t = anchoredFinVector
        ((dyadicKnownGram k x)⁻¹ *ᵥ (if t then dyadicConstantMoment θ k x else dyadicResponseMoment θ k x)) := by
      ext i; cases t <;>
      · simp only [dyadicFinPilotMoments, Bool.false_eq_true, ↓reduceIte, anchoredFinVector]
        rw [preconditionedPilotPopulation_eq_sum C θ hθ k x hx]
        simp only [localPilotRow, localPilotReplaceRow, Matrix.mulVec, dotProduct,
          dyadicPilotPopulation_response C θ hθ k x hx, dyadicPilotPopulation_constant C θ hθ]
    rw [hmom false, hmom true]; simp only [Bool.false_eq_true, ↓reduceIte]
    change (dyadicFinPilotGram θ k x)⁻¹ *ᵥ anchoredFinVector (_ - θ.regression x • _) = _
    have hinv_re (A : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) :
        (anchoredFinReindex d ℓ A)⁻¹ = anchoredFinReindex d ℓ A⁻¹ := Matrix.inv_reindex _ _ A
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_sub, dyadicFinPilotGram, hinv_re,
      hmulVec, dyadicPopulationFit_preconditioner_cancels C θ hθ]
  rw [hfit j]
  cases j with
  | zero => simp [dyadicPopulationIncrement, anchoredIncrement]
  | succ j =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel_right]
    rw [hfit j, anchoredFinTransport, hmulVec]; rfl

theorem incrementFinVector_eval_population {r : ℕ} [NeZero r] (a b : ℝ)
    (A B T : Matrix (Fin r) (Fin r) ℝ) (U V : Bool → Fin r → ℝ) (y : ℝ) (m : ℕ) :
    incrementFinVector r a b T y m
      (fun i => incrementValuation A B U V ((Fintype.equivFin (incrementVariables r)).symm i)) =
        fun i => eval (incrementValuation A B U V) (incrementEntryPolynomial r a b T y m i) := by
  ext i; simp [incrementFinVector, incrementFinPolynomial, eval_rename, Function.comp_def]

theorem anchoredNormalized_increment_error {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)]
    (u v : Covariate d) (p q : Covariate d → ℝ) (hpmeas : Measurable p) (hqmeas : Measurable q)
    (a b χ ε : ℝ) (ha : 0 < a) (hab : a < b)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)
    (hq : ∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b)
    (hχ : ‖(anchoredFinSimilarityUnit (ℓ := ℓ) u).val‖ *
      ‖((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ)
    (U V : Bool → Fin (anchoredDimension d ℓ) → ℝ)
    (y : ℝ) (T : Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ)
    (hδ : ‖(EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm
      ((anchoredFinNormalizedGram u p)⁻¹ *ᵥ (U false - y • U true) -
        T *ᵥ ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - y • V true)))‖ ≤ ε) (m : ℕ) :
    ‖(EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm
      ((fun i => eval (incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q) U V)
          (incrementEntryPolynomial (anchoredDimension d ℓ) a b T y m i)) -
        ((anchoredFinNormalizedGram u p)⁻¹ *ᵥ (U false - y • U true) -
          T *ᵥ ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - y • V true))))‖ ≤
      (χ ^ 2 * b ^ (anchoredDimension d ℓ + 1) * parentInverseErrorConstant a b (anchoredDimension d ℓ)) * ε *
        ((m + 1 : ℕ) : ℝ) ^ anchoredDimension d ℓ * Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  let Q := anchoredFinSimilarityUnit (ℓ := ℓ) u
  let R := anchoredFinSimilarityUnit (ℓ := ℓ) v
  let G := anchoredFinNormalizedGram (ℓ := ℓ) u p
  let H := anchoredFinNormalizedGram (ℓ := ℓ) v q
  have hG : matrixSimilarity Q (matrixSimilarity Q⁻¹ G) = G := by simp [matrixSimilarity, Matrix.mul_assoc]
  have hH : matrixSimilarity R (matrixSimilarity R⁻¹ H) = H := by simp [matrixSimilarity, Matrix.mul_assoc]
  simpa only [hG, hH] using incrementEntryPolynomial_error a b ha hab
    (matrixSimilarity Q⁻¹ G) (matrixSimilarity R⁻¹ H) T
    (anchoredFin_similarity_isHermitian u p) (anchoredFin_similarity_isHermitian v q)
    (anchoredFin_similarity_spectrum u p hpmeas a b ha.le hp)
    (anchoredFin_similarity_spectrum v q hqmeas a b ha.le hq)
    Q R χ hχ U V y ε (by simpa only [hG, hH] using hδ) m

theorem dyadicPilotRow_dot_coefficients {d ℓ : ℕ} (j : ℕ) (x y : Covariate d) (v : AnchoredIndex d ℓ → ℝ) :
    dyadicPilotRow j x y ⬝ᵥ anchoredFinVector v = dyadicAnchoredFeature j x y ⬝ᵥ v :=
  (Fintype.equivFin (AnchoredIndex d ℓ)).symm.sum_comp fun γ => dyadicAnchoredFeature j x y γ * v γ

theorem finite_row_abs_dot_le_euclidean_norm {ι : Type*} [Fintype ι] (row v : ι → ℝ) :
    |row ⬝ᵥ v| ≤ (∑ i, |row i|) * ‖(EuclideanSpace.equiv ι ℝ).symm v‖ := by
  refine (Finset.abs_sum_le_sum_abs ..).trans
    ((Finset.sum_le_sum fun i _ => ?_).trans_eq (Finset.sum_mul ..).symm)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (by simpa [EuclideanSpace.equiv, Real.norm_eq_abs] using PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℝ).symm v) i)
    (abs_nonneg _)

theorem dyadic_scale_rpow_cancel (j : ℕ) (s : ℝ) :
    (2 : ℝ) ^ j * (((2 : ℝ) ^ j)⁻¹) ^ s = (((2 : ℝ) ^ j)⁻¹) ^ (s - 1) := by
  simpa only [inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ j ≠ 0), one_mul, mul_comm] using
    positive_rpow_times_distance (((2 : ℝ) ^ j)⁻¹) s ((2 : ℝ) ^ j) (by positivity)

def dyadicPopulationPolynomial {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ) : Fin (anchoredDimension d C.order) → ℝ :=
  incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) y m (dyadicIncrementRawMean θ j x)

def dyadicPopulationBiasBudget {d : ℕ} (C : ModelConstants d) (J : ℕ) (m : ℕ → ℕ) : ℝ :=
  (((2 : ℝ) ^ J)⁻¹) ^ (C.smoothness - 1) +
    ∑ j ∈ Finset.range (J + 1), (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) *
      ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-(m j : ℝ) * paperTau C)

def dyadicPopulationResidual {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : ℕ → ℕ) (x y : Covariate d) : ℝ :=
  θ.regression y - θ.regression x - ∑ j ∈ Finset.range (J + 1),
    dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)

theorem dyadicIncrementRawMean_eq_with_virtual_parent {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ)
    (x : Covariate d) (hx : x ∈ unitCube d) :
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
  · simp only [hj, ite_false]; rw [dyadicFinPilotGram_eq_normalized C θ hθ (j - 1) x]

def dyadicPopulationRawPolynomial {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (t : Bool) (m : ℕ) : Fin (anchoredDimension d C.order) → ℝ :=
  incrementFinRawVector (anchoredDimension d C.order) C.densityLower C.densityUpper
    (anchoredFinTransport d C.order) t m (dyadicIncrementRawMean θ j x)

theorem dyadicPopulationPolynomial_affine {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (j : ℕ) (x : Covariate d) (y : ℝ) (m : ℕ) :
    dyadicPopulationPolynomial C θ j x y m = dyadicPopulationRawPolynomial C θ j x false m -
      y • dyadicPopulationRawPolynomial C θ j x true m :=
  congrFun (incrementFinVector_affine _ _ _ _ y m) (dyadicIncrementRawMean θ j x)

def dyadicPopulationPilotSum {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : ℕ → ℕ) (t : Bool) (w : Covariate d × Covariate d) : ℝ :=
  ∑ j ∈ Finset.range (J + 1),
    dyadicPilotRow j w.1 w.2 ⬝ᵥ dyadicPopulationRawPolynomial C θ j w.1 t (m j)

def dyadicPopulationCoefficients {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (J : ℕ) (m : ℕ → ℕ) (w : Covariate d × Covariate d) : PairVector :=
  WithLp.toLp 2 ![1, -1 + dyadicPopulationPilotSum C θ J m true w,
    -dyadicPopulationPilotSum C θ J m false w]

theorem finite_row_abs_dot_le_pi_norm {ι : Type*} [Fintype ι] (row v : ι → ℝ) :
    |row ⬝ᵥ v| ≤ (∑ i, |row i|) * ‖v‖ := by
  refine (Finset.abs_sum_le_sum_abs ..).trans
    ((Finset.sum_le_sum fun i _ => ?_).trans_eq (Finset.sum_mul ..).symm)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i) (abs_nonneg _)

theorem dyadicPilotRow_total_abs_le {d ℓ : ℕ} (J : ℕ) (x y : Covariate d)
    (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) (hc : y ∈ dyadicPilotCell J x) :
    (∑ j ∈ Finset.range (J + 1), ∑ i, |dyadicPilotRow (ℓ := ℓ) j x y i|) ≤
      2 * (anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) := by
  have hg : (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ (J + 1) := by
    clear hx hy hc
    induction J with
    | zero => norm_num
    | succ J ih => rw [Finset.sum_range_succ, pow_succ _ (J + 1)]; linarith
  refine (Finset.sum_le_sum fun j hj =>
    dyadicPilotRow_sum_abs_le_fine_cell j J (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x y hx hy hc).trans ?_
  calc ∑ j ∈ Finset.range (J + 1), (anchoredDimension d ℓ : ℝ) * (2 : ℝ) ^ j * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹
    _ = ((anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹) * ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ((anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹) * (2 : ℝ) ^ (J + 1) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
    _ = 2 * (anchoredDimension d ℓ : ℝ) * Real.sqrt (d : ℝ) := by rw [pow_succ]; field_simp

theorem dyadicPopulationCoefficients_residual {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (J : ℕ) (m : ℕ → ℕ) (x y : Covariate d) :
    ⟪dyadicPopulationCoefficients C θ J m (x, y), pairResponseVector (θ.regression x) (θ.regression y)⟫ =
      dyadicPopulationResidual C θ J m x y := by
  have hsum : (∑ j ∈ Finset.range (J + 1),
      dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)) =
      dyadicPopulationPilotSum C θ J m false (x, y) - θ.regression x * dyadicPopulationPilotSum C θ J m true (x, y) := by
    simp only [dyadicPopulationPolynomial_affine, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      Finset.sum_sub_distrib, dyadicPopulationPilotSum, Finset.mul_sum]
  rw [pairResponseVector_inner]
  change 1 * θ.regression y + (-1 + dyadicPopulationPilotSum C θ J m true (x, y)) * θ.regression x +
    (-dyadicPopulationPilotSum C θ J m false (x, y)) = dyadicPopulationResidual C θ J m x y
  unfold dyadicPopulationResidual; rw [hsum]; ring

theorem dyadicPopulationCoefficients_measurable {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (J : ℕ) (m : ℕ → ℕ) :
    Measurable (dyadicPopulationCoefficients C θ J m) := by
  have hsum_m (t : Bool) : Measurable (dyadicPopulationPilotSum C θ J m t) :=
    Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun i _ =>
      (dyadicAnchoredFeature_joint_measurable j (anchoredFinIndex i)).mul
        (((MvPolynomial.continuous_eval (MvPolynomial.rename
          (Fintype.equivFin (incrementVariables (anchoredDimension d C.order)))
          (rawIncrementEntryPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) t (m j) i))).measurable.comp
          (dyadicIncrementRawMean_measurable C θ hθ j)).comp measurable_fst)
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp (measurable_pi_iff.mpr fun i => ?_)
  fin_cases i
  · exact measurable_const
  · exact measurable_const.add (hsum_m true)
  · exact (hsum_m false).neg

-- 7. Kernel field measurability, weak tests & multilevel error fields

instance finiteInputMultilinearMeasurableSpace {p k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    MeasurableSpace (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) F) := borel _

instance finiteInputMultilinearBorelSpace {p k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    BorelSpace (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) F) := ⟨rfl⟩

instance finiteInputScalarMultilinearFiniteDimensional (p k : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ) := by
  let e : (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin p → ℝ) ℝ) →L[ℝ] ((Fin k → Fin p) → ℝ) :=
    ContinuousLinearMap.pi fun σ =>
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin p → ℝ) ℝ (fun i => Pi.single (σ i) 1)
  refine FiniteDimensional.of_injective e.toLinearMap fun H G he => ?_
  ext v
  change H.toMultilinearMap v = G.toMultilinearMap v
  rw [LiftL2.multilinear_coordinate_expansion H.toMultilinearMap, LiftL2.multilinear_coordinate_expansion G.toMultilinearMap]
  exact Finset.sum_congr rfl fun σ _ => congrArg (· * ∏ i, v i (σ i)) (congrFun he σ)

theorem dyadicIncrementKernel_field_measurable {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (j : ℕ) (y : ℝ) (m k : ℕ)
    (row : Covariate d × Covariate d → Fin (anchoredDimension d C.order) → ℝ) (hrow : Measurable row) :
    Measurable (fun w : Covariate d × Covariate d => dyadicIncrementKernel C θ j w.1 y m (row w) k) := by
  have hm : Measurable fun w : Covariate d × Covariate d => dyadicIncrementRawMean (ℓ := C.order) θ j w.1 :=
    (dyadicIncrementRawMean_measurable (ℓ := C.order) C θ hθ j).comp measurable_fst
  have hD := ((incrementFinVector_contDiff (anchoredDimension d C.order)
    C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m).continuous_iteratedFDeriv
      (show (k : WithTop ℕ∞) ≤ ⊤ from le_top)).measurable.comp hm
  have hpost : Continuous fun z : (Fin (anchoredDimension d C.order) → ℝ) ×
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin (Fintype.card (incrementVariables (anchoredDimension d C.order))) → ℝ)
        (Fin (anchoredDimension d C.order) → ℝ) => (rowFunctional z.1).compContinuousMultilinearMap z.2 := by
    change Continuous fun z : (Fin (anchoredDimension d C.order) → ℝ) ×
        ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin (Fintype.card (incrementVariables (anchoredDimension d C.order))) → ℝ)
          (Fin (anchoredDimension d C.order) → ℝ) =>
      (ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ _ ℝ (rowFunctional z.1)) z.2
    exact ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ _ ℝ).continuous.comp
      ((continuous_finsetSum Finset.univ fun i _ => (continuous_apply i).smul continuous_const).comp continuous_fst)).clm_apply
      continuous_snd
  have hpull : Continuous fun z :
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin (Fintype.card (incrementVariables (anchoredDimension d C.order))) → ℝ) ℝ ×
        ((Fin (Fintype.card (IncrementGlobalIndex d C.order j)) → ℝ) →L[ℝ]
          (Fin (Fintype.card (incrementVariables (anchoredDimension d C.order))) → ℝ)) =>
      z.1.compContinuousLinearMap fun _ => z.2 := by
    change Continuous fun z :
        ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin (Fintype.card (incrementVariables (anchoredDimension d C.order))) → ℝ) ℝ ×
          ((Fin (Fintype.card (IncrementGlobalIndex d C.order j)) → ℝ) →L[ℝ]
            (Fin (Fintype.card (incrementVariables (anchoredDimension d C.order))) → ℝ)) =>
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ _ _ ℝ (fun _ => z.2)) z.1
    exact ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ _ _ ℝ).cont.comp
      (continuous_pi fun _ => continuous_snd)).clm_apply continuous_fst
  have hscalar := hpost.measurable.comp (hrow.prodMk hD)
  change Measurable fun w : Covariate d × Covariate d =>
    (rowFunctional (row w)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ k (incrementFinVector (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m) (dyadicIncrementRawMean θ j w.1)) at hscalar
  have heq : (fun w : Covariate d × Covariate d =>
      (rowFunctional (row w)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (incrementFinVector (anchoredDimension d C.order)
          C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m) (dyadicIncrementRawMean θ j w.1))) =
      fun w => iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
        C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m (row w)) (dyadicIncrementRawMean θ j w.1) := by
    funext w; ext v; exact (incrementFinScalar_iteratedFDeriv ..).symm
  rw [heq] at hscalar
  have hres := hpull.measurable.comp
    (hscalar.prodMk ((incrementPilotCoordinate_measurable (ℓ := C.order) j).comp measurable_fst))
  exact hres

theorem dyadicIncrementKernel_field_norm_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (j : ℕ) (y : ℝ) (hy : |y| ≤ C.holderBound) (m k : ℕ)
    (row : Covariate d × Covariate d → Fin (anchoredDimension d C.order) → ℝ)
    (M : Measure (Covariate d × Covariate d)) (R : ℝ) (hR : 0 ≤ R)
    (hcube : ∀ᵐ w ∂M, w.1 ∈ unitCube d) (hrow : ∀ᵐ w ∂M, (∑ i, |row w i|) ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ w ∂M, ‖dyadicIncrementKernel C θ j w.1 y m (row w) k‖ ≤ B := by
  obtain ⟨W, hW, hmom⟩ := anchoredFinMomentFamilies_uniform_bound (d := d) (ℓ := C.order)
    C.densityUpper C.holderBound (zero_le_one.trans C.one_lt_densityUpper.le) C.holderBound_pos.le
  obtain ⟨D, A, hD, hA, hder⟩ := anchored_population_inverse_derivatives
    (d := d) (ℓ := C.order) C.densityLower C.densityUpper W C.holderBound C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le C.holderBound_pos.le
  obtain ⟨L, hL, hmap⟩ := incrementPilotCoordinate_uniform_bound (d := d) (ℓ := C.order) j
  let B := R * D * (k.factorial : ℝ) * A ^ k * L ^ k
  refine ⟨max 1 B, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hcube, hrow] with w hw hr
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hlprod : (∏ _i : Fin k, ‖incrementPilotCoordinate (ℓ := C.order) j w.1‖) ≤ L ^ k :=
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun _ _ => hmap _ hw).trans_eq (by simp)
  -- Scalar derivative bound at `w.1 ∈ unitCube d` via virtual parent
  have hmom_pt (lvl : ℕ) (t : Bool) : ‖dyadicFinPilotMoments (ℓ := C.order) θ lvl w.1 t‖ ≤ W := by
    rw [dyadicFinPilotMoments_eq_anchored C θ hθ lvl w.1 hw]
    exact hmom _ (gridNormalizedAnchor_mem_cube _ (by positivity) w.1 hw) _ _
      ((dyadicNormalizedDensity_bounds C θ hθ lvl w.1).mono fun _ hz => ⟨C.densityLower_pos.le.trans hz.1, hz.2⟩)
      (fun z hz => admissible_regression_value_bound C θ hθ _ (dyadicCellAffine_mem_cube lvl w.1 z hz)) t
  have hqm : Measurable (if j = 0 then fun _ : Covariate d => (1 : ℝ) else dyadicNormalizedDensity θ (j - 1) w.1) := by
    by_cases hj : j = 0 <;> simp [hj, measurable_const, dyadicNormalizedDensity_measurable C θ hθ]
  have hqb : ∀ᵐ z ∂cubeVolume d, C.densityLower ≤ (if j = 0 then fun _ => (1 : ℝ) else dyadicNormalizedDensity θ (j - 1) w.1) z ∧
      (if j = 0 then fun _ => (1 : ℝ) else dyadicNormalizedDensity θ (j - 1) w.1) z ≤ C.densityUpper := by
    by_cases hj : j = 0
    · simp only [hj, ↓reduceIte]
      exact Eventually.of_forall fun _ => ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩
    · simp only [hj, ↓reduceIte]; exact dyadicNormalizedDensity_bounds C θ hθ (j - 1) w.1
  have hV (t : Bool) : ‖(if j = 0 then (0 : Bool → Fin (anchoredDimension d C.order) → ℝ)
      else dyadicFinPilotMoments θ (j - 1) w.1) t‖ ≤ W := by
    by_cases hj : j = 0 <;> simp [hj, hW.le, hmom_pt (j - 1) t]
  have hd : ‖iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d C.order)
      C.densityLower C.densityUpper (anchoredFinTransport d C.order) y m (row w))
      (dyadicIncrementRawMean θ j w.1)‖ ≤ R * D * (k.factorial : ℝ) * A ^ k := by
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun dirs => ?_
    rw [incrementFinScalar_iteratedFDeriv]
    have hd_vec := hder (dyadicNormalizedAnchor j w.1) (dyadicNormalizedAnchor (j - 1) w.1)
      (gridNormalizedAnchor_mem_cube _ (by positivity) w.1 hw)
      (gridNormalizedAnchor_mem_cube _ (by positivity) w.1 hw)
      (dyadicNormalizedDensity θ j w.1) _
      (dyadicNormalizedDensity_measurable C θ hθ j w.1) hqm
      (dyadicNormalizedDensity_bounds C θ hθ j w.1) hqb
      (dyadicFinPilotMoments θ j w.1) _ (hmom_pt j) hV y hy m k dirs
    rw [← dyadicIncrementRawMean_eq_with_virtual_parent C θ hθ j w.1 hw] at hd_vec
    calc ‖rowFunctional (row w) (iteratedFDeriv ℝ k _ _ dirs)‖
      _ ≤ ‖rowFunctional (row w)‖ * ‖iteratedFDeriv ℝ k _ _ dirs‖ := (rowFunctional (row w)).le_opNorm _
      _ ≤ R * (D * (k.factorial : ℝ) * A ^ k * ∏ i, ‖dirs i‖) :=
          mul_le_mul ((rowFunctional_norm_le (row w)).trans hr) hd_vec (norm_nonneg _) hR
      _ = _ := by ring
  exact (mul_le_mul hd hlprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)).trans (le_max_right _ _)

theorem dyadicIncrementKernel_weighted_integrable {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (j : ℕ) (y : ℝ) (hy : |y| ≤ C.holderBound) (m k : ℕ)
    (row : Covariate d × Covariate d → Fin (anchoredDimension d C.order) → ℝ)
    (hrowMeas : Measurable row) (M : Measure (Covariate d × Covariate d)) [IsFiniteMeasure M]
    (R : ℝ) (hR : 0 ≤ R) (hcube : ∀ᵐ w ∂M, w.1 ∈ unitCube d)
    (hrow : ∀ᵐ w ∂M, (∑ i, |row w i|) ≤ R) (ν : Covariate d × Covariate d → ℝ) (hν : MemLp ν 2 M) :
    Integrable (fun w => ν w • dyadicIncrementKernel C θ j w.1 y m (row w) k) M := by
  obtain ⟨B, _, hcap⟩ := dyadicIncrementKernel_field_norm_bound C θ hθ j y hy m k row M R hR hcube hrow
  exact (hν.integrable (by norm_num)).smul_bdd B
    (dyadicIncrementKernel_field_measurable C θ hθ j y m k row hrowMeas).aestronglyMeasurable hcap

theorem dyadicPilotRow_field_measurable {d ℓ : ℕ} (j : ℕ) :
    Measurable (fun w : Covariate d × Covariate d => dyadicPilotRow (ℓ := ℓ) j w.1 w.2) :=
  measurable_pi_iff.mpr fun i => dyadicAnchoredFeature_joint_measurable j (anchoredFinIndex i)

def dyadicPilotRowCap (d ℓ j J : ℕ) : ℝ :=
  (anchoredDimension d ℓ : ℝ) * (2 : ℝ) ^ j * Real.sqrt (d : ℝ) * ((2 : ℝ) ^ J)⁻¹

theorem dyadicPilotRowCap_nonneg (d ℓ j J : ℕ) : 0 ≤ dyadicPilotRowCap d ℓ j J := by
  unfold dyadicPilotRowCap; positivity

theorem dyadicPilotRowCap_square (d ℓ j L : ℕ) (D : ℝ) :
    (dyadicPilotRowCap d ℓ j L * D) ^ 2 =
      ((anchoredDimension d ℓ : ℝ) * D) ^ 2 * (d : ℝ) * (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ j) ^ 2 := by
  simp only [dyadicPilotRowCap, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]; ring

theorem dyadicPilotRow_pair_cap {d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (j J : ℕ) (hj : j ≤ J) :
    ∀ᵐ w ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity),
      (∑ i, |dyadicPilotRow (ℓ := ℓ) j w.1 w.2 i|) ≤ dyadicPilotRowCap d ℓ j J := by
  have hsame : ∀ᵐ w ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity),
      regularGridCell ((2 : ℕ) ^ J) (by positivity) w.1 = regularGridCell ((2 : ℕ) ^ J) (by positivity) w.2 :=
    Measure.ae_smul_measure (ae_restrict_mem (measurableSet_eq_fun
      ((regular_grid_cell_measurable _ _).comp measurable_fst)
      ((regular_grid_cell_measurable _ _).comp measurable_snd))) _
  filter_upwards [regularPairDesignMeasure_cube_ae C θ hθ ((2 : ℕ) ^ J) (by positivity), hsame] with w hw hc
  exact dyadicPilotRow_sum_abs_le_fine_cell j J hj w.1 w.2 hw.1 hw.2 hc.symm

def dyadicPilotErrorField {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (n j : ℕ) (y : ℝ) (m : ℕ) (z : Fin n → Observation d) (w : Covariate d × Covariate d) : ℝ :=
  dyadicPolynomialPilot C n j w.1 y m (dyadicPilotRow j w.1 w.2) z -
    incrementFinScalar (anchoredDimension d C.order) C.densityLower C.densityUpper
      (anchoredFinTransport d C.order) y m (dyadicPilotRow j w.1 w.2) (dyadicIncrementRawMean θ j w.1)

def dyadicMultilevelErrorField {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d)
    (n J : ℕ) (y : ℝ) (m : ℕ → ℕ) (z : Fin n → Observation d) (w : Covariate d × Covariate d) : ℝ :=
  ∑ j : Fin (J + 1), dyadicPilotErrorField C θ n j.val y (m j.val) z w

def dyadicMultilevelBudget (H : ℝ) (J L : ℕ) : ℝ :=
  (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ J) ^ 2 * H

theorem secondMoment_dyadic_sum_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (J : ℕ) (X : Fin (J + 1) → Ω → ℝ)
    (hX : ∀ j, MemLp (X j) 2 μ) (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ j, (∫ z, X j z ^ 2 ∂μ) ≤ B * ((2 : ℝ) ^ j.val) ^ 2) :
    (∫ z, (∑ j, X j z) ^ 2 ∂μ) ≤ 4 * B * ((2 : ℝ) ^ J) ^ 2 := by
  classical
  let w (j : Fin (J + 1)) : ℝ := (2 : ℝ) ^ j.val
  have hw (j) : 0 < w j := by dsimp [w]; positivity
  have hsum : MemLp (fun z => ∑ j, X j z) 2 μ := memLp_finsetSum _ fun j _ => hX j
  have hi (j) : Integrable (fun z => X j z ^ 2 / w j) μ := (hX j).integrable_sq.div_const _
  have hm := integral_mono hsum.integrable_sq
    ((integrable_finsetSum Finset.univ fun j _ => hi j).const_mul (∑ j, w j)) fun z =>
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ (fun j _ => (hw j).le)
      (fun j _ => div_nonneg (sq_nonneg _) (hw j).le) fun j _ => le_of_eq (by field_simp [(hw j).ne'])
  rw [integral_const_mul, integral_finsetSum Finset.univ fun j _ => hi j] at hm
  have hterms : (∑ j, ∫ z, X j z ^ 2 / w j ∂μ) ≤ B * ∑ j, w j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [integral_div]
    exact (div_le_div_of_nonneg_right (hE j) (hw j).le).trans_eq (by dsimp [w]; field_simp [(hw j).ne'])
  have hwt_le : (∑ j : Fin (J + 1), w j) ≤ 2 * (2 : ℝ) ^ J := by
    dsimp [w]; rw [Fin.sum_univ_eq_sum_range]
    have h := geom_sum_mul_of_one_le (by norm_num : (1 : ℝ) ≤ 2) (J + 1)
    norm_num only [sub_self, add_zero, sub_zero, mul_one] at h
    rw [h, pow_succ]; linarith
  have hw_nn : 0 ≤ ∑ j, w j := Finset.sum_nonneg fun j _ => (hw j).le
  have h1 := hm.trans (mul_le_mul_of_nonneg_left hterms hw_nn)
  have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw_nn hwt_le 2) hB
  nlinarith

theorem dyadicPilotErrorField_point_moment_facts {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n j : ℕ) (x : Covariate d) (hx : x ∈ unitCube d) (z : Covariate d)
    (y : ℝ) (m : ℕ) (hdegree : m + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (fun t => dyadicPilotErrorField C θ n j y m t (x, z)) 2 (sampleLaw θ n) ∧
      (∫ t, dyadicPilotErrorField C θ n j y m t (x, z) ∂sampleLaw θ n) = 0 := by
  let _ := sampleLaw_isProbability C θ hθ n
  obtain ⟨hL2, hmean⟩ := dyadicPolynomialPilot_moment_facts C θ hθ n j x hx y m (dyadicPilotRow j x z) hdegree
  refine ⟨hL2.sub (memLp_const _), ?_⟩
  unfold dyadicPilotErrorField
  rw [integral_sub (hL2.integrable (by norm_num)) (integrable_const _), hmean]; simp

theorem dyadicMultilevelErrorField_point_moment_facts {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n J : ℕ) (x : Covariate d) (hx : x ∈ unitCube d) (z : Covariate d)
    (y : ℝ) (m : ℕ → ℕ) (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) :
    MemLp (fun t => dyadicMultilevelErrorField C θ n J y m t (x, z)) 2 (sampleLaw θ n) ∧
      (∫ t, dyadicMultilevelErrorField C θ n J y m t (x, z) ∂sampleLaw θ n) = 0 := by
  let _ := sampleLaw_isProbability C θ hθ n
  have hf (j : Fin (J + 1)) := dyadicPilotErrorField_point_moment_facts C θ hθ n j.val x hx z y (m j.val) (hdegree j)
  refine ⟨memLp_finsetSum _ fun j _ => (hf j).1, ?_⟩
  unfold dyadicMultilevelErrorField
  rw [integral_finsetSum Finset.univ fun j _ => (hf j).1.integrable (by norm_num)]
  exact Finset.sum_eq_zero fun j _ => (hf j).2

theorem dyadicPilotErrorField_weighted_integrable {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n j L : ℕ) (hj : j ≤ L) (y : ℝ) (hy : |y| ≤ C.holderBound) (m : ℕ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n)
    (ν : Covariate d × Covariate d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)))
    (t : Fin n → Observation d) :
    Integrable (fun w => ν w * dyadicPilotErrorField C θ n j y m t w)
      (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) := by
  let M := regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)
  let _ := regularPairDesignMeasure_isFinite C θ hθ ((2 : ℕ) ^ L) (by positivity)
  let R := m + anchoredDimension d C.order + 1
  let H (w : Covariate d × Covariate d) (r : Fin R) :=
    dyadicIncrementKernel C θ j w.1 y m (dyadicPilotRow j w.1 w.2) (r.val + 1)
  have hc : ∀ᵐ w ∂M, w.1 ∈ unitCube d :=
    (regularPairDesignMeasure_cube_ae C θ hθ ((2 : ℕ) ^ L) (by positivity)).mono fun _ hw => hw.1
  have hH (r : Fin R) : Integrable (fun w => ν w • H w r) M :=
    dyadicIncrementKernel_weighted_integrable C θ hθ j y hy m (r.val + 1) _
      (dyadicPilotRow_field_measurable j) M (dyadicPilotRowCap d C.order j L)
      (dyadicPilotRowCap_nonneg ..) hc (dyadicPilotRow_pair_cap (ℓ := C.order) C θ hθ j L hj) ν hν
  have hi := integrable_finsetSum Finset.univ fun r _ =>
    FieldLiftCovariance.weighted_kernel_statistic_integrable
      (fun i (z : Fin n → Observation d) => incrementGlobalVector (ℓ := C.order) j (z i) - incrementGlobalMean θ j)
      ν (fun w => H w r) (hH r) t
  have heq : (fun w => ν w * dyadicPilotErrorField C θ n j y m t w) =
      fun w => ∑ r : Fin R, ν w * LiftL2.kernelStatistic (H w r)
        (fun i z => incrementGlobalVector (ℓ := C.order) j (z i) - incrementGlobalMean θ j) t := by
    funext w; unfold dyadicPilotErrorField
    rw [← dyadicPolynomialPilot_centered_global C θ hθ n j w.1 y m (dyadicPilotRow j w.1 w.2) hdegree t]
    simp only [LiftL2.centeredKernelExpansion, zero_add, Finset.mul_sum]; rfl
  rwa [heq]

theorem dyadicPilotErrorField_test_moment_facts {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n j J : ℕ) (hj : j ≤ J) (y : ℝ) (hy : |y| ≤ C.holderBound) (m : ℕ)
    (hdegree : m + anchoredDimension d C.order + 1 ≤ n)
    (ν : Covariate d × Covariate d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity))) :
    MemLp (fun z => ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)) 2 (sampleLaw θ n) ∧
    (∫ z, ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity) ∂sampleLaw θ n) = 0 := by
  let _ := sampleLaw_isProbability C θ hθ n
  let M := regularPairDesignMeasure θ ((2 : ℕ) ^ J) (by positivity)
  let _ := regularPairDesignMeasure_isFinite C θ hθ ((2 : ℕ) ^ J) (by positivity)
  let R := m + anchoredDimension d C.order + 1
  let H (w : Covariate d × Covariate d) (r : Fin R) :=
    dyadicIncrementKernel C θ j w.1 y m (dyadicPilotRow j w.1 w.2) (r.val + 1)
  have hc : ∀ᵐ w ∂M, w.1 ∈ unitCube d :=
    (regularPairDesignMeasure_cube_ae C θ hθ ((2 : ℕ) ^ J) (by positivity)).mono fun _ hw => hw.1
  have hH (r : Fin R) : Integrable (fun w => ν w • H w r) M :=
    dyadicIncrementKernel_weighted_integrable C θ hθ j y hy m (r.val + 1) _
      (dyadicPilotRow_field_measurable j) M (dyadicPilotRowCap d C.order j J)
      (dyadicPilotRowCap_nonneg ..) hc (dyadicPilotRow_pair_cap (ℓ := C.order) C θ hθ j J hj) ν hν
  obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := incrementGlobalVector_sample_facts (ℓ := C.order) C θ hθ j
  have h := FieldLiftCovariance.integrated_centered_lift_moment_facts H ν hH
    (fun i (z : Fin n → Observation d) => incrementGlobalVector j (z i))
    (incrementGlobalMean θ j) hind hmeas hid hL2 hmean
  have heq : (fun z : Fin n → Observation d => ∫ w, ν w *
      LiftL2.centeredKernelExpansion 0 (H w)
        (fun i z => incrementGlobalVector j (z i) - incrementGlobalMean θ j) z ∂M) =
      fun z => ∫ w, ν w * dyadicPilotErrorField C θ n j y m z w ∂M :=
    funext fun z => integral_congr_ae <| Eventually.of_forall fun w => congrArg (ν w * ·)
      (dyadicPolynomialPilot_centered_global C θ hθ n j w.1 y m (dyadicPilotRow j w.1 w.2) hdegree z)
  rwa [heq] at h

theorem dyadicMultilevelErrorField_test_integral_sum {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n J L : ℕ) (hJL : J ≤ L) (y : ℝ) (hy : |y| ≤ C.holderBound) (m : ℕ → ℕ)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n)
    (ν : Covariate d × Covariate d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)))
    (t : Fin n → Observation d) :
    (∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) =
    ∑ j : Fin (J + 1), ∫ w, ν w * dyadicPilotErrorField C θ n j.val y (m j.val) t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity) := by
  unfold dyadicMultilevelErrorField; simp_rw [Finset.mul_sum]
  exact integral_finsetSum Finset.univ fun j _ =>
    dyadicPilotErrorField_weighted_integrable C θ hθ n j.val L
      ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy (m j.val) (hdegree j) ν hν t

theorem dyadicMultilevelErrorField_test_moment_facts {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n J L : ℕ) (hJL : J ≤ L) (y : ℝ) (hy : |y| ≤ C.holderBound) (m : ℕ → ℕ)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n)
    (ν : Covariate d × Covariate d → ℝ)
    (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity))) :
    MemLp (fun t => ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) 2 (sampleLaw θ n) ∧
    (∫ t, ∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
      ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity) ∂sampleLaw θ n) = 0 := by
  let _ := sampleLaw_isProbability C θ hθ n
  have hf (j : Fin (J + 1)) := dyadicPilotErrorField_test_moment_facts C θ hθ n j.val L
    ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy (m j.val) (hdegree j) ν hν
  simp_rw [dyadicMultilevelErrorField_test_integral_sum C θ hθ n J L hJL y hy m hdegree ν hν]
  refine ⟨memLp_finsetSum _ fun j _ => (hf j).1, ?_⟩
  rw [integral_finsetSum Finset.univ fun j _ => (hf j).1.integrable (by norm_num)]
  exact Finset.sum_eq_zero fun j _ => (hf j).2

theorem dyadicMultilevelErrorField_joint_measurable {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (θ : RegressionParameter d) (hθ : Admissible C θ)
    (n J : ℕ) (y : ℝ) (m : ℕ → ℕ)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) :
    Measurable (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      dyadicMultilevelErrorField C θ n J y m t.1 t.2) := by
  classical
  refine Finset.measurable_sum Finset.univ fun (j : Fin (J + 1)) _ => ?_
  let R := m j.val + anchoredDimension d C.order + 1
  let H (w : Covariate d × Covariate d) (r : Fin R) :=
    dyadicIncrementKernel C θ j.val w.1 y (m j.val) (dyadicPilotRow j.val w.1 w.2) (r.val + 1)
  have hH (r : Fin R) : Measurable fun w => H w r :=
    dyadicIncrementKernel_field_measurable C θ hθ j.val y (m j.val) (r.val + 1) _ (dyadicPilotRow_field_measurable j.val)
  have hX (i : Fin n) : Measurable fun z : Fin n → Observation d =>
      incrementGlobalVector (ℓ := C.order) j.val (z i) - incrementGlobalMean θ j.val :=
    ((incrementGlobalVector_measurable j.val).comp (measurable_pi_apply i)).sub measurable_const
  have hexp : Measurable fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      LiftL2.centeredKernelExpansion 0 (H t.2) (fun i z => incrementGlobalVector j.val (z i) - incrementGlobalMean θ j.val) t.1 := by
    unfold LiftL2.centeredKernelExpansion LiftL2.kernelStatistic LiftL2.kernelSum
    simp only [zero_add]
    refine Finset.measurable_sum _ fun r _ => Measurable.const_mul (Finset.measurable_sum _ fun e _ => ?_) _
    have heval : Continuous fun p :
        ContinuousMultilinearMap ℝ (fun _ : Fin (r.val + 1) => Fin (Fintype.card (IncrementGlobalIndex d C.order j.val)) → ℝ) ℝ ×
          (Fin (r.val + 1) → Fin (Fintype.card (IncrementGlobalIndex d C.order j.val)) → ℝ) => p.1 p.2 := continuous_eval
    exact heval.measurable.comp (((hH r).comp measurable_snd).prodMk
      (measurable_pi_iff.mpr fun i => (hX (e i)).comp measurable_fst))
  have heq : (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
      LiftL2.centeredKernelExpansion 0 (H t.2)
        (fun i z => incrementGlobalVector j.val (z i) - incrementGlobalMean θ j.val) t.1) =
      fun t => dyadicPilotErrorField C θ n j.val y (m j.val) t.1 t.2 :=
    funext fun t => dyadicPolynomialPilot_centered_global C θ hθ n j.val t.2.1 y (m j.val)
      (dyadicPilotRow j.val t.2.1 t.2.2) (hdegree j) t.1
  rwa [heq] at hexp

end NearlyMinimax
