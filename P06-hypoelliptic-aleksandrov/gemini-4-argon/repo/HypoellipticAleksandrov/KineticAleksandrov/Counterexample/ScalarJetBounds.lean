module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarJetFormulas
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarHessianScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarRescaled
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHomogeneousBounds
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarCancellation
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarJetFields
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNormalized
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarMatching
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarTails

/-! # Genuine compact jet bounds for the scalar construction -/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics Set
open scoped Topology ContDiff

/- The source's cancelled position similarity factor. -/
def scalarPositionFactor (gamma : ScalarGamma) (Lam s : ℝ) : ℝ :=
  gamma.1 * F gamma Lam s - s / 3 * deriv (F gamma Lam) s

/- The cancelled position similarity factor is continuous. -/
theorem scalarGx_abs_rescaled (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) (q : XV 1) :
    |scalarGx gamma Lam q 0| =
      |scalarRescaled (scalarPositionFactor gamma Lam) (3 * gamma.1 - 3) q| := by
  rcases lt_trichotomy (q.1 0) 0 with hx | hx | hx
  · simp only [scalarGx, hx.ne, ↓reduceIte, scalarRescaled, not_lt.mpr hx.le, hx]
    rw [scalarProfile_dx_negative gamma Lam hLam q hx,
      scalarAnsatz_deriv_x_cancel gamma Lam _ _ hLam (neg_pos.mpr hx), abs_neg]
    simp only [scalarPositionFactor, show (3 * gamma.1 - 3) / 3 = gamma.1 - 1 by ring]
  · simp only [scalarGx, hx, ↓reduceIte, Pi.zero_apply, scalarRescaled, lt_self_iff_false]
  · simp only [scalarGx, hx.ne', ↓reduceIte, scalarRescaled, hx]
    rw [scalarProfile_dx_positive gamma Lam hLam q hx,
      scalarAnsatz_deriv_x_cancel gamma Lam _ _ hLam hx]
    simp only [scalarPositionFactor, show (3 * gamma.1 - 3) / 3 = gamma.1 - 1 by ring]

/- The absolute velocity jet equals the reflected first-derivative rescaling. -/
theorem scalarGv_abs_rescaled (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) (q : XV 1) :
    |scalarGv gamma Lam q 0| =
      |scalarRescaled (deriv (F gamma Lam)) (3 * gamma.1 - 1) q| := by
  rcases lt_trichotomy (q.1 0) 0 with hx | hx | hx
  · simp only [scalarGv, hx.ne, ↓reduceIte, scalarRescaled, not_lt.mpr hx.le, hx]
    have _h_xinl_1 : dv (scalarProfile gamma Lam) q 0 =
      -deriv (scalarAnsatz gamma Lam (-q.1 0)) (-q.2 0) := by
      rw [dv_eq_scalar_slice _ q
        ((scalarProfile_contDiffAt_off_axis gamma Lam hLam q hx.ne).differentiableAt
          (by norm_num))]
      have he : (fun v => scalarProfile gamma Lam (scalarVelocitySlice q v)) =
          fun v => scalarAnsatz gamma Lam (-q.1 0) (-v) := by
        funext v
        simp only [scalarVelocitySlice, scalarProfile, hx, not_lt.mpr hx.le, ↓reduceIte]
      rw [he]
      exact deriv_comp_neg _ _
    rw [_h_xinl_1,
      scalarAnsatz_deriv_v_power gamma Lam _ _ hLam (neg_pos.mpr hx)]
    simp only [neg_mul, neg_neg, show (3 * gamma.1 - 1) / 3 = gamma.1 - 1 / 3 by ring]
  · simp only [scalarGv, hx, ↓reduceIte, Pi.zero_apply, scalarRescaled, lt_self_iff_false]
  · simp only [scalarGv, hx.ne', ↓reduceIte, scalarRescaled, hx]
    have _h_xinl_7 : dv (scalarProfile gamma Lam) q 0 = deriv (scalarAnsatz gamma Lam (q.1 0)) (q.2 0) := by
        rw [dv_eq_scalar_slice _ q
          ((scalarProfile_contDiffAt_off_axis gamma Lam hLam q hx.ne').differentiableAt
            (by norm_num))]
        congr 1
        funext v
        simp only [scalarVelocitySlice, scalarProfile, hx, ↓reduceIte]

      /- The negative-position velocity selector has the exact reflected sign. -/
    rw [_h_xinl_7,
      scalarAnsatz_deriv_v_power gamma Lam _ _ hLam hx]
    simp only [neg_mul, abs_neg, show (3 * gamma.1 - 1) / 3 = gamma.1 - 1 / 3 by ring]

/- The absolute Hessian jet equals the reflected second-derivative rescaling. -/
theorem scalarHess_abs_rescaled (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (q : XV 1) : |scalarHess gamma Lam q 0 0| =
      |scalarRescaled (deriv (deriv (F gamma Lam))) (3 * gamma.1 - 2) q| := by
  rcases lt_trichotomy (q.1 0) 0 with hx | hx | hx
  · simp only [scalarHess, hx.ne, ↓reduceIte, scalarRescaled, not_lt.mpr hx.le, hx]
    rw [scalarProfile_dvv_negative gamma Lam hLam q hx,
      scalarAnsatz_deriv2_v_power gamma Lam _ _ hLam (neg_pos.mpr hx)]
    simp only [show (3 * gamma.1 - 2) / 3 = gamma.1 - 2 / 3 by ring]
  · simp only [scalarHess, hx, ↓reduceIte, Matrix.zero_apply, scalarRescaled,
      lt_self_iff_false]
  · simp only [scalarHess, hx.ne', ↓reduceIte, scalarRescaled, hx]
    rw [scalarProfile_dvv_positive gamma Lam hLam q hx,
      scalarAnsatz_deriv2_v_power gamma Lam _ _ hLam hx]
    simp only [show (3 * gamma.1 - 2) / 3 = gamma.1 - 2 / 3 by ring]

/- Native supremum norm in dimension one is exactly the sole scalar absolute value. -/
theorem scalar_vec_norm (v : PDE.Vec 1) : ‖v‖ = |v 0| := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg (v 0))).mpr
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact le_rfl
  · simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0

/- Both actual derivative rays can be used in the absolute-value rescaling bound. -/
theorem scalar_positive_power_to_abs (f : ℝ → ℝ) (beta )
    (ht : IsBigO atTop f (fun s => Real.rpow s beta)) :
    IsBigO atTop f (fun s => Real.rpow |s| beta) := by
  apply ht.congr' EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  simp only [abs_of_pos hs]

/- All scalar representative jets are uniformly bounded on compact sets away from zero. -/
theorem scalarJets_compact_bound (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (K : Set (XV 1)) (hK : IsCompact K) (hz : 0 ∉ K) :
    ∃ M : ℝ, ∀ q ∈ K, ‖scalarGx gamma Lam q‖ ≤ M ∧ ‖scalarGv gamma Lam q‖ ≤ M ∧
      ∀ i k, |scalarHess gamma Lam q i k| ≤ M := by
  have hf := F_contDiff_two gamma Lam hLam
  have hd : ContDiff ℝ 1 (deriv (F gamma Lam)) := hf.deriv'
  have hp : IsBigO atTop (deriv (F gamma Lam)) (fun s => Real.rpow s (3 * gamma.1 - 1)) ∧
    IsBigO atTop (deriv (deriv (F gamma Lam))) (fun s => Real.rpow s (3 * gamma.1 - 2)) := by
      have hj : IsBigO atTop (deriv (fun s => F gamma Lam s -
          Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1)))
          (fun s => Real.rpow s (3 * gamma.1 - 4)) ∧
        IsBigO atTop (deriv (deriv (fun s => F gamma Lam s -
          Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1))))
          (fun s => Real.rpow s (3 * gamma.1 - 5)) := by
          have hp := Fplus_tail_derivatives gamma Lam hLam
          have he (s : ℝ) (hs : 0 < s) : (fun t => Fplus gamma Lam t -
              Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1)) =ᶠ[𝓝 s]
              fun t => F gamma Lam t -
                Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1) := by
            filter_upwards [Ioi_mem_nhds hs] with t ht
            simp only [F, show 0 < t from ht, ↓reduceIte]
          constructor
          · apply hp.1.congr' _ EventuallyEq.rfl
            filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
            exact (he s hs).deriv_eq
          · apply hp.2.congr' _ EventuallyEq.rfl
            filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
            exact (he s hs).deriv.deriv_eq

        /- The actual reflected negative-ray remainder derivatives agree with the M branch. -/
      have hf := F_contDiff_two gamma Lam hLam
      constructor
      · exact scalar_isBigO_of_power_ratio _ _ _
          (scalar_deriv_tail_ratio _ _ _ hf hj.1)
      · exact scalar_isBigO_of_power_ratio _ _ _
          (scalar_deriv2_tail_ratio _ _ _ hf hj.2)

    /- Both actual derivative orders have their leading power bounds on the negative ray. -/
  have hn : IsBigO atBot (deriv (F gamma Lam)) (fun s => Real.rpow |s| (3 * gamma.1 - 1)) ∧
    IsBigO atBot (deriv (deriv (F gamma Lam)))
      (fun s => Real.rpow |s| (3 * gamma.1 - 2)) := by
    let f : ℝ → ℝ := fun s => F gamma Lam (-s)
    have hj : IsBigO atTop (deriv (fun s => F gamma Lam (-s) -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1)))
        (fun s => Real.rpow s (3 * gamma.1 - 4)) ∧
      IsBigO atTop (deriv (deriv (fun s => F gamma Lam (-s) -
        Real.rpow (9 * Lam) (-gamma.1) * Real.rpow s (3 * gamma.1))))
        (fun s => Real.rpow s (3 * gamma.1 - 5)) := by
        have hn := Fminus_negative_ray_tail_derivatives_of_M_jets
          Kummer.M_negative_expansion_jet gamma Lam hLam
        rw [scalar_matching_trace_coefficient gamma Lam hLam hmatch] at hn
        have he (s : ℝ) (hs : 0 < s) : (fun t => Fminus gamma Lam (-t) -
            Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1)) =ᶠ[𝓝 s]
            fun t => F gamma Lam (-t) -
              Real.rpow (9 * Lam) (-gamma.1) * Real.rpow t (3 * gamma.1) := by
          filter_upwards [Ioi_mem_nhds hs] with t ht
          simp only [F, neg_neg_of_pos (show 0 < t from ht),
            not_lt.mpr (neg_neg_of_pos (show 0 < t from ht)).le, ↓reduceIte]
        constructor
        · apply hn.1.congr' _ EventuallyEq.rfl
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
          exact (he s hs).deriv_eq
        · apply hn.2.congr' _ EventuallyEq.rfl
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
          exact (he s hs).deriv.deriv_eq

      /- A finite power-normalized limit gives the corresponding actual Big-O estimate. -/
    have hf : ContDiff ℝ 2 f := (F_contDiff_two gamma Lam hLam).comp contDiff_id.neg
    have h1 : IsBigO atTop (deriv f) (fun s => Real.rpow s (3 * gamma.1 - 1)) :=
      scalar_isBigO_of_power_ratio _ _ _ (scalar_deriv_tail_ratio f _ _ hf hj.1)
    have h2 : IsBigO atTop (deriv (deriv f)) (fun s => Real.rpow s (3 * gamma.1 - 2)) :=
      scalar_isBigO_of_power_ratio _ _ _ (scalar_deriv2_tail_ratio f _ _ hf hj.2)
    constructor
    · have hb := (h1.comp_tendsto tendsto_neg_atBot_atTop).neg_left
      apply hb.congr' _ _
      · exact Eventually.of_forall fun s => by
          simp only [f, Function.comp_def, deriv_comp_neg, neg_neg]
      · filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
        simp only [Function.comp_def, abs_of_neg hs]
    · have hb := h2.comp_tendsto tendsto_neg_atBot_atTop
      apply hb.congr' _ _
      · exact Eventually.of_forall fun s => by
          simp only [f, Function.comp_def, scalar_deriv2_comp_neg, neg_neg]
      · filter_upwards [eventually_lt_atBot (0 : ℝ)] with s hs
        simp only [Function.comp_def, abs_of_neg hs]
  have _h_inl_14 : Continuous (scalarPositionFactor gamma Lam) := by
    have hf := F_contDiff_two gamma Lam hLam
    exact continuous_const.mul hf.continuous |>.sub
      ((continuous_id.div_const 3).mul (hf.continuous_deriv (by norm_num)))
  have _h_xinl_0 : IsBigO atTop (fun s => gamma.1 * F gamma Lam s - s / 3 * deriv (F gamma Lam) s) (fun s => Real.rpow s (3 * gamma.1 - 3)) := by
    let c : ℝ := Real.rpow (9 * Lam) (-gamma.1)
    let E : ℝ → ℝ := fun s => Fplus gamma Lam s - c * Real.rpow s (3 * gamma.1)
    have hE := Fplus_asymptotic gamma Lam hLam
    have hdE := (Fplus_tail_derivatives gamma Lam hLam).1
    have hM := Kummer.rpow_mul_isBigO_of_add_eq (deriv E) 1 (3 * gamma.1 - 4)
      (3 * gamma.1 - 3) (by simpa only [E, c, Real.rpow_eq_pow] using hdE) (by ring)
    have hR : IsBigO atTop (fun s => gamma.1 * E s - (1 / 3 : ℝ) * (s * deriv E s))
        (fun s => Real.rpow s (3 * gamma.1 - 3)) := by
      have hM' : IsBigO atTop (fun s => s * deriv E s)
          (fun s => Real.rpow s (3 * gamma.1 - 3)) := by
        simpa only [Real.rpow_one] using hM
      exact (hE.const_mul_left gamma.1).sub (hM'.const_mul_left (1 / 3 : ℝ))
    apply hR.congr' _ (EventuallyEq.rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have he : F gamma Lam =ᶠ[𝓝 s] Fplus gamma Lam := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      simp only [F, show 0 < t from ht, ↓reduceIte]
    have hd : DifferentiableAt ℝ (Fplus gamma Lam) s :=
      ((F_contDiff_two gamma Lam hLam).differentiable (by norm_num) s).congr_of_eventuallyEq
        he.symm
    rw [he.eq_of_nhds, he.deriv_eq, scalar_power_cancellation _ gamma.1 c s hs hd]
    dsimp only [E]
    ring
  obtain ⟨Mx, hx⟩ := scalarRescaled_compact_bound (scalarPositionFactor gamma Lam)
    (3 * gamma.1 - 3) _h_inl_14
    (scalar_positive_power_to_abs _ _ _h_xinl_0)
    (F_position_cancellation_atBot gamma Lam hLam hmatch) K hK hz
  obtain ⟨Mv, hv⟩ := scalarRescaled_compact_bound (deriv (F gamma Lam)) (3 * gamma.1 - 1)
    hd.continuous (scalar_positive_power_to_abs _ _ hp.1) hn.1 K hK hz
  obtain ⟨Mh, hh⟩ := scalarRescaled_compact_bound (deriv (deriv (F gamma Lam)))
    (3 * gamma.1 - 2) hd.continuous_deriv_one
    (scalar_positive_power_to_abs _ _ hp.2) hn.2 K hK hz
  refine ⟨max Mx (max Mv Mh), ?_⟩
  intro q hq
  constructor
  · rw [scalar_vec_norm, scalarGx_abs_rescaled gamma Lam hLam]
    exact (hx q hq).trans (le_max_left _ _)
  constructor
  · rw [scalar_vec_norm, scalarGv_abs_rescaled gamma Lam hLam]
    exact (hv q hq).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro i k
    have hi : i = 0 := Subsingleton.elim _ _
    have hk : k = 0 := Subsingleton.elim _ _
    subst i k
    rw [scalarHess_abs_rescaled gamma Lam hLam]
    exact (hh q hq).trans ((le_max_right _ _).trans (le_max_right _ _))

/- Euclidean normalization in dimension one agrees with the scalar absolute value. -/
theorem scalar_vec_euclidean_norm (v : PDE.Vec 1) : PDE.vecEuclideanNorm v = |v 0| := by
  simp only [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot, Fin.sum_univ_one,
    ← sq, Real.sqrt_sq_eq_abs]

/- The selected velocity representative has the required global kinetic gradient bound. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
