module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Profile
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.GeometryHomogeneity
import Mathlib.Tactic.Linarith

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set Filter


/-- The total position derivative selectors are measurable, even at singular points. -/
theorem measurable_dx {d : ℕ} (H : XV d → ℝ) : Measurable (dx H) := by
  apply Measurable.of_eval
  intro i
  exact measurable_fderiv_apply_const ℝ H (Pi.single i 1, 0)

/-- The total velocity derivative selectors are measurable, even at singular points. -/
theorem measurable_dv {d : ℕ} (H : XV d → ℝ) : Measurable (dv H) := by
  apply Measurable.of_eval
  intro i
  exact measurable_fderiv_apply_const ℝ H (0, Pi.single i 1)

/-- The total second velocity derivative selectors are entrywise measurable. -/
theorem measurable_dvv {d : ℕ} (H : XV d → ℝ) (i k : Fin d) :
    Measurable (fun q => dvv H q i k) :=
  measurable_fderiv_apply_const ℝ (fun q => dv H q k) (0, Pi.single i 1)

/-- Smoothness off the origin gives smooth position derivative components there. -/
theorem contDiffAt_dx_off_origin {d : ℕ} (H : XV d → ℝ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)))
    (q : XV d) (hq : q ≠ 0) (i : Fin d) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => dx H z i) q := by
  exact ((hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq))).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const

/-- Smoothness off the origin gives smooth velocity derivative components there. -/
theorem contDiffAt_dv_off_origin {d : ℕ} (H : XV d → ℝ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)))
    (q : XV d) (hq : q ≠ 0) (i : Fin d) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => dv H z i) q := by
  exact ((hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq))).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const

/-- Smoothness off the origin gives smooth second velocity derivative components there. -/
theorem contDiffAt_dvv_off_origin {d : ℕ} (H : XV d → ℝ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)))
    (q : XV d) (hq : q ≠ 0) (i k : Fin d) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => dvv H z i k) q := by
  exact ((contDiffAt_dv_off_origin H hs q hq k).fderiv_right
    (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const


/-- All classical jet components are bounded on each compact set avoiding the origin. -/
theorem profile_jets_compact_bound {d : ℕ} (H : XV d → ℝ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)))
    (K : Set (XV d)) (hK : IsCompact K) (hz : 0 ∉ K) :
    ∃ M : ℝ, ∀ q ∈ K,
      ‖dx H q‖ ≤ M ∧ ‖dv H q‖ ≤ M ∧ ∀ i k, |dvv H q i k| ≤ M  := by
  have continuousOn_profile_jets :
      ContinuousOn (dx H) ({0}ᶜ : Set (XV d)) ∧
    ContinuousOn (dv H) ({0}ᶜ : Set (XV d)) ∧
    ContinuousOn (dvv H) ({0}ᶜ : Set (XV d)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      apply continuousWithinAt_pi.mpr
      intro i
      exact (contDiffAt_dx_off_origin H hs q (by simpa using hq) i).continuousAt.continuousWithinAt
    · intro q hq
      apply continuousWithinAt_pi.mpr
      intro i
      exact (contDiffAt_dv_off_origin H hs q (by simpa using hq) i).continuousAt.continuousWithinAt
    · intro q hq
      apply continuousWithinAt_pi.mpr
      intro i
      apply continuousWithinAt_pi.mpr
      intro k
      exact (contDiffAt_dvv_off_origin H hs q (by simpa using hq) i k).continuousAt.continuousWithinAt
  have hsub : K ⊆ ({0}ᶜ : Set (XV d)) := by
    intro q hq
    intro he
    subst q
    exact hz hq
  obtain ⟨Mx, hx⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_profile_jets).1.mono hsub)
  obtain ⟨Mv, hv⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_profile_jets).2.1.mono hsub)
  let B : XV d → (Fin d × Fin d → ℝ) := fun q ik => dvv H q ik.1 ik.2
  have hB : ContinuousOn B K := by
    intro q hq
    apply continuousWithinAt_pi.mpr
    intro ik
    exact (contDiffAt_dvv_off_origin H hs q (fun he => hz (he ▸ hq))
      ik.1 ik.2).continuousAt.continuousWithinAt
  obtain ⟨Mh, hh⟩ := hK.exists_bound_of_continuousOn hB
  refine ⟨max Mx (max Mv Mh), ?_⟩
  intro q hq
  refine ⟨(hx q hq).trans (le_max_left _ _),
    (hv q hq).trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro i k
  have hc' : |dvv H q i k| ≤ ‖B q‖ := by
    simpa using (norm_le_pi_norm (B q) (i, k))
  exact hc'.trans ((hh q hq).trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- Positive gauge comparability and smoothness away from zero imply continuity everywhere. -/
theorem continuous_profile_of_comparison {d : ℕ} (H : XV d → ℝ)
    (alpha c C : ℝ) (ha : 0 < alpha) (hc : 0 ≤ c) (hzero : H 0 = 0)
    (hcomp : ∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha)
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) : Continuous H := by
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hq : q = 0
  · subst q
    have hmajor : Continuous (fun q => C * Real.rpow (rho q) alpha) :=
      continuous_const.mul ((continuous_rho d).rpow_const (fun _ => Or.inr ha.le))
    have hm : Tendsto (fun q : XV d => C * Real.rpow (rho q) alpha) (nhds 0) (nhds 0) := by
      simpa [rho_zero, Real.rpow_eq_pow, Real.zero_rpow ha.ne'] using
        hmajor.tendsto 0
    simpa only [ContinuousAt, hzero] using (squeeze_zero (fun q => (mul_nonneg hc (Real.rpow_nonneg (rho_nonneg q) alpha)).trans (hcomp q).1) (fun q => (hcomp q).2) hm)
  · exact hsmooth.continuousOn.continuousAt
      (isOpen_compl_singleton.mem_nhds (by simpa using hq))



/-- Positive kinetic dilation preserves nonzero points. -/
theorem dilate_ne_zero {d : ℕ} (r : ℝ) (hr : 0 < r) (q : XV d) (hq : q ≠ 0) :
    dilate r q ≠ 0 := by
  intro hz
  have he := congrArg (dilate r⁻¹) hz
  rw [dilate_mul, inv_mul_cancel₀ hr.ne', dilate_one] at he
  exact hq (by simpa [dilate, Prod.mk_zero_zero] using he)

/-- The smooth homogeneous profile is differentiable at every nonzero point. -/
theorem differentiableAt_profile_off_origin {d : ℕ} (H : XV d → ℝ)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d))) (q : XV d) (hq : q ≠ 0) :
    DifferentiableAt ℝ H q :=
  (hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq))).differentiableAt
    (by simp)

/-- Differentiating kinetic homogeneity twice gives the Hessian degree alpha minus two. -/
theorem homogeneous_dvv_off_origin {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ)
    (hr : 0 < r) (hhom : ∀ q, H (dilate r q) = Real.rpow r alpha * H q)
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ : Set (XV d)))
    (q : XV d) (hq : q ≠ 0) (i k : Fin d) :
    dvv H (dilate r q) i k = Real.rpow r (alpha - 2) * dvv H q i k := by
  have hg :=
    (contDiffAt_dv_off_origin H hs q hq k).differentiableAt (by simp)
  have hgr :=
    (contDiffAt_dv_off_origin H hs _ (dilate_ne_zero r hr q hq) k).differentiableAt (by simp)
  have hloc : (fun z => dv H (dilate r z) k) =ᶠ[nhds q]
      (fun z => Real.rpow r (alpha - 1) * dv H z k) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hq] with z hz
    exact homogeneous_dv_identity H alpha r hr hhom z
      (differentiableAt_profile_off_origin H hs z hz)
      (differentiableAt_profile_off_origin H hs _ (dilate_ne_zero r hr z hz)) k
  have he := congrArg (fun L : XV d →L[ℝ] ℝ => L (0, Pi.single i 1)) hloc.fderiv_eq
  rw [fderiv_fun_comp q hgr (hasFDerivAt_dilate r q).differentiableAt,
    fderiv_const_mul hg, (hasFDerivAt_dilate r q).fderiv] at he
  have hw : dilate r ((0, Pi.single i 1) : XV d) = r • (0, Pi.single i 1) := by
    simp [dilate, Prod.smul_mk]
  simp [dilationLinearMap_apply, smul_apply] at he
  rw [hw, map_smul] at he
  change r * dvv H (dilate r q) i k = Real.rpow r (alpha - 1) * dvv H q i k at he
  simp at he ⊢
  rw [show alpha - 2 = (alpha - 1) - 1 by ring, Real.rpow_sub hr, Real.rpow_one,
    div_mul_eq_mul_div]
  apply (eq_div_iff hr.ne').mpr
  simpa only [mul_comm] using he

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

