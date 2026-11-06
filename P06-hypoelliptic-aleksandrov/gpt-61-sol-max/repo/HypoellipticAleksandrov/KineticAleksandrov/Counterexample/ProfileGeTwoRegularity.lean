module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Profile
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import PDEFoundation.Calculus.RegularityOrder


/-! # Regularity of the higher-dimensional profile witnesses -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set Filter

variable {d : ℕ} (H : XV d → ℝ)

/-- The total position derivative selectors are measurable, even at singular points. -/
theorem measurable_dx  : Measurable (dx H) := by
  apply Measurable.of_eval
  intro i
  exact measurable_fderiv_apply_const ℝ H (Pi.single i 1, 0)

/-- The total velocity derivative selectors are measurable, even at singular points. -/
theorem measurable_dv  : Measurable (dv H) := by
  apply Measurable.of_eval
  intro i
  exact measurable_fderiv_apply_const ℝ H _

/-- The total second velocity derivative selectors are entrywise measurable. -/
theorem measurable_dvv  (i k : Fin d) :
    Measurable (fun q => dvv H q i k) :=
  measurable_fderiv_apply_const ℝ (fun q => dv H q k) _

variable (hs : ContDiffOn ℝ PDE.smoothOrder H ({0}ᶜ : Set (XV d)))

variable (q : XV d) (hq : q ≠ 0)

section
variable (i : Fin d)

include hs hq
/-- Smoothness off the origin gives smooth position derivative components there. -/
theorem contDiffAt_dx_off_origin

      :
    ContDiffAt ℝ PDE.smoothOrder (fun z => dx H z i) q := ((hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq))).fderiv_right (m := PDE.smoothOrder) (by simp)).clm_apply contDiffAt_const

/-- Smoothness off the origin gives smooth velocity derivative components there. -/
theorem contDiffAt_dv_off_origin

      :
    ContDiffAt ℝ PDE.smoothOrder (fun z => dv H z i) q := ((hs.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hq))).fderiv_right (m := PDE.smoothOrder) (by simp)).clm_apply contDiffAt_const
end


include hs hq in
/-- Smoothness off the origin gives smooth second velocity derivative components there. -/
theorem contDiffAt_dvv_off_origin

     (i k : Fin d) :
    ContDiffAt ℝ PDE.smoothOrder (fun z => dvv H z i k) q := ((contDiffAt_dv_off_origin H hs q hq k).fderiv_right
    (m := PDE.smoothOrder) (by simp)).clm_apply contDiffAt_const

include hs in
/-- The full first derivative vectors are continuous away from the origin. -/
theorem continuousOn_profile_jets
     :
    ContinuousOn (dx H) ({0}ᶜ : Set (XV d)) ∧
    ContinuousOn (dv H) ({0}ᶜ : Set (XV d)) ∧
    ContinuousOn (dvv H) ({0}ᶜ : Set (XV d)) := (⟨fun q hq =>
  continuousWithinAt_pi.mpr fun i =>
    ContinuousAt.continuousWithinAt (ContDiffAt.continuousAt (contDiffAt_dx_off_origin H hs q hq i)),
  ⟨fun q hq =>
    continuousWithinAt_pi.mpr fun i =>
      ContinuousAt.continuousWithinAt (ContDiffAt.continuousAt (contDiffAt_dv_off_origin H hs q hq i)),
    fun q hq =>
    continuousWithinAt_pi.mpr fun i =>
      continuousWithinAt_pi.mpr fun k =>
        ContinuousAt.continuousWithinAt (ContDiffAt.continuousAt (contDiffAt_dvv_off_origin H hs q hq i k))⟩⟩)

include hs in
/-- All classical jet components are bounded on each compact set avoiding the origin. -/
theorem profile_jets_compact_bound

    (K : Set (XV d)) (hK : IsCompact K) (hz : 0 ∉ K) :
    ∃ M : ℝ, ∀ q ∈ K,
      ‖dx H q‖ ≤ M ∧ ‖dv H q‖ ≤ M ∧ ∀ i k, |dvv H q i k| ≤ M := by
  have hsub : K ⊆ ({0}ᶜ : Set (XV d)) := by
    intro q hq
    change q ≠ 0
    intro he
    subst q
    exact hz hq
  obtain ⟨Mx, hx⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_profile_jets H hs).1.mono hsub)
  obtain ⟨Mv, hv⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_profile_jets H hs).2.1.mono hsub)
  let B : XV d → (Fin d × Fin d → ℝ) := fun q ik => dvv H q ik.1 ik.2

  obtain ⟨Mh, hh⟩ := hK.exists_bound_of_continuousOn (show ContinuousOn B K by
      intro q hq
      apply continuousWithinAt_pi.mpr
      intro ik
      exact (contDiffAt_dvv_off_origin H hs q (fun he => hz (he ▸ hq))
        ik.1 ik.2).continuousAt.continuousWithinAt)
  refine ⟨max Mx (max Mv Mh), ?_⟩
  intro q hq
  refine ⟨(hx q hq).trans (le_max_left _ _),
    (hv q hq).trans ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro i k


  exact (show |dvv H q i k| ≤ ‖B q‖ by
      exact (norm_le_pi_norm (B q) (i, k))).trans ((hh q hq).trans ((le_max_right _ _).trans (le_max_right _ _)))

/-- Positive gauge comparability and smoothness away from zero imply continuity everywhere. -/
theorem continuous_profile_of_comparison
    (alpha c C : ℝ) (ha : 0 < alpha) (hc : 0 ≤ c) (hzero : H 0 = 0)
    (hcomp : ∀ q, c * Real.rpow (rho q) alpha ≤ H q ∧
      H q ≤ C * Real.rpow (rho q) alpha)
    (hsmooth : ContDiffOn ℝ PDE.smoothOrder H ({0}ᶜ : Set (XV d))) : Continuous H := by
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hq : q = 0
  · subst q


    have hz := squeeze_zero (fun q =>
      (mul_nonneg hc (Real.rpow_nonneg (rho_nonneg q) alpha)).trans (hcomp q).1)
      (fun q => (hcomp q).2) (by
          simpa only [rho_zero, Real.rpow_eq_pow, Real.zero_rpow ha.ne', mul_zero] using
            (show Continuous (fun q : XV d => C * Real.rpow (rho q) alpha) from continuous_const.mul ((continuous_rho d).rpow_const (fun _ => Or.inr ha.le))).tendsto 0)
    simpa only [ContinuousAt, hzero] using hz
  · exact hsmooth.continuousOn.continuousAt
      (isOpen_compl_singleton.mem_nhds (hq))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
