module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningBounds
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakConvergence
import Mathlib.Tactic.GCongr
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningValues
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakJetApprox

/-! # The weak flattening chain rule in every dimension

Classical chain rules hold for the normalized convolutions. Compact jet bounds
and almost-everywhere convergence pass their test identities to the original
flattening. The complementary-coordinate cutoffs then remove the origin.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter Set
open Metric

/- Smooth functions have the three classical punctured distributional identities. -/
theorem smooth_punctured_weak_identities {d } (H : XV d → ℝ)
    (hs : ContDiff ℝ (⊤ : ℕ∞) H)
    (test : XV d → ℝ) (ht : ContDiff ℝ 2 test) (hc : HasCompactSupport test)
    (hz : (0 : XV d) ∉ tsupport test) :
    (∀ i, (∫ q, H q * dx test q i) = -(∫ q, dx H q i * test q)) ∧
    (∀ i, (∫ q, H q * dv test q i) = -(∫ q, dv H q i * test q)) ∧
    (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, dvv H q i k * test q)) := by
  have hx (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun q => dx H q i) :=
    (hs.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hv (i : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun q => dv H q i) :=
    (hs.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hh (i k : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun q => dvv H q i k) :=
    ((hv k).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  exact classical_punctured_weak_from_jets H hs.continuous hs.contDiffOn
    (fun i => (hx i).continuous.locallyIntegrable)
    (fun i => (hv i).continuous.locallyIntegrable)
    (fun i k => (hh i k).continuous.locallyIntegrable) test ht hc hz

/- The literal flattened function has all weak test identities away from the origin. -/
theorem flatProfile_punctured_weak_of_profile {d alpha}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (test : XV d → ℝ) (ht : ContDiff ℝ 2 test) (hs : HasCompactSupport test)
    (hz : (0 : XV d) ∉ tsupport test) :
    (∀ i, (∫ q, selectedFlatProfile h r q * dx test q i) =
      -(∫ q, flatProfilePositionJet h r q i * test q)) ∧
    (∀ i, (∫ q, selectedFlatProfile h r q * dv test q i) =
      -(∫ q, flatProfileVelocityJet h r q i * test q)) ∧
    (∀ i k, (∫ q, selectedFlatProfile h r q * dvv test q i k) =
      (∫ q, flatProfileHessian h r q i k * test q)) := by
  let K := tsupport test
  obtain ⟨C, hC, hb⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ q ∈ K,
      ‖mollifiedFlatProfile h r n q‖ ≤ C ∧
      (∀ i, |dx (mollifiedFlatProfile h r n) q i| ≤ C) ∧
      (∀ i, |dv (mollifiedFlatProfile h r n) q i| ≤ C) ∧
      (∀ i k, |dvv (mollifiedFlatProfile h r n) q i k| ≤ C) := by
    obtain ⟨M, hM, he⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ∀ q ∈ K,
      ‖mollifiedProfile h n q‖ ≤ M ∧
      (∀ i, |dx (mollifiedProfile h n) q i| ≤ M) ∧
      (∀ i, |dv (mollifiedProfile h n) q i| ≤ M) ∧
      (∀ i k, |dvv (mollifiedProfile h n) q i k| ≤ M) := by
        have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
        have hmx := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.1
        have hmv := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.1
        have hmh := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.1
        have hb := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hsub : K ⊆ ({0}ᶜ : Set (XV d)) := by
          intro q hq
          change q ≠ 0
          intro he
          exact hz (he ▸ hq)
        obtain ⟨delta, hd, hdelta⟩ := hs.exists_cthickening_subset_open isOpen_compl_singleton hsub
        let L := cthickening delta K
        have hL : IsCompact L := hs.cthickening
        obtain ⟨MH, hMH⟩ := hL.exists_bound_of_continuousOn hH.continuousOn
        obtain ⟨MG, hMG⟩ := hb L hL (fun hmem => by simpa using hdelta hmem)
        let M := max 0 (max MH MG)
        have hM : 0 ≤ M := le_max_left _ _
        have hHM : MH ≤ M := (le_max_left _ _).trans (le_max_right _ _)
        have hGM : MG ≤ M := (le_max_right _ _).trans (le_max_right _ _)
        refine ⟨M, hM, ?_⟩
        have he : ∀ᶠ n in atTop, (standardMollifierSequence (G := XV d) n).rOut < delta :=
          standardMollifierSequence_rOut_tendsto.eventually (gt_mem_nhds hd)
        filter_upwards [he] with n hn
        intro q hq
        have hyL (y : XV d) (hy : y ∈ ball q (standardMollifierSequence n).rOut) : y ∈ L :=
          mem_cthickening_of_dist_le y q delta K hq ((mem_ball.mp hy).le.trans hn.le)
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact spatialMollify_norm_le_on_ball _ _ hH.aestronglyMeasurable M hM q
            (fun y hy => (hMH y (hyL y hy)).trans hHM)
        · intro i
          rw [dx_mollifiedProfile, ← Real.norm_eq_abs]
          apply spatialMollify_norm_le_on_ball _ _
            (((measurable_pi_apply i).comp hmx).aestronglyMeasurable) M hM q
          intro y hy
          exact (norm_le_pi_norm (profilePositionJet h y) i).trans ((hMG y (hyL y hy)).1.trans hGM)
        · intro i
          rw [dv_mollifiedProfile, ← Real.norm_eq_abs]
          apply spatialMollify_norm_le_on_ball _ _
            (((measurable_pi_apply i).comp hmv).aestronglyMeasurable) M hM q
          intro y hy
          exact (norm_le_pi_norm (profileVelocityJet h y) i).trans ((hMG y (hyL y hy)).2.1.trans hGM)
        · intro i k
          rw [dvv_mollifiedProfile, ← Real.norm_eq_abs]
          apply spatialMollify_norm_le_on_ball _ _ (hmh i k).aestronglyMeasurable M hM q
          intro y hy
          simpa only [Real.norm_eq_abs] using ((hMG y (hyL y hy)).2.2 i k).trans hGM

      /- The flattened values and all jets have one eventual bound on each punctured compact set. -/
    obtain ⟨P, hP, hp⟩ := flatteningPsi_deriv2_bound
    let B := 1 + |flatteningOffset| * Real.rpow r alpha + M
    let D := M + Real.rpow r (-alpha) * P * M ^ 2
    let C := max B D
    have hR : 0 ≤ Real.rpow r (-alpha) := (Real.rpow_pos_of_pos hr (-alpha)).le
    have hD : M ≤ D := le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg hR hP.le) (sq_nonneg M))
    have hDC : D ≤ C := le_max_right _ _
    have hBC : B ≤ C := le_max_left _ _
    refine ⟨C, hM.trans (hD.trans hDC), ?_⟩
    filter_upwards [he] with n hn
    intro q hq
    obtain ⟨hH, hx, hv, hh⟩ := hn q hq
    have hdiff := (contDiff_mollifiedProfile h n).differentiable (by simp) q
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hHabs : |mollifiedProfile h n q| ≤ M := by
        simpa only [Real.norm_eq_abs] using hH
      have hv : |mollifiedFlatProfile h r n q| ≤ B :=
        (abs_flatProfile_le (mollifiedProfile h n) alpha r hr q).trans
          (add_le_add_right hHabs _)
      simpa only [Real.norm_eq_abs] using hv.trans hBC
    · intro i
      unfold dx mollifiedFlatProfile
      rw [fderiv_flatProfile _ _ _ hr q hdiff]
      change |-deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
        dx (mollifiedProfile h n) q i| ≤ C
      exact (abs_flatSlope_mul_le _ _ M (hx i)).trans (hD.trans hDC)
    · intro i
      unfold dv mollifiedFlatProfile
      rw [fderiv_flatProfile _ _ _ hr q hdiff]
      change |-deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
        dv (mollifiedProfile h n) q i| ≤ C
      exact (abs_flatSlope_mul_le _ _ M (hv i)).trans (hD.trans hDC)
    · intro i k
      rw [mollifiedFlatProfile, dvv_flatProfile_of_contDiffAt _ _ _ hr q
        ((contDiff_mollifiedProfile h n).contDiffAt.of_le (by simp)) i k]
      exact (abs_flatSecond_le _ _ _ _ alpha r M P hr hM (hv i) (hv k) (hh i k)
        hP.le (hp _)).trans hDC
  have hnorm : ∀ᶠ n in atTop, ∀ q ∈ K, ‖mollifiedFlatProfile h r n q‖ ≤ C := by
    filter_upwards [hb] with n hn
    exact fun q hq => (hn q hq).1
  have _h_xinl_0 : ∀ᵐ q ∂volume, Tendsto (fun n => mollifiedFlatProfile h r n q) atTop (nhds (selectedFlatProfile h r q)) := by
    have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
    have hc : Continuous (fun s : ℝ => 1 - flatteningOffset * Real.rpow r alpha -
        Real.rpow r alpha * flatteningPsi (s / Real.rpow r alpha)) :=
      continuous_const.sub (continuous_const.mul
        (contDiff_flatteningPsi.continuous.comp (continuous_id.div_const _)))
    filter_upwards [spatialMollify_ae_tendsto _ hH.locallyIntegrable] with q hq
    exact hc.continuousAt.tendsto.comp hq
  have hvalue (t : XV d → ℝ) (hc : Continuous t) (hsc : HasCompactSupport t)
      (hsub : tsupport t ⊆ K) :
      Tendsto (fun n => ∫ q, mollifiedFlatProfile h r n q * t q) atTop
        (nhds (∫ q, selectedFlatProfile h r q * t q)) :=
    integral_mul_test_tendsto _ _
      (fun n => (contDiff_mollifiedFlatProfile h r n).continuous.aestronglyMeasurable)
      _h_xinl_0 t hc hsc K hsub C hC hnorm
  have hclassic (n : ℕ) := smooth_punctured_weak_identities _
    (contDiff_mollifiedFlatProfile h r n) test ht hs hz
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hleft := hvalue (fun q => dx test q i) (continuous_dx_test test ht i)
      (hs.fderiv_apply ℝ (Pi.single i 1, 0)) (tsupport_fderiv_apply_subset ℝ (Pi.single i 1, 0))
    have hbound : ∀ᶠ n in atTop, ∀ q ∈ K, ‖dx (mollifiedFlatProfile h r n) q i‖ ≤ C := by
      filter_upwards [hb] with n hn
      intro q hq
      simpa only [Real.norm_eq_abs] using (hn q hq).2.1 i
    have _h_xinl_0 : ∀ᵐ q ∂volume, Tendsto (fun n => dx (mollifiedFlatProfile h r n) q i) atTop (nhds (flatProfilePositionJet h r q i)) := by
      have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
      have hx := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i
      filter_upwards [spatialMollify_ae_tendsto _ hH.locallyIntegrable,
        spatialMollify_ae_tendsto _ hx] with q hq hg
      have hc := ((continuous_flatSlope alpha r).continuousAt.tendsto.comp hq).neg.mul hg
      convert hc using 1
      · funext n
        unfold dx mollifiedFlatProfile
        rw [fderiv_flatProfile _ _ _ hr q
          ((contDiff_mollifiedProfile h n).differentiable (by simp) q)]
        change -deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
            dx (mollifiedProfile h n) q i = _
        rw [dx_mollifiedProfile]
        rfl
      · rfl
    have hright := integral_mul_test_tendsto _ _
      (fun n => (measurable_fderiv_apply_const ℝ (mollifiedFlatProfile h r n)
        (Pi.single i 1, 0)).aestronglyMeasurable)
      _h_xinl_0 test ht.continuous hs K subset_rfl C hC hbound
    exact tendsto_nhds_unique (hleft.congr (fun n => (hclassic n).1 i)) hright.neg
  · intro i
    have hleft := hvalue (fun q => dv test q i) (continuous_dv_test test ht i)
      (hs.fderiv_apply ℝ (0, Pi.single i 1)) (tsupport_fderiv_apply_subset ℝ (0, Pi.single i 1))
    have hbound : ∀ᶠ n in atTop, ∀ q ∈ K, ‖dv (mollifiedFlatProfile h r n) q i‖ ≤ C := by
      filter_upwards [hb] with n hn
      intro q hq
      simpa only [Real.norm_eq_abs] using (hn q hq).2.2.1 i
    have _h_xinl_0 : ∀ᵐ q ∂volume, Tendsto (fun n => dv (mollifiedFlatProfile h r n) q i) atTop (nhds (flatProfileVelocityJet h r q i)) := by
      have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
      have hv := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i
      filter_upwards [spatialMollify_ae_tendsto _ hH.locallyIntegrable,
        spatialMollify_ae_tendsto _ hv] with q hq hg
      have hc := ((continuous_flatSlope alpha r).continuousAt.tendsto.comp hq).neg.mul hg
      convert hc using 1
      · funext n
        unfold dv mollifiedFlatProfile
        rw [fderiv_flatProfile _ _ _ hr q
          ((contDiff_mollifiedProfile h n).differentiable (by simp) q)]
        change -deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
            dv (mollifiedProfile h n) q i = _
        rw [dv_mollifiedProfile]
        rfl
      · rfl
    have hright := integral_mul_test_tendsto _ _
      (fun n => (measurable_fderiv_apply_const ℝ (mollifiedFlatProfile h r n)
        (0, Pi.single i 1)).aestronglyMeasurable)
      _h_xinl_0 test ht.continuous hs K subset_rfl C hC hbound
    exact tendsto_nhds_unique (hleft.congr (fun n => (hclassic n).2.1 i)) hright.neg
  · intro i k
    have hsub : tsupport (fun q => dvv test q i k) ⊆ K :=
      (tsupport_fderiv_apply_subset ℝ (0, Pi.single i 1)).trans
        (tsupport_fderiv_apply_subset ℝ (0, Pi.single k 1))
    have hleft := hvalue (fun q => dvv test q i k) (continuous_dvv_test test ht i k)
      ((hs.fderiv_apply ℝ (0, Pi.single k 1)).fderiv_apply ℝ (0, Pi.single i 1)) hsub
    have hbound : ∀ᶠ n in atTop, ∀ q ∈ K, ‖dvv (mollifiedFlatProfile h r n) q i k‖ ≤ C := by
      filter_upwards [hb] with n hn
      intro q hq
      simpa only [Real.norm_eq_abs] using (hn q hq).2.2.2 i k
    have _h_xinl_0 : ∀ᵐ q ∂volume, Tendsto (fun n => dvv (mollifiedFlatProfile h r n) q i k) atTop (nhds (flatProfileHessian h r q i k)) := by
      have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
      have hv := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hh := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i k
      filter_upwards [spatialMollify_ae_tendsto _ hH.locallyIntegrable,
        spatialMollify_ae_tendsto _ (hv i), spatialMollify_ae_tendsto _ (hv k),
        spatialMollify_ae_tendsto _ hh] with q hq hi hk hhq
      have hp := (continuous_flatSlope alpha r).continuousAt.tendsto.comp hq
      have hp2 := (continuous_flatSecond alpha r).continuousAt.tendsto.comp hq
      have hconst : Tendsto (fun _ : ℕ => Real.rpow r (-alpha)) atTop
          (nhds (Real.rpow r (-alpha))) := tendsto_const_nhds
      have hc := (hp.neg.mul hhq).sub (((hconst.mul hp2).mul hi).mul hk)
      convert hc using 1
      · funext n
        rw [mollifiedFlatProfile, dvv_flatProfile_of_contDiffAt _ _ _ hr q
          ((contDiff_mollifiedProfile h n).contDiffAt.of_le (by simp)) i k,
          dvv_mollifiedProfile, dv_mollifiedProfile, dv_mollifiedProfile]
        rfl
      · rfl
    have hright := integral_mul_test_tendsto _ _
      (fun n => (measurable_dvv (mollifiedFlatProfile h r n) i k).aestronglyMeasurable)
      _h_xinl_0
      test ht.continuous hs K subset_rfl C hC hbound
    exact tendsto_nhds_unique (hleft.congr (fun n => (hclassic n).2.2 i k)) hright

/- The literal flattened function has the three weak identities on the entire carrier. -/
theorem flatProfile_weak_of_profile {d } (hd : 1 ≤ d) {alpha }
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    ∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, selectedFlatProfile h r q * dx test q i) =
        -(∫ q, flatProfilePositionJet h r q i * test q)) ∧
      (∀ i, (∫ q, selectedFlatProfile h r q * dv test q i) =
        -(∫ q, flatProfileVelocityJet h r q i * test q)) ∧
      (∀ i k, (∫ q, selectedFlatProfile h r q * dvv test q i k) =
        (∫ q, flatProfileHessian h r q i k * test q)) := by
  obtain ⟨hx, hv, hh⟩ := flatProfile_jets_locallyIntegrable_of_profile h r hr
  exact profile_weak_identities_extend d hd (selectedFlatProfile h r)
    (flatProfilePositionJet h r) (flatProfileVelocityJet h r) (flatProfileHessian h r)
    (continuous_selectedFlatProfile h r) hx hv hh (flatProfile_punctured_weak_of_profile h r hr)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
