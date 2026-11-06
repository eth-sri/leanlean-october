module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SignsRescaled
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SignsSeedTransport
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Cutoff
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffRescaling
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import PDEFoundation.Ambient.EuclideanNorm
import PDEFoundation.Geometry.EuclideanBall.Topology
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffRadial
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Hessian sign control for the actual Appendix C cutoff -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open scoped BigOperators

/- The velocity Hessian quadratic form of the actual cutoff. -/
def cutoffHessian {d : ℕ} (alpha C₀ sigma R : ℝ) (y e w : PDE.Vec d) : ℝ :=
  fderiv ℝ (fun z => fderiv ℝ (fun a => cutoffProfile alpha C₀ sigma R a e) z w) y w

/- Two locally equal functions have equal scalar second directional derivatives. -/
theorem hessian_eq_of_eventuallyEq {d : ℕ} (F G : PDE.Vec d → ℝ)
    (y w u : PDE.Vec d) (h : F =ᶠ[nhds y] G) :
    fderiv ℝ (fun z => fderiv ℝ F z w) y u =
      fderiv ℝ (fun z => fderiv ℝ G z w) y u := by
  have hh : (fun z => fderiv ℝ F z w) =ᶠ[nhds y] (fun z => fderiv ℝ G z w) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with z hz
    exact congrArg (fun L => L w) hz
  exact congrArg (fun L => L u) (hh.fderiv_eq (𝕜 := ℝ))

/- The actual cutoff has the seed Hessian in the open inner ball. -/
theorem cutoffHessian_eq_seed {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (y e w : PDE.Vec d) (hy : PDE.vecEuclideanNorm y < R) :
    cutoffHessian alpha C₀ sigma R y e w =
      fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w) y w := by
  apply hessian_eq_of_eventuallyEq
  filter_upwards [PDE.continuous_vecEuclideanNorm.continuousAt.eventually_lt_const hy]
    with z hz
  exact cutoffProfile_eq_seed alpha C₀ sigma R hR z e hz.le

/- The actual cutoff has the radial Hessian in the open outer region. -/
theorem cutoffHessian_eq_radial {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (y e w : PDE.Vec d) (hy : 2 * R < PDE.vecEuclideanNorm y) :
    cutoffHessian alpha C₀ sigma R y e w =
      fderiv ℝ (fun z => fderiv ℝ (radialProfile alpha) z w) y w := by
  apply hessian_eq_of_eventuallyEq
  filter_upwards [PDE.continuous_vecEuclideanNorm.continuousAt.eventually_const_lt hy]
    with z hz
  exact cutoffProfile_eq_radial alpha C₀ sigma R hR z e hz.le

/- For sufficiently large R the actual cutoff has both Hessian signs on its closed annulus. -/
theorem eventually_cutoff_annulus_signs (d : ℕ) (hd : 2 ≤ d) (alpha C₀ sigma : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hsigma : 0 < sigma) :
    ∀ᶠ R : ℝ in Filter.atTop, 2 < R ∧ ∀ y e : PDE.Vec d,
      PDE.vecNormSq e = 1 → R ≤ PDE.vecEuclideanNorm y →
      PDE.vecEuclideanNorm y ≤ 2 * R →
      (∃ w, 0 < cutoffHessian alpha C₀ sigma R y e w) ∧
      (∃ w, cutoffHessian alpha C₀ sigma R y e w < 0) := by
  have _h_xinl_1 : ∀ᶠ R : ℝ in Filter.atTop, ∀ e z, (e, z) ∈ cutoffAnnulus d →
      (∃ w, 0 < rescaledHessian alpha sigma (C₀ / Real.rpow R alpha) R⁻¹ e z w) ∧
      (∃ w, rescaledHessian alpha sigma (C₀ / Real.rpow R alpha) R⁻¹ e z w < 0) := by
    obtain ⟨U, hU, hzero, hsign⟩ : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, 0) ∈ U ∧
        ∀ e z, (e, z) ∈ cutoffAnnulus d → ∀ p ∈ U,
          (∃ w, 0 < rescaledHessian alpha sigma p.1 p.2 e z w) ∧
          (∃ w, rescaledHessian alpha sigma p.1 p.2 e z w < 0) := by
        have _h_xinl_1 : IsCompact (cutoffAnnulus d) := by
          have hclosed : IsClosed (cutoffAnnulus d) := by
            exact (isClosed_eq (PDE.continuous_vecNormSq.comp continuous_fst) continuous_const).inter
              ((isClosed_le continuous_const (PDE.continuous_vecEuclideanNorm.comp continuous_snd)).inter
                (isClosed_le (PDE.continuous_vecEuclideanNorm.comp continuous_snd) continuous_const))
          apply (isCompact_closedBall (0 : PDE.Vec d × PDE.Vec d) 2).of_isClosed_subset hclosed
          intro q hq
          rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
          have he : PDE.vecEuclideanNorm q.1 = 1 := by
            unfold PDE.vecEuclideanNorm
            rw [hq.1]
            norm_num
          exact max_le ((PDE.norm_le_vecEuclideanNorm _).trans (by linarith))
            ((PDE.norm_le_vecEuclideanNorm _).trans hq.2.2)
        have _h_xinl_0 : IsOpen (rescaledSignRegion d alpha sigma) := by
          apply isOpen_iff_mem_nhds.mpr
          intro q hq
          obtain ⟨hz, hb, ⟨wp, hp⟩, ⟨wn, hn⟩⟩ := hq
          have hc : Continuous (fun p : (PDE.Vec d × PDE.Vec d) × (ℝ × ℝ) =>
              ((p.2.1, p.2.2, p.1.1), p.1.2)) := by fun_prop
          have hpos := (continuousAt_rescaledCutoff_hessian alpha sigma
            ((q.2.1, q.2.2, q.1.1), q.1.2) hz hb wp wp).comp_of_eq hc.continuousAt rfl
          have hneg := (continuousAt_rescaledCutoff_hessian alpha sigma
            ((q.2.1, q.2.2, q.1.1), q.1.2) hz hb wn wn).comp_of_eq hc.continuousAt rfl
          have hbase : Continuous (fun p : (PDE.Vec d × PDE.Vec d) × (ℝ × ℝ) =>
              seedBase (p.2.2 * sigma) p.1.2 (p.2.2 • p.1.1)) := by
            unfold seedBase PDE.vecNormSq PDE.vecDot
            fun_prop
          have hvel : Continuous (fun p : (PDE.Vec d × PDE.Vec d) × (ℝ × ℝ) => p.1.2) := by
            fun_prop
          filter_upwards [hvel.continuousAt.eventually_ne hz, hbase.continuousAt.eventually_ne hb,
            hpos.eventually_const_lt hp, hneg.eventually_lt_const hn] with p hpz hpb hpp hpn
          exact ⟨hpz, hpb, ⟨wp, hpp⟩, ⟨wn, hpn⟩⟩
        obtain ⟨_, U, _, hU, hK, hzero, hsub⟩ := generalized_tube_lemma
          _h_xinl_1 (isCompact_singleton (x := (0, 0)))
          _h_xinl_0
          (cutoffAnnulus_zero_signs d hd alpha sigma ha ha1)
        refine ⟨U, hU, hzero (Set.mem_singleton _), ?_⟩
        intro e z hz p hp
        exact (hsub (a := ((e, z), p)) ⟨hK hz, hp⟩).2.2

      /- The source parameters enter the uniform sign neighborhood for every sufficiently large R. -/
    have ht : Filter.Tendsto (fun R : ℝ => R⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    have hs : Filter.Tendsto (fun R : ℝ => C₀ / Real.rpow R alpha)
        Filter.atTop (nhds 0) := by
      have hh := (tendsto_rpow_neg_atTop ha).const_mul C₀
      simp only [mul_zero] at hh
      apply hh.congr'
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
      simp only [Real.rpow_eq_pow, Real.rpow_neg hR, div_eq_mul_inv]
    have hp := hs.prodMk_nhds ht
    filter_upwards [hp.eventually (hU.mem_nhds hzero)] with R hR
    intro e z hz
    exact hsign e z hz (C₀ / Real.rpow R alpha, R⁻¹) hR
  filter_upwards [_h_xinl_1,
    Filter.eventually_gt_atTop (2 : ℝ)] with R hsign hR2
  have hR : 0 < R := lt_trans (by norm_num) hR2
  refine ⟨hR2, ?_⟩
  intro y e he hyR hy2R
  let z := R⁻¹ • y
  have hnorm : PDE.vecEuclideanNorm z = PDE.vecEuclideanNorm y / R := by
    simp only [z, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hR),
      div_eq_mul_inv, mul_comm]
  have hz : (e, z) ∈ cutoffAnnulus d := by
    refine ⟨he, ?_, ?_⟩
    · rw [hnorm]
      exact (le_div_iff₀ hR).mpr (by simpa using hyR)
    · rw [hnorm]
      exact (div_le_iff₀ hR).mpr (by simpa only [mul_comm] using hy2R)
  have hRz : R • z = y := by
    dsimp [z]
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hp : 0 < (Real.rpow R alpha)⁻¹ * R ^ 2 :=
    mul_pos (inv_pos.mpr (Real.rpow_pos_of_pos hR _)) (sq_pos_of_pos hR)
  obtain ⟨⟨wp, hwp⟩, ⟨wn, hwn⟩⟩ := hsign e z hz
  have hh (w : PDE.Vec d) : rescaledHessian alpha sigma
      (C₀ / Real.rpow R alpha) R⁻¹ e z w =
      (Real.rpow R alpha)⁻¹ * R ^ 2 * cutoffHessian alpha C₀ sigma R y e w := by
    unfold rescaledHessian cutoffHessian
    rw [rescaledCutoff_hessian alpha C₀ sigma R hsigma hR, hRz]
  refine ⟨⟨wp, ?_⟩, ⟨wn, ?_⟩⟩
  · rw [hh] at hwp
    exact (mul_pos_iff_of_pos_left hp).mp hwp
  · rw [hh] at hwn
    by_contra hh
    exact (mul_nonneg hp.le (le_of_not_gt hh)).not_gt hwn

/- The actual cutoff has a positive Hessian direction everywhere, once R is large. -/
theorem eventually_cutoff_negative_direction (d : ℕ) (hd : 2 ≤ d)
    (alpha C₀ sigma : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) (hsigma : 0 < sigma)
    (hsq : sigma ^ 2 < (1 - alpha) / 16) :
    ∀ᶠ R : ℝ in Filter.atTop, 2 < R ∧ ∀ y e : PDE.Vec d,
      PDE.vecNormSq e = 1 → 1 / 4 < PDE.vecEuclideanNorm (y - e) →
      ∃ w, cutoffHessian alpha C₀ sigma R y e w < 0 := by
  filter_upwards [eventually_cutoff_annulus_signs d hd alpha C₀ sigma ha ha1 hsigma]
    with R hR
  have hR0 : 0 < R := lt_trans (by norm_num) hR.1
  refine ⟨hR.1, ?_⟩
  intro y e he hyseed
  by_cases hy : PDE.vecEuclideanNorm y < R
  · have hnorm := PDE.vecEuclideanNorm_nonneg (y - e)
    have hsqnorm := PDE.vecEuclideanNorm_sq (y - e)
    have hlow : (1 / 16 : ℝ) < PDE.vecNormSq (y - e) := by nlinarith
    have hthreshold : sigma ^ 2 < (1 - alpha) * PDE.vecNormSq (y - e) := by
      have hh := mul_lt_mul_of_pos_left hlow (sub_pos.mpr ha1)
      linarith
    obtain ⟨w, hw⟩ : ∃ w : PDE.Vec d,
      fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w) y w < 0 := by
        refine ⟨y - e, ?_⟩
        rw [seed_hessian_radial alpha C₀ sigma hsigma]
        have hn : 0 < PDE.vecNormSq (y - e) := by
          by_contra h
          have hzero : PDE.vecNormSq (y - e) = 0 :=
            le_antisymm (le_of_not_gt h) (PDE.vecNormSq_nonneg _)
          rw [hzero, mul_zero] at hthreshold
          exact (sq_nonneg sigma).not_gt hthreshold
        have _h_xinl_0 : seedRadialEigenvalue alpha sigma y e < 0 ↔ sigma ^ 2 < (1 - alpha) * PDE.vecNormSq (y - e) := by
          unfold seedRadialEigenvalue
          have hp := mul_pos ha
            (Real.rpow_pos_of_pos (seedBase_pos sigma hsigma y e) (alpha / 2 - 2))
          simp only [Real.rpow_eq_pow]
          rw [mul_neg_iff]
          simp only [hp, hp.not_gt, true_and, false_and, or_false, sub_neg]
        exact mul_neg_of_neg_of_pos
          (_h_xinl_0.mpr hthreshold) hn

      /- A point in the small source seed ball has a uniformly positive position dot product. -/
    exact ⟨w, by rwa [cutoffHessian_eq_seed alpha C₀ sigma R hR0 y e w hy]⟩
  · by_cases houter : 2 * R < PDE.vecEuclideanNorm y
    · have hy0 : y ≠ 0 := by
        intro hzero
        rw [PDE.vecEuclideanNorm_eq_zero_iff.mpr hzero] at houter
        linarith
      refine ⟨y, ?_⟩
      rw [cutoffHessian_eq_radial alpha C₀ sigma R hR0 y e y houter,
        radialProfile_hessian alpha y y y hy0]
      exact radialHessian_radial_neg alpha ha ha1 y hy0
    · exact (hR.2 y e he (le_of_not_gt hy) (le_of_not_gt houter)).2

/- Source sign control for the actual cutoff, with all parameters chosen internally. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
