module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffRescaling
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Signs
import Mathlib.Tactic.FieldSimp
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffScaling

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The velocity Hessian quadratic form of the rescaled interpolation. -/
def rescaledHessian {d : ℕ} (alpha sigma s t : ℝ) (e z w : PDE.Vec d) : ℝ :=
  fderiv ℝ (fun a => fderiv ℝ (rescaledCutoff alpha sigma s t e) a w) z w











/-- Increasing the additive seed constant has exactly the source's transport effect. -/
theorem ansatzTransport_seed_shift {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e : PDE.Vec d) :
    ansatzTransport alpha (seed alpha C₀ sigma) y e =
      ansatzTransport alpha (seed alpha 0 sigma) y e +
        PDE.vecDot y e * (alpha / 3 * C₀) := by
  rw [ansatzTransport_seed alpha C₀ sigma hsigma, ansatzTransport_seed alpha 0 sigma hsigma]
  unfold seed
  ring




/-- The velocity Hessian quadratic form of the actual cutoff. -/
def cutoffHessian {d : ℕ} (alpha C₀ sigma R : ℝ) (y e w : PDE.Vec d) : ℝ :=
  fderiv ℝ (fun z => fderiv ℝ (fun a => cutoffProfile alpha C₀ sigma R a e) z w) y w

/-- Two locally equal functions have equal scalar second directional derivatives. -/
theorem hessian_eq_of_eventuallyEq {d : ℕ} (F G : PDE.Vec d → ℝ)
    (y w u : PDE.Vec d) (h : F =ᶠ[nhds y] G) :
    fderiv ℝ (fun z => fderiv ℝ F z w) y u =
      fderiv ℝ (fun z => fderiv ℝ G z w) y u := by
  have hh : (fun z => fderiv ℝ F z w) =ᶠ[nhds y] (fun z => fderiv ℝ G z w) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with z hz
    exact congrArg (fun L => L w) hz
  exact congrArg (fun L => L u) (hh.fderiv_eq (𝕜 := ℝ))

/-- The actual cutoff has the seed Hessian in the open inner ball. -/
theorem cutoffHessian_eq_seed {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (y e w : PDE.Vec d) (hy : PDE.vecEuclideanNorm y < R) :
    cutoffHessian alpha C₀ sigma R y e w =
      fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w) y w := by
  apply hessian_eq_of_eventuallyEq
  filter_upwards [PDE.continuous_vecEuclideanNorm.continuousAt.eventually_lt_const hy]
    with z hz
  exact cutoffProfile_eq_seed alpha C₀ sigma R hR z e hz.le

/-- The actual cutoff has the radial Hessian in the open outer region. -/
theorem cutoffHessian_eq_radial {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (y e w : PDE.Vec d) (hy : 2 * R < PDE.vecEuclideanNorm y) :
    cutoffHessian alpha C₀ sigma R y e w =
      fderiv ℝ (fun z => fderiv ℝ (radialProfile alpha) z w) y w := by
  apply hessian_eq_of_eventuallyEq
  filter_upwards [PDE.continuous_vecEuclideanNorm.continuousAt.eventually_const_lt hy]
    with z hz
  exact cutoffProfile_eq_radial alpha C₀ sigma R hR z e hz.le



/-- The transport expression agrees with the seed throughout the open inner ball. -/
theorem cutoffTransport_eq_seed {d : ℕ} (alpha C₀ sigma R : ℝ) (hR : 0 < R)
    (y e : PDE.Vec d) (hy : PDE.vecEuclideanNorm y < R) :
    ansatzTransport alpha (cutoffProfile alpha C₀ sigma R) y e =
      ansatzTransport alpha (seed alpha C₀ sigma) y e := by
  have hvel : (fun z => cutoffProfile alpha C₀ sigma R z e) =ᶠ[nhds y]
      (fun z => seed alpha C₀ sigma z e) := by
    filter_upwards [PDE.continuous_vecEuclideanNorm.continuousAt.eventually_lt_const hy]
      with z hz
    exact cutoffProfile_eq_seed alpha C₀ sigma R hR z e hz.le
  have hsphere : (fun z => cutoffProfile alpha C₀ sigma R y z) =
      (fun z => seed alpha C₀ sigma y z) := by
    funext z
    exact cutoffProfile_eq_seed alpha C₀ sigma R hR y z hy.le
  unfold ansatzTransport
  rw [cutoffProfile_eq_seed alpha C₀ sigma R hR y e hy.le, hvel.fderiv_eq, hsphere]


/-- Source sign control for the actual cutoff, with all parameters chosen internally. -/
theorem exists_cutoff_sign_parameters (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C₀ sigma R : ℝ, 0 < C₀ ∧ 0 < sigma ∧ 2 < R ∧
      ∀ y e : PDE.Vec d, PDE.vecNormSq e = 1 →
        (∃ w, 0 < cutoffHessian alpha C₀ sigma R y e w) ∧
        ((∃ w, cutoffHessian alpha C₀ sigma R y e w < 0) ∨
          1 ≤ ansatzTransport alpha (cutoffProfile alpha C₀ sigma R) y e)      := by
  have eventually_cutoff_annulus_signs (alpha C₀ sigma : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) (hsigma : 0 < sigma) :
      ∀ᶠ R : ℝ in Filter.atTop, 2 < R ∧ ∀ y e : PDE.Vec d,
      PDE.vecNormSq e = 1 → R ≤ PDE.vecEuclideanNorm y →
      PDE.vecEuclideanNorm y ≤ 2 * R →
      (∃ w, 0 < cutoffHessian alpha C₀ sigma R y e w) ∧
      (∃ w, cutoffHessian alpha C₀ sigma R y e w < 0) := by
    let rescaledSignRegion (alpha : ℝ) (sigma : ℝ) : Set ((PDE.Vec d × PDE.Vec d) × (ℝ × ℝ)) :=
      {q | q.1.2 ≠ 0 ∧ seedBase (q.2.2 * sigma) q.1.2 (q.2.2 • q.1.1) ≠ 0 ∧
          (∃ w, 0 < rescaledHessian alpha sigma q.2.1 q.2.2 q.1.1 q.1.2 w) ∧
          (∃ w, rescaledHessian alpha sigma q.2.1 q.2.2 q.1.1 q.1.2 w < 0)}
    let cutoffAnnulus : Set (PDE.Vec d × PDE.Vec d) :=
      {q | PDE.vecNormSq q.1 = 1 ∧ 1 ≤ PDE.vecEuclideanNorm q.2 ∧
          PDE.vecEuclideanNorm q.2 ≤ 2}
    have eventually_rescaled_annulus_signs (alpha C₀ sigma : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
        ∀ᶠ R : ℝ in Filter.atTop, ∀ e z, (e, z) ∈ cutoffAnnulus →
        (∃ w, 0 < rescaledHessian alpha sigma (C₀ / Real.rpow R alpha) R⁻¹ e z w) ∧
        (∃ w, rescaledHessian alpha sigma (C₀ / Real.rpow R alpha) R⁻¹ e z w < 0) := by
      have exists_rescaled_sign_neighborhood (alpha : ℝ) (sigma : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
          ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (0, 0) ∈ U ∧
          ∀ e z, (e, z) ∈ cutoffAnnulus → ∀ p ∈ U,
            (∃ w, 0 < rescaledHessian alpha sigma p.1 p.2 e z w) ∧
            (∃ w, rescaledHessian alpha sigma p.1 p.2 e z w < 0) := by
        have cutoffAnnulus_zero_signs :
            cutoffAnnulus ×ˢ ({(0, 0)} : Set (ℝ × ℝ)) ⊆ rescaledSignRegion alpha sigma := by
          rintro ⟨⟨e, z⟩, p⟩ ⟨hz, hp⟩
          have hp0 : p = (0, 0) := Set.mem_singleton_iff.mp hp
          subst p
          have hz0 : z ≠ 0 := by
            intro hzero
            have hh := hz.2.1
            simp [hzero, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot] at hh
            norm_num at hh
          have hbase : seedBase (0 * sigma) z ((0 : ℝ) • e) ≠ 0 := by
            simpa [seedBase] using PDE.vecNormSq_eq_zero_iff.not.mpr hz0
          have heq : rescaledCutoff alpha sigma 0 0 e = radialProfile alpha := by
            funext a
            exact rescaledCutoff_zero alpha sigma e a
          have hh (w : PDE.Vec d) : rescaledHessian alpha sigma 0 0 e z w =
              radialHessianForm alpha z w w := by
            unfold rescaledHessian
            rw [heq, radialProfile_hessian alpha z w w hz0]
          obtain ⟨w, hw⟩ := radialHessian_positive_direction d hd alpha ha z hz0
          change z ≠ 0 ∧ seedBase (0 * sigma) z (0 • e) ≠ 0 ∧ _
          refine ⟨hz0, hbase, ⟨w, ?_⟩, ⟨z, ?_⟩⟩
          · rw [hh]
            exact hw
          · rw [hh]
            exact radialHessian_radial_neg alpha ha ha1 z hz0
        have isOpen_rescaledSignRegion :
            IsOpen (rescaledSignRegion alpha sigma) := by
          apply isOpen_iff_mem_nhds.mpr
          intro q hq
          obtain ⟨hz, hb, ⟨wp, hp⟩, ⟨wn, hn⟩⟩ := hq
          have hc : Continuous (fun p : (PDE.Vec d × PDE.Vec d) × (ℝ × ℝ) =>
              ((p.2.1, p.2.2, p.1.1), p.1.2)) := by fun_prop
          have hbase : Continuous (fun p : (PDE.Vec d × PDE.Vec d) × (ℝ × ℝ) =>
              seedBase (p.2.2 * sigma) p.1.2 (p.2.2 • p.1.1)) := by
            unfold seedBase PDE.vecNormSq PDE.vecDot
            fun_prop
          have hvel : Continuous (fun p : (PDE.Vec d × PDE.Vec d) × (ℝ × ℝ) => p.1.2) := by
            fun_prop
          filter_upwards [hvel.continuousAt.eventually_ne hz, hbase.continuousAt.eventually_ne hb,
            ((continuousAt_rescaledCutoff_hessian alpha sigma ((q.2.1, q.2.2, q.1.1), q.1.2) hz hb wp wp).comp_of_eq hc.continuousAt rfl).eventually_const_lt hp, ((continuousAt_rescaledCutoff_hessian alpha sigma ((q.2.1, q.2.2, q.1.1), q.1.2) hz hb wn wn).comp_of_eq hc.continuousAt rfl).eventually_lt_const hn] with p hpz hpb hpp hpn
          exact ⟨hpz, hpb, ⟨wp, hpp⟩, ⟨wn, hpn⟩⟩
        have isCompact_cutoffAnnulus :
            IsCompact (cutoffAnnulus) := by
          have hclosed : IsClosed (cutoffAnnulus) := by
            exact (isClosed_eq (PDE.continuous_vecNormSq.comp continuous_fst) continuous_const).inter
              ((isClosed_le continuous_const (PDE.continuous_vecEuclideanNorm.comp continuous_snd)).inter
                (isClosed_le (PDE.continuous_vecEuclideanNorm.comp continuous_snd) continuous_const))
          apply (isCompact_closedBall 0 2).of_isClosed_subset hclosed
          intro q hq
          rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
          have he : PDE.vecEuclideanNorm q.1 = 1 := by
            unfold PDE.vecEuclideanNorm
            rw [hq.1]
            norm_num
          exact max_le ((PDE.norm_le_vecEuclideanNorm _).trans (by linarith))
            ((PDE.norm_le_vecEuclideanNorm _).trans hq.2.2)
        obtain ⟨_, U, _, hU, hK, hzero, hsub⟩ := generalized_tube_lemma
          (isCompact_cutoffAnnulus) (isCompact_singleton)
          (isOpen_rescaledSignRegion)
          (cutoffAnnulus_zero_signs)
        refine ⟨U, hU, hzero (Set.mem_singleton _), ?_⟩
        intro e z hz p hp
        exact (hsub (a := ((e, z), p)) ⟨hK hz, hp⟩).2.2
      obtain ⟨U, hU, hzero, hsign⟩ := exists_rescaled_sign_neighborhood alpha sigma ha ha1
      have ht : Filter.Tendsto (fun R : ℝ => R⁻¹) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero
      have hs : Filter.Tendsto (fun R => C₀ / Real.rpow R alpha)
          Filter.atTop (nhds 0) := by
        have hh := (tendsto_rpow_neg_atTop ha).const_mul C₀
        simp at hh
        apply hh.congr'
        filter_upwards [Filter.eventually_ge_atTop 0] with R hR
        simp only [Real.rpow_eq_pow, Real.rpow_neg hR, div_eq_mul_inv]
      have hp := hs.prodMk_nhds ht
      filter_upwards [hp.eventually (hU.mem_nhds hzero)] with R hR
      intro e z hz
      exact hsign e z hz (C₀ / Real.rpow R alpha, R⁻¹) hR
    filter_upwards [eventually_rescaled_annulus_signs alpha C₀ sigma ha ha1,
      Filter.eventually_gt_atTop 2] with R hsign hR2
    have hR : 0 < R := lt_trans (by norm_num) hR2
    refine ⟨hR2, ?_⟩
    intro y e he hyR hy2R
    let z := R⁻¹ • y
    have hnorm : PDE.vecEuclideanNorm z = PDE.vecEuclideanNorm y / R := by
      simp only [z, PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hR),
        div_eq_mul_inv, mul_comm]
    have hz : (e, z) ∈ cutoffAnnulus := by
      refine ⟨he, ?_, ?_⟩
      · rw [hnorm]
        exact (le_div_iff₀ hR).mpr (by simpa using hyR)
      · rw [hnorm]
        exact (div_le_iff₀ hR).mpr (by simpa using hy2R)
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
  let smallSeedBall : Set (PDE.Vec d × PDE.Vec d) :=
    {q | PDE.vecNormSq q.2 = 1 ∧ PDE.vecEuclideanNorm (q.1 - q.2) ≤ 1 / 4}
  have eventually_cutoff_negative_direction (alpha C₀ sigma : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) (hsigma : 0 < sigma) (hsq : sigma ^ 2 < (1 - alpha) / 16) :
      ∀ᶠ R : ℝ in Filter.atTop, 2 < R ∧ ∀ y e : PDE.Vec d,
      PDE.vecNormSq e = 1 → 1 / 4 < PDE.vecEuclideanNorm (y - e) →
      ∃ w, cutoffHessian alpha C₀ sigma R y e w < 0 := by
    filter_upwards [eventually_cutoff_annulus_signs alpha C₀ sigma ha ha1 hsigma]
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
      obtain ⟨w, hw⟩ := seed_negative_direction alpha C₀ sigma ha hsigma y e hthreshold
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
  have eventually_cutoff_positive_direction (alpha C₀ sigma : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) (hsigma : 0 < sigma) :
      ∀ᶠ R : ℝ in Filter.atTop, 2 < R ∧ ∀ y e : PDE.Vec d,
      PDE.vecNormSq e = 1 → ∃ w, 0 < cutoffHessian alpha C₀ sigma R y e w := by
    filter_upwards [eventually_cutoff_annulus_signs alpha C₀ sigma ha ha1 hsigma]
      with R hR
    have hR0 : 0 < R := lt_trans (by norm_num) hR.1
    refine ⟨hR.1, ?_⟩
    intro y e he
    by_cases hy : PDE.vecEuclideanNorm y < R
    · obtain ⟨w, hw⟩ := seed_positive_direction d hd alpha C₀ sigma ha hsigma y e
      exact ⟨w, by rwa [cutoffHessian_eq_seed alpha C₀ sigma R hR0 y e w hy]⟩
    · by_cases houter : 2 * R < PDE.vecEuclideanNorm y
      · have hy0 : y ≠ 0 := by
          intro hzero
          have hn := PDE.vecEuclideanNorm_eq_zero_iff.mpr hzero
          rw [hn] at houter
          linarith
        obtain ⟨w, hw⟩ := radialHessian_positive_direction d hd alpha ha y hy0
        refine ⟨w, ?_⟩
        rw [cutoffHessian_eq_radial alpha C₀ sigma R hR0 y e w houter,
          radialProfile_hessian alpha y w w hy0]
        exact hw
      · exact (hR.2 y e he (le_of_not_gt hy) (le_of_not_gt houter)).1
  have seed_transport_pos (sigma : ℝ) (hsigma : 0 < sigma) :
      ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ y e : PDE.Vec d,
      PDE.vecNormSq e = 1 → PDE.vecEuclideanNorm (y - e) ≤ 1 / 4 →
      1 ≤ ansatzTransport alpha (seed alpha C₀ sigma) y e := by
    have continuous_seed_transport (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma) :
        Continuous (fun q : PDE.Vec d × PDE.Vec d =>
        ansatzTransport alpha (seed alpha C₀ sigma) q.1 q.2) := by
      have hb : ContDiff ℝ ⊤
          (fun q : PDE.Vec d × PDE.Vec d => seedBase sigma q.1 q.2) := by
        unfold seedBase PDE.vecNormSq PDE.vecDot
        fun_prop
      have hp : Continuous (fun q : PDE.Vec d × PDE.Vec d =>
          Real.rpow (seedBase sigma q.1 q.2) (alpha / 2 - 1)) :=
        (hb.rpow_const_of_ne fun q =>
          (seedBase_pos sigma hsigma q.1 q.2).ne').continuous
      have hs := (contDiff_seed (d := d) alpha C₀ sigma hsigma).continuous
      simp_rw [ansatzTransport_seed alpha C₀ sigma hsigma]
      unfold PDE.vecDot
      fun_prop
    have isCompact_smallSeedBall :
        IsCompact (smallSeedBall) := by
      have hclosed : IsClosed (smallSeedBall) :=
        (isClosed_eq (PDE.continuous_vecNormSq.comp continuous_snd) continuous_const).inter
          (isClosed_le (PDE.continuous_vecEuclideanNorm.comp (continuous_fst.sub continuous_snd))
            continuous_const)
      apply (isCompact_closedBall 0 2).of_isClosed_subset hclosed
      intro q hq
      obtain ⟨he, hy⟩ := hq
      have hen : PDE.vecEuclideanNorm q.2 = 1 := by simp [PDE.vecEuclideanNorm, he]
      have he' : ‖q.2‖ ≤ 1 := by simpa [hen] using PDE.norm_le_vecEuclideanNorm q.2
      have hy' := (PDE.norm_le_vecEuclideanNorm _).trans hy
      have htri : ‖q.1‖ ≤ ‖q.1 - q.2‖ + ‖q.2‖ := by
        simpa using norm_add_le (q.1 - q.2) q.2
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
      constructor <;> linarith
    let f : PDE.Vec d × PDE.Vec d → ℝ :=
      fun q => ansatzTransport alpha (seed alpha 0 sigma) q.1 q.2
    obtain ⟨B₀, hB₀⟩ := (isCompact_smallSeedBall).bddAbove_image
      (continuous_seed_transport alpha 0 sigma hsigma).abs.continuousOn
    let B := max 0 B₀
    have hB : 0 ≤ B := le_max_left _ _
    let C₀ := 4 * (B + 1) / alpha
    have hC₀ : 0 < C₀ := div_pos (mul_pos (by norm_num) (by linarith)) ha
    refine ⟨C₀, hC₀, ?_⟩
    intro y e he hy
    have hbound : |f (y, e)| ≤ B :=
      (hB₀ ⟨(y, e), ⟨he, hy⟩, rfl⟩).trans (le_max_right _ _)
    have hlow := (abs_le.mp hbound).1
    have hc : 0 < alpha / 3 * C₀ := mul_pos (div_pos ha (by norm_num)) hC₀
    have hmul := mul_le_mul_of_nonneg_right (seed_ball_dot_lower y e he hy) hc.le
    have heq : (3 / 4 : ℝ) * (alpha / 3 * C₀) = B + 1 := by
      dsimp [C₀]
      field_simp
    rw [heq] at hmul
    rw [ansatzTransport_seed_shift alpha C₀ sigma hsigma]
    change 1 ≤ f (y, e) + PDE.vecDot y e * (alpha / 3 * C₀)
    linarith
  let sigma := (1 - alpha) / 8
  have hsigma : 0 < sigma := div_pos (sub_pos.mpr ha1) (by norm_num)
  have hsq : sigma ^ 2 < (1 - alpha) / 16 := by
    dsimp [sigma]
    nlinarith [sq_nonneg alpha]
  obtain ⟨C₀, hC₀, htransport⟩ := seed_transport_pos sigma hsigma
  obtain ⟨R, hp, hn⟩ := ((eventually_cutoff_positive_direction alpha C₀ sigma ha ha1
    hsigma).and (eventually_cutoff_negative_direction alpha C₀ sigma ha ha1
    hsigma hsq)).exists
  refine ⟨C₀, sigma, R, hC₀, hsigma, hp.1, ?_⟩
  intro y e he
  refine ⟨hp.2 y e he, ?_⟩
  by_cases hy : 1 / 4 < PDE.vecEuclideanNorm (y - e)
  · exact Or.inl (hn.2 y e he hy)
  · right
    have hsmall : PDE.vecEuclideanNorm (y - e) ≤ 1 / 4 := le_of_not_gt hy
    have hen : PDE.vecEuclideanNorm e = 1 := by
      unfold PDE.vecEuclideanNorm
      rw [he]
      norm_num
    have htri := PDE.vecEuclideanNorm_add_le (y - e) e
    have hinner : PDE.vecEuclideanNorm y < R := by
      rw [sub_add_cancel, hen] at htri
      linarith
    rw [cutoffTransport_eq_seed alpha C₀ sigma R (lt_trans (by norm_num) hp.1) y e hinner]
    exact htransport y e he hsmall

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

