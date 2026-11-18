module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningProfile
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyWeakJets
public import Mathlib.Topology.MetricSpace.Thickening
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningValues
import Mathlib.Tactic.GCongr
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter MeasureTheory Set Metric
open scoped Convolution


/-- At a C2 point the flattened velocity Hessian has the literal rank-one correction. -/
theorem dvv_flatProfile_of_contDiffAt {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ)
    (hr : 0 < r) (q : XV d) (hH : ContDiffAt ℝ 2 H q) (i k : Fin d) :
    dvv (flatProfile H flatteningPsi flatteningOffset alpha r) q i k =
      -deriv flatteningPsi (H q / Real.rpow r alpha) * dvv H q i k -
        Real.rpow r (-alpha) * deriv (deriv flatteningPsi) (H q / Real.rpow r alpha) *
          dv H q i * dv H q k := by
  let a := Real.rpow r alpha
  have hin : HasFDerivAt (fun z => H z / a) (a⁻¹ • fderiv ℝ H q) q := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (hH.differentiableAt (by norm_num)).hasFDerivAt.const_mul a⁻¹
  have hpsi : DifferentiableAt ℝ (deriv flatteningPsi) (H q / a) :=
    by
      rw [funext deriv_flatteningPsi]
      exact (contDiff_flatteningSlope.differentiable (by simp)).differentiableAt
  have hv : DifferentiableAt ℝ (fun z => dv H z k) q :=
    ((hH.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have he := (hpsi.hasDerivAt.comp_hasFDerivAt q hin).neg.mul hv.hasFDerivAt
  change HasFDerivAt (fun z => -deriv flatteningPsi (H z / a) * dv H z k) _ q at he
  have hloc : (fun z => dv (flatProfile H flatteningPsi flatteningOffset alpha r) z k) =ᶠ[nhds q]
      (fun z => -deriv flatteningPsi (H z / a) * dv H z k) := by
    filter_upwards [(hH.eventually (by norm_num))] with z hz
    unfold dv
    rw [fderiv_flatProfile H alpha r hr z (hz.differentiableAt (by norm_num))]
    rfl
  unfold dvv
  rw [hloc.fderiv_eq, he.fderiv]
  simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]
  change -deriv flatteningPsi (H q / a) * dvv H q i k +
    dv H q k * -(deriv (deriv flatteningPsi) (H q / a) * (a⁻¹ * dv H q i)) = _
  have ha : a⁻¹ = Real.rpow r (-alpha) := by
    dsimp [a]
    rw [Real.rpow_neg hr.le]
  rw [ha]
  dsimp only [a, dvv]
  ring







/-- A local bound on the kernel sampling ball suffices for the normalized convolution bound. -/
theorem spatialMollify_norm_le_on_ball {d : ℕ} (phi : ContDiffBump (0 : XV d))
    (g : XV d → ℝ) (hg : AEStronglyMeasurable g volume) (C : ℝ) (hC : 0 ≤ C)
    (q : XV d) (hb : ∀ y ∈ ball q phi.rOut, ‖g y‖ ≤ C) :
    ‖spatialMollify phi g q‖ ≤ C := by
  simpa only [spatialMollify, dist_zero_right] using (dist_convolution_le (μ := volume) (x₀ := q) (z₀ := 0) hC phi.support_normed_eq.subset phi.nonneg_normed phi.integral_normed hg (fun y hy => by simpa using hb y hy))

/-- The standard normalized convolution converges almost everywhere for every locally
integrable scalar function, without a global boundedness assumption. -/
theorem spatialMollify_ae_tendsto {d : ℕ} (g : XV d → ℝ) (hg : LocallyIntegrable g volume) :
    ∀ᵐ q ∂volume,
      Tendsto (fun n => spatialMollify (standardMollifierSequence n) g q) atTop (nhds (g q)) := by
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (standardMollifierSequence_rOut_tendsto) (Eventually.of_forall (standardMollifierSequence_radius_ratio)) hg



/-- The standard smooth approximation of the selected unflattened profile. -/
noncomputable def mollifiedProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (n : ℕ) : XV d → ℝ :=
  spatialMollify (standardMollifierSequence n) (profileFunction h)

/-- Each selected profile approximation is smooth. -/
theorem contDiff_mollifiedProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifiedProfile h n) :=
  spatialMollify_contDiff _ _ (selectedProfile_spec h).2.2.2.2.2.2.1.locallyIntegrable

/-- The position derivative of the profile approximation is convolution of the selected jet. -/
theorem dx_mollifiedProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (n : ℕ) (q : XV d) (i : Fin d) :
    dx (mollifiedProfile h n) q i =
      spatialMollify (standardMollifierSequence n) (fun z => profilePositionJet h z i) q := by
  apply mollify_weak_directional_jet _ _ _ ((selectedProfile_spec h).2.2.2.2.2.2.1).locallyIntegrable (Pi.single i 1, 0)
  intro test ht hc
  exact (((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) test (ht.of_le (by simp)) hc).1 i

/-- The velocity derivative of the approximation is convolution of the selected weak jet. -/
theorem dv_mollifiedProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (n : ℕ) (q : XV d) (i : Fin d) :
    dv (mollifiedProfile h n) q i =
      spatialMollify (standardMollifierSequence n) (fun z => profileVelocityJet h z i) q := by
  apply mollify_weak_directional_jet _ _ _ ((selectedProfile_spec h).2.2.2.2.2.2.1).locallyIntegrable (0, Pi.single i 1)
  intro test ht hc
  exact (((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) test (ht.of_le (by simp)) hc).2.1 i

/-- The velocity Hessian of the approximation is convolution of the selected weak Hessian. -/
theorem dvv_mollifiedProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (n : ℕ) (q : XV d) (i k : Fin d) :
    dvv (mollifiedProfile h n) q i k =
      spatialMollify (standardMollifierSequence n) (fun z => profileHessian h z i k) q := by
  have hw := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  apply mollify_weak_second_jet _ _ (fun z => profileVelocityJet h z k) _
    ((selectedProfile_spec h).2.2.2.2.2.2.1).locallyIntegrable (((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) k) (0, Pi.single k 1) (0, Pi.single i 1)
  · intro test ht hc
    exact (hw test (ht.of_le (by simp)) hc).2.1 k
  · intro test ht hc
    change (∫ z, profileFunction h z * dvv test z k i) = _
    calc
      _ = (∫ z, profileFunction h z * dvv test z i k) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => congrArg (fun a => profileFunction h z * a)
          (dvv_test_swap test (ht.of_le (by simp)) z k i))
      _ = _ := (hw test (ht.of_le (by simp)) hc).2.2 i k



/-- Flattening the smooth approximations keeps the literal profile formula. -/
noncomputable def mollifiedFlatProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (n : ℕ) : XV d → ℝ :=
  flatProfile (mollifiedProfile h n) flatteningPsi flatteningOffset alpha r


/-- The fixed slope composed with division is continuous. -/
theorem continuous_flatSlope (alpha r : ℝ) :
    Continuous (fun s : ℝ => deriv flatteningPsi (s / Real.rpow r alpha)) := by
  rw [funext deriv_flatteningPsi]
  exact contDiff_flatteningSlope.continuous.comp (continuous_id.div_const _)



/-- The position jets converge to the explicit selected flattened position jet. -/
theorem dx_mollifiedFlatProfile_ae_tendsto {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (i : Fin d) :
    ∀ᵐ q ∂volume, Tendsto (fun n => dx (mollifiedFlatProfile h r n) q i) atTop
      (nhds (flatProfilePositionJet h r q i)) := by
  filter_upwards [spatialMollify_ae_tendsto _ ((selectedProfile_spec h).2.2.2.2.2.2.1).locallyIntegrable,
    spatialMollify_ae_tendsto _ ((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i)] with q hq hg
  convert (((continuous_flatSlope alpha r).continuousAt.tendsto.comp hq).neg.mul hg) using 1
  · funext n
    unfold dx mollifiedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q
      ((contDiff_mollifiedProfile h n).differentiable (by simp) q)]
    change -deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
        dx (mollifiedProfile h n) q i = _
    rw [dx_mollifiedProfile]
    rfl
  · rfl

/-- The velocity jets converge to the explicit selected flattened velocity jet. -/
theorem dv_mollifiedFlatProfile_ae_tendsto {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (i : Fin d) :
    ∀ᵐ q ∂volume, Tendsto (fun n => dv (mollifiedFlatProfile h r n) q i) atTop
      (nhds (flatProfileVelocityJet h r q i)) := by
  filter_upwards [spatialMollify_ae_tendsto _ ((selectedProfile_spec h).2.2.2.2.2.2.1).locallyIntegrable,
    spatialMollify_ae_tendsto _ ((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i)] with q hq hg
  convert (((continuous_flatSlope alpha r).continuousAt.tendsto.comp hq).neg.mul hg) using 1
  · funext n
    unfold dv mollifiedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q
      ((contDiff_mollifiedProfile h n).differentiable (by simp) q)]
    change -deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
        dv (mollifiedProfile h n) q i = _
    rw [dv_mollifiedProfile]
    rfl
  · rfl

/-- The Hessian jets converge, including the nonlinear product of the two first jets. -/
theorem dvv_mollifiedFlatProfile_ae_tendsto {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (i k : Fin d) :
    ∀ᵐ q ∂volume, Tendsto (fun n => dvv (mollifiedFlatProfile h r n) q i k) atTop
      (nhds (flatProfileHessian h r q i k))  := by
  have continuous_flatSecond :
      Continuous (fun s => deriv (deriv flatteningPsi) (s / Real.rpow r alpha)) := by
    rw [funext deriv_flatteningPsi]
    exact (contDiff_flatteningSlope.continuous_deriv (by simp)).comp (continuous_id.div_const _)
  have hv := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  filter_upwards [spatialMollify_ae_tendsto _ ((selectedProfile_spec h).2.2.2.2.2.2.1).locallyIntegrable,
    spatialMollify_ae_tendsto _ (hv i), spatialMollify_ae_tendsto _ (hv k),
    spatialMollify_ae_tendsto _ ((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i k)] with q hq hi hk hhq
  have hconst : Tendsto (fun _ : ℕ => Real.rpow r (-alpha)) atTop
      (nhds (Real.rpow r (-alpha))) := tendsto_const_nhds
  have hc := (((continuous_flatSlope alpha r).continuousAt.tendsto.comp hq).neg.mul hhq).sub (((hconst.mul ((continuous_flatSecond).continuousAt.tendsto.comp hq)).mul hi).mul hk)
  convert hc using 1
  · funext n
    rw [mollifiedFlatProfile, dvv_flatProfile_of_contDiffAt _ _ _ hr q
      ((contDiff_mollifiedProfile h n).contDiffAt.of_le (by simp)) i k,
      dvv_mollifiedProfile, dv_mollifiedProfile, dv_mollifiedProfile]
    rfl
  · rfl



/-- Multiplication by the negative flattening slope preserves an absolute bound. -/
theorem abs_flatSlope_mul_le (s g M : ℝ) (hg : |g| ≤ M) :
    |(-deriv flatteningPsi s) * g| ≤ M := by
  rw [abs_mul, abs_neg]
  have hs : |deriv flatteningPsi s| ≤ 1 := by
    rw [abs_of_nonneg (flatteningPsi_deriv_bounds s).1]
    exact (flatteningPsi_deriv_bounds s).2
  calc
    _ ≤ 1 * M := mul_le_mul hs hg (abs_nonneg _) (by norm_num)
    _ = M := one_mul _

/-- The nonlinear Hessian correction is uniformly bounded on bounded first and second jets. -/
theorem abs_flatSecond_le (s gi gk hij alpha r M P : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (hi : |gi| ≤ M) (hk : |gk| ≤ M) (hh : |hij| ≤ M)
    (hP : 0 ≤ P) (hp : deriv (deriv flatteningPsi) s ≤ P) :
    |-deriv flatteningPsi s * hij - Real.rpow r (-alpha) *
        deriv (deriv flatteningPsi) s * gi * gk| ≤ M + Real.rpow r (-alpha) * P * M ^ 2 := by
  simp only [Real.rpow_eq_pow]
  have hpabs : |deriv (deriv flatteningPsi) s| ≤ P := by
    rw [abs_of_nonneg (flatteningPsi_deriv2_nonneg s)]
    exact hp
  calc
    _ ≤ |(-deriv flatteningPsi s) * hij| +
        |r ^ (-alpha) * deriv (deriv flatteningPsi) s * gi * gk| := abs_sub _ _
    _ ≤ M + r ^ (-alpha) * P * M ^ 2 := by
      apply add_le_add (abs_flatSlope_mul_le s hij M hh)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ((Real.rpow_pos_of_pos hr (-alpha)).le), pow_two]
      calc
        _ ≤ r ^ (-alpha) * P * M * M := by gcongr
        _ = _ := by ring


/-- The flattened values and all jets have one eventual bound on each punctured compact set. -/
theorem mollifiedFlatProfile_eventually_bounded {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (K : Set (XV d)) (hK : IsCompact K) (hz : 0 ∉ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ q ∈ K,
      ‖mollifiedFlatProfile h r n q‖ ≤ C ∧
      (∀ i, |dx (mollifiedFlatProfile h r n) q i| ≤ C) ∧
      (∀ i, |dv (mollifiedFlatProfile h r n) q i| ≤ C) ∧
      (∀ i k, |dvv (mollifiedFlatProfile h r n) q i k| ≤ C)  := by
  have mollifiedProfile_eventually_bounded :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ∀ q ∈ K,
      ‖mollifiedProfile h n q‖ ≤ M ∧
      (∀ i, |dx (mollifiedProfile h n) q i| ≤ M) ∧
      (∀ i, |dv (mollifiedProfile h n) q i| ≤ M) ∧
      (∀ i k, |dvv (mollifiedProfile h n) q i k| ≤ M) := by
    have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
    have hsub : K ⊆ ({0}ᶜ : Set (XV d)) := by
      intro q hq
      change q ≠ 0
      intro he
      exact hz (he ▸ hq)
    obtain ⟨delta, hd, hdelta⟩ := hK.exists_cthickening_subset_open isOpen_compl_singleton hsub
    let L := cthickening delta K
    have hL : IsCompact L := hK.cthickening
    obtain ⟨MH, hMH⟩ := hL.exists_bound_of_continuousOn hH.continuousOn
    obtain ⟨MG, hMG⟩ := ((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) L hL (fun hmem => by simpa using hdelta hmem)
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
        (((measurable_pi_apply i).comp ((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.1)).aestronglyMeasurable) M hM q
      intro y hy
      exact (norm_le_pi_norm (profilePositionJet h y) i).trans ((hMG y (hyL y hy)).1.trans hGM)
    · intro i
      rw [dv_mollifiedProfile, ← Real.norm_eq_abs]
      apply spatialMollify_norm_le_on_ball _ _
        (((measurable_pi_apply i).comp ((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.1)).aestronglyMeasurable) M hM q
      intro y hy
      exact (norm_le_pi_norm (profileVelocityJet h y) i).trans ((hMG y (hyL y hy)).2.1.trans hGM)
    · intro i k
      rw [dvv_mollifiedProfile, ← Real.norm_eq_abs]
      apply spatialMollify_norm_le_on_ball _ _ (((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.1) i k).aestronglyMeasurable M hM q
      intro y hy
      simpa using ((hMG y (hyL y hy)).2.2 i k).trans hGM
  obtain ⟨M, hM, he⟩ := mollifiedProfile_eventually_bounded
  obtain ⟨P, hP, hp⟩ := flatteningPsi_deriv2_bound
  let B := 1 + |flatteningOffset| * Real.rpow r alpha + M
  let D := M + Real.rpow r (-alpha) * P * M ^ 2
  let C := max B D
  have hD : M ≤ D := le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg ((Real.rpow_pos_of_pos hr (-alpha)).le) hP.le) (sq_nonneg M))
  have hDC : D ≤ C := le_max_right _ _
  have hBC : B ≤ C := le_max_left _ _
  refine ⟨C, hM.trans (hD.trans hDC), ?_⟩
  filter_upwards [he] with n hn
  intro q hq
  obtain ⟨hH, hx, hv, hh⟩ := hn q hq
  have hdiff := (contDiff_mollifiedProfile h n).differentiable (by simp) q
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hHabs : |mollifiedProfile h n q| ≤ M := by
      simpa using hH
    have hv : |mollifiedFlatProfile h r n q| ≤ B :=
      (abs_flatProfile_le (mollifiedProfile h n) alpha r hr q).trans
        (add_le_add_right hHabs _)
    simpa using hv.trans hBC
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



/-- Smooth functions have the three classical punctured distributional identities. -/
theorem smooth_punctured_weak_identities {d : ℕ} (H : XV d → ℝ)
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

/-- The literal flattened function has all weak test identities away from the origin. -/
theorem flatProfile_punctured_weak_of_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (test : XV d → ℝ) (ht : ContDiff ℝ 2 test) (hs : HasCompactSupport test)
    (hz : (0 : XV d) ∉ tsupport test) :
    (∀ i, (∫ q, selectedFlatProfile h r q * dx test q i) =
      -(∫ q, flatProfilePositionJet h r q i * test q)) ∧
    (∀ i, (∫ q, selectedFlatProfile h r q * dv test q i) =
      -(∫ q, flatProfileVelocityJet h r q i * test q)) ∧
    (∀ i k, (∫ q, selectedFlatProfile h r q * dvv test q i k) =
      (∫ q, flatProfileHessian h r q i k * test q))    := by
  have integral_mul_test_tendsto {d : ℕ} (F : ℕ → XV d → ℝ) (f : XV d → ℝ) (hm : ∀ n, AEStronglyMeasurable (F n) volume) (hl : ∀ᵐ q ∂volume, Tendsto (fun n => F n q) atTop (nhds (f q))) (test : XV d → ℝ) (ht : Continuous test) (hs : HasCompactSupport test) (K : Set (XV d)) (hsub : tsupport test ⊆ K) (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ᶠ n in atTop, ∀ q ∈ K, ‖F n q‖ ≤ C) :
      Tendsto (fun n => ∫ q, F n q * test q) atTop (nhds (∫ q, f q * test q)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun q => C * ‖test q‖)
    · exact Eventually.of_forall (fun n => (hm n).mul ht.aestronglyMeasurable)
    · filter_upwards [hb] with n hn
      exact Eventually.of_forall (fun q => by
        rw [norm_mul]
        by_cases hq : q ∈ K
        · exact mul_le_mul_of_nonneg_right (hn q hq) (norm_nonneg _)
        · have hz : test q = 0 := image_eq_zero_of_notMem_tsupport (fun hmem => hq (hsub hmem))
          simp [hz, norm_zero, le_refl])
    · exact (ht.integrable_of_hasCompactSupport hs).norm.const_mul C
    · filter_upwards [hl] with q hq
      exact hq.mul tendsto_const_nhds
  have mollifiedFlatProfile_ae_tendsto :
      ∀ᵐ q ∂volume, Tendsto (fun n => mollifiedFlatProfile h r n q) atTop
      (nhds (selectedFlatProfile h r q)) := by
    have hc : Continuous (fun s => 1 - flatteningOffset * Real.rpow r alpha -
        Real.rpow r alpha * flatteningPsi (s / Real.rpow r alpha)) :=
      continuous_const.sub (continuous_const.mul
        (contDiff_flatteningPsi.continuous.comp (continuous_id.div_const _)))
    filter_upwards [spatialMollify_ae_tendsto _ ((selectedProfile_spec h).2.2.2.2.2.2.1).locallyIntegrable] with q hq
    exact hc.continuousAt.tendsto.comp hq
  have contDiff_mollifiedFlatProfile (n : ℕ) :
      ContDiff ℝ (⊤ : ℕ∞) (mollifiedFlatProfile h r n) := by
    unfold mollifiedFlatProfile flatProfile
    exact contDiff_const.sub (contDiff_const.mul
      (contDiff_flatteningPsi.comp ((contDiff_mollifiedProfile h n).div_const _)))
  let K := tsupport test
  obtain ⟨C, hC, hb⟩ := mollifiedFlatProfile_eventually_bounded h r hr K hs hz
  have hnorm : ∀ᶠ n in atTop, ∀ q ∈ K, ‖mollifiedFlatProfile h r n q‖ ≤ C := by
    filter_upwards [hb] with n hn
    exact fun q hq => (hn q hq).1
  have hvalue (t : XV d → ℝ) (hc : Continuous t) (hsc : HasCompactSupport t)
      (hsub : tsupport t ⊆ K) :
      Tendsto (fun n => ∫ q, mollifiedFlatProfile h r n q * t q) atTop
        (nhds (∫ q, selectedFlatProfile h r q * t q)) :=
    integral_mul_test_tendsto _ _
      (fun n => (contDiff_mollifiedFlatProfile n).continuous.aestronglyMeasurable)
      (mollifiedFlatProfile_ae_tendsto) t hc hsc K hsub C hC hnorm
  have hclassic (n : ℕ) := smooth_punctured_weak_identities _
    (contDiff_mollifiedFlatProfile n) test ht hs hz
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hleft := hvalue (fun q => dx test q i) (continuous_dx_test test ht i)
      (hs.fderiv_apply ℝ (Pi.single i 1, 0)) (tsupport_fderiv_apply_subset ℝ (Pi.single i 1, 0))
    have hbound : ∀ᶠ n in atTop, ∀ q ∈ K, ‖dx (mollifiedFlatProfile h r n) q i‖ ≤ C := by
      filter_upwards [hb] with n hn
      intro q hq
      simpa using (hn q hq).2.1 i
    have hright := integral_mul_test_tendsto _ _
      (fun n => (measurable_fderiv_apply_const ℝ (mollifiedFlatProfile h r n)
        (Pi.single i 1, 0)).aestronglyMeasurable)
      (dx_mollifiedFlatProfile_ae_tendsto h r hr i) test ht.continuous hs K subset_rfl C hC hbound
    exact tendsto_nhds_unique (hleft.congr (fun n => (hclassic n).1 i)) hright.neg
  · intro i
    have hleft := hvalue (fun q => dv test q i) (continuous_dv_test test ht i)
      (hs.fderiv_apply ℝ (0, Pi.single i 1)) (tsupport_fderiv_apply_subset ℝ (0, Pi.single i 1))
    have hbound : ∀ᶠ n in atTop, ∀ q ∈ K, ‖dv (mollifiedFlatProfile h r n) q i‖ ≤ C := by
      filter_upwards [hb] with n hn
      intro q hq
      simpa using (hn q hq).2.2.1 i
    have hright := integral_mul_test_tendsto _ _
      (fun n => (measurable_fderiv_apply_const ℝ (mollifiedFlatProfile h r n)
        (0, Pi.single i 1)).aestronglyMeasurable)
      (dv_mollifiedFlatProfile_ae_tendsto h r hr i) test ht.continuous hs K subset_rfl C hC hbound
    exact tendsto_nhds_unique (hleft.congr (fun n => (hclassic n).2.1 i)) hright.neg
  · intro i k
    have hsub : tsupport (fun q => dvv test q i k) ⊆ K :=
      (tsupport_fderiv_apply_subset ℝ (0, Pi.single i 1)).trans
        (tsupport_fderiv_apply_subset ℝ (0, Pi.single k 1))
    have hbound : ∀ᶠ n in atTop, ∀ q ∈ K, ‖dvv (mollifiedFlatProfile h r n) q i k‖ ≤ C := by
      filter_upwards [hb] with n hn
      intro q hq
      simpa using (hn q hq).2.2.2 i k
    exact tendsto_nhds_unique ((hvalue (fun q => dvv test q i k) (continuous_dvv_test test ht i k) ((hs.fderiv_apply ℝ (0, Pi.single k 1)).fderiv_apply ℝ (0, Pi.single i 1)) hsub).congr (fun n => (hclassic n).2.2 i k)) (integral_mul_test_tendsto _ _ (fun n => (measurable_dvv (mollifiedFlatProfile h r n) i k).aestronglyMeasurable) (dvv_mollifiedFlatProfile_ae_tendsto h r hr i k) test ht.continuous hs K subset_rfl C hC hbound)




/-- The requested source-range facade for the complete conditional flattened-profile theorem. -/
theorem flatProfile_source {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ}
    (_ha : 0 < alpha) (_ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    FlatProfileSourceStatement h r    := by
  have flatProfile_jets_ae_of_profile :
      ∀ᵐ q ∂volume, flatProfilePositionJet h r q = dx (selectedFlatProfile h r) q ∧
      flatProfileVelocityJet h r q = dv (selectedFlatProfile h r) q ∧
      flatProfileHessian h r q = dvv (selectedFlatProfile h r) q := by
    filter_upwards [((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.1), ((selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)] with q hj hH
    refine ⟨?_, ?_, ?_⟩
    · ext i
      unfold dx selectedFlatProfile
      rw [fderiv_flatProfile _ _ _ hr q (hH.differentiableAt (by norm_num))]
      change -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
        profilePositionJet h q i =
          -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) * dx (profileFunction h) q i
      rw [hj.1]
    · ext i
      unfold dv selectedFlatProfile
      rw [fderiv_flatProfile _ _ _ hr q (hH.differentiableAt (by norm_num))]
      change -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) *
        profileVelocityJet h q i =
          -deriv flatteningPsi (profileFunction h q / Real.rpow r alpha) * dv (profileFunction h) q i
      rw [hj.2.1]
    · ext i k
      rw [selectedFlatProfile, dvv_flatProfile_of_contDiffAt _ _ _ hr q hH i k]
      unfold flatProfileHessian
      rw [hj.2.1, hj.2.2]
  have flatProfile_operator_ae_of_profile :
      ∀ᵐ q ∂volume, statOp (profileMatrix h) (selectedFlatProfile h r) q =
      flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q := by
    filter_upwards [flatProfile_jets_ae_of_profile,
      flatProfile_representatives_source h r] with q hj hs
    unfold statOp
    rw [← hj.1, ← hj.2.2]
    exact hs
  have flatProfile_weak_of_profile :
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
  obtain ⟨hmx, hmv, hmh⟩ := measurable_flatProfile_jets h r
  obtain ⟨hx, hv, hh⟩ := flatProfile_jets_locallyIntegrable_of_profile h r hr
  exact ⟨continuous_selectedFlatProfile h r, hmx, hmv, hmh,
    flatProfile_jets_compact_bound_of_profile h r hr, hx, hv, hh,
    flatProfile_jets_ae_of_profile, flatProfile_weak_of_profile,
    flatProfile_representatives_source h r, flatProfile_operator_ae_of_profile⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

