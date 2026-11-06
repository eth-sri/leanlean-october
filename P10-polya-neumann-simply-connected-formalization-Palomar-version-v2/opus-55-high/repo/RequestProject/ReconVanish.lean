module

public import RequestProject.ReconBasic
public import RequestProject.ReconOuter
public import RequestProject.ReconDensity
public import RequestProject.WeakConstancy

/-!
# Vanishing of `L²` Helmholtz solutions on unbounded connected open sets

An `L²(ℝ²)` function that solves `(Δ + E) u = 0` weakly (`E > 0`) on a connected open set
containing the exterior of a disc vanishes almost everywhere on that set
(`ae_eq_zero_of_helmholtz`). Its mollifications are smooth classical solutions away from the
boundary; they vanish outside a large disc by the Rellich-type argument of
`eq_zero_outside_of_helmholtz`, and the set where `u` vanishes locally is open and closed in
the domain by the unique continuation result `eq_zero_on_ball_of_helmholtz`.
-/

@[expose] public section

open MeasureTheory Set Filter Metric Topology
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-! ### Derivatives of mollifications -/

variable {g : ℂ → ℝ} {E : ℝ} {u : ℂ → ℂ} (φ : ContDiffBump (0 : ℂ))

/-- The flipped mollifier integrand is integrable. -/
lemma integrable_mollify_flip (hg : Continuous g) (hgs : HasCompactSupport g)
    {U : ℂ → ℂ} (hU : LocallyIntegrable U volume) (x : ℂ) :
    Integrable (fun t => g (x - t) • U t) volume := by
  have h2 := (HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    hgs hg hU x).integrable.comp_sub_left x
  simp_all

/-- The real-valued kernel `z ↦ ∂_v g(z)`. -/
def kerD (g : ℂ → ℝ) (v : ℂ) : ℂ → ℝ := fun z => fderiv ℝ g z v

/-- Differentiating a mollification differentiates the kernel. -/
lemma dirD_mollify {g : ℂ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgs : HasCompactSupport g)
    {U : ℂ → ℂ} (hU : LocallyIntegrable U volume) (v : ℂ) :
    dirD (mollify g U) v = mollify (kerD g v) U := by
  funext x
  set L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
  simp only [dirD, mollify]
  rw [(HasCompactSupport.hasFDerivAt_convolution_left L hgs (hg.of_le (by simp)) hU x).fderiv, convolution_def, ContinuousLinearMap.integral_apply (HasCompactSupport.convolutionExists_left (ContinuousLinearMap.precompL ℂ L)
      (hgs.fderiv ℝ) (hg.continuous_fderiv (by simp)) hU x)]
  rfl

lemma contDiff_kerD (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (kerD g v) :=
  (hg.fderiv_right  (by simp)).clm_apply contDiff_const

lemma hasCompactSupport_kerD (hgs : HasCompactSupport g) (v : ℂ) :
    HasCompactSupport (kerD g v) :=
  hgs.fderiv_apply ℝ v

/-- The Laplacian kernel `∂₁₁ g + ∂₂₂ g`. -/
def lapK (g : ℂ → ℝ) : ℂ → ℝ := kerD (kerD g 1) 1 + kerD (kerD g Complex.I) Complex.I

lemma contDiff_lapK (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (lapK g) :=
  (contDiff_kerD (contDiff_kerD hg _) _).add (contDiff_kerD (contDiff_kerD hg _) _)

lemma hasCompactSupport_lapK (hgs : HasCompactSupport g) :
    HasCompactSupport (lapK g) :=
  (hasCompactSupport_kerD (hasCompactSupport_kerD hgs _) _).add
    (hasCompactSupport_kerD (hasCompactSupport_kerD hgs _) _)

lemma mollify_add_kernel {g₁ g₂ : ℂ → ℝ} (h₁ : Continuous g₁) (h₁s : HasCompactSupport g₁)
    (h₂ : Continuous g₂) (h₂s : HasCompactSupport g₂) {U : ℂ → ℂ}
    (hU : LocallyIntegrable U volume) (x : ℂ) :
    mollify (g₁ + g₂) U x = mollify g₁ U x + mollify g₂ U x := by
  simp only [mollify_eq_flip, Pi.add_apply, add_smul]
  exact integral_add (integrable_mollify_flip h₁ h₁s hU x) (integrable_mollify_flip h₂ h₂s hU x)

/-- `t ↦ g(x - t)` as a complex function. -/
def reflK (g : ℂ → ℝ) (x : ℂ) : ℂ → ℂ := fun t => ((g (x - t) : ℝ) : ℂ)

lemma dirD_reflK {g : ℂ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x v : ℂ) :
    dirD (reflK g x) v = -reflK (kerD g v) x := by
  funext t
  have hρ : HasFDerivAt g (fderiv ℝ g (x - t)) (x - t) :=
    ((hg.differentiable (by simp)) _).hasFDerivAt
  have : reflK g x = Complex.ofRealCLM ∘ g ∘ (fun t => x - t) := rfl
  simp [dirD, this, ((Complex.ofRealCLM.hasFDerivAt).comp t (hρ.comp t ((hasFDerivAt_id t).const_sub x))).fderiv, reflK, kerD]

lemma dirD_dirD_reflK (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x v : ℂ) :
    dirD (dirD (reflK g x) v) v = reflK (kerD (kerD g v) v) x := by
  rw [dirD_reflK hg]
  funext t
  have : dirD (-reflK (kerD g v) x) v t = -dirD (reflK (kerD g v) x) v t := by
    simp [dirD, fderiv_neg]
  simp [this, dirD_reflK (contDiff_kerD hg v)]

lemma lap_reflK {g : ℂ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x t : ℂ) :
    lap (reflK g x) t = reflK (lapK g) x t := by
  simp [lap, dirD_dirD_reflK hg, reflK, lapK]

/-- The Laplacian of a mollification. -/
lemma lap_mollify (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgs : HasCompactSupport g)
    {U : ℂ → ℂ} (hU : LocallyIntegrable U volume) (x : ℂ) :
    lap (mollify g U) x = mollify (lapK g) U x := by
  simp [lap, dirD_mollify hg hgs hU, dirD_mollify (contDiff_kerD hg _) (hasCompactSupport_kerD hgs _) hU, lapK, mollify_add_kernel (contDiff_kerD (contDiff_kerD hg _) _).continuous       (hasCompactSupport_kerD (hasCompactSupport_kerD hgs _) _)       (contDiff_kerD (contDiff_kerD hg _) _).continuous       (hasCompactSupport_kerD (hasCompactSupport_kerD hgs _) _) hU]

/-- Mollifications of a weak Helmholtz solution are classical solutions away from `∂D`. -/
lemma mollify_helmholtz {D : Set ℂ} {u : ℂ → ℂ} (hu : LocallyIntegrable u volume)
    (hhelm : ∀ φ : ℂ → ℂ, TestFunction D φ → ∫ z, u z * (lap φ z + E * φ z) = 0)
    (φ : ContDiffBump (0 : ℂ)) {x : ℂ} (hx : closedBall x φ.rOut ⊆ D) :
    lap (mollify (φ.normed volume) u) x + E * mollify (φ.normed volume) u x = 0 := by
  set g := φ.normed volume
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := φ.contDiff_normed
  have hgs : HasCompactSupport g := φ.hasCompactSupport_normed
  have h := hhelm (reflBump φ x) (testFunction_reflBump φ x hx)
  have hre : reflBump φ x = reflK g x := rfl
  rw [hre] at h
  rw [lap_mollify hg hgs hu, mollify_eq_flip, mollify_eq_flip,
    ← integral_const_mul, ← integral_add (integrable_mollify_flip (contDiff_lapK hg).continuous
      (hasCompactSupport_lapK hgs) hu x)
      ((integrable_mollify_flip hg.continuous hgs hu x).const_mul _)]
  rw [← h]
  congr 1; funext t
  rw [lap_reflK hg]
  simp only [reflK, Complex.real_smul]
  ring

lemma contDiff_mollify_bump {u : ℂ → ℂ}
    (hu : LocallyIntegrable u volume) : ContDiff ℝ 2 (mollify (φ.normed volume) u) :=
  HasCompactSupport.contDiff_convolution_left _ φ.hasCompactSupport_normed
    (φ.contDiff_normed) hu

/-- A mollification vanishes where `u` vanishes a.e. at scale `rOut`. -/
lemma mollify_eq_zero_of_ae {y : ℂ} {δ : ℝ}
    (h0 : ∀ᵐ z ∂(volume.restrict (ball y δ)), u z = 0) {z : ℂ}
    (hz : z ∈ ball y (δ - φ.rOut)) : mollify (φ.normed volume) u z = 0 := by
  rw [mollify_eq_flip]
  rw [ae_restrict_iff' measurableSet_ball] at h0
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h0] with t ht
  by_cases hzt : z - t ∈ Function.support (φ.normed volume)
  · rw [φ.support_normed_eq, mem_ball_zero_iff] at hzt
    have htu : u t = 0 := by
      refine ht ?_
      rw [mem_ball] at hz ⊢
      rw [dist_eq_norm] at hz
      rw [dist_eq_norm]
      calc ‖t - y‖ = ‖(z - y) - (z - t)‖ := by ring
        _ ≤ ‖z - y‖ + ‖z - t‖ := norm_sub_le _ _
        _ < δ := by linarith
    simp_all
  simp_all

/-- If the mollifications `stdBump k ⋆ u` eventually vanish on `W`, then `u = 0` a.e. on `W`. -/
lemma ae_eq_zero_of_mollify_eq_zero (hu : MemLp u 2 volume) {W : Set ℂ}
    (hW : MeasurableSet W)
    (h : ∀ᶠ k in atTop, ∀ z ∈ W, mollify ((stdBump k).normed volume) u z = 0) :
    ∀ᵐ z ∂(volume.restrict W), u z = 0 := by
  have hle : ∀ᶠ k in atTop, eLpNorm u 2 (volume.restrict W) ≤
      eLpNorm (mollify ((stdBump k).normed volume) u - u) 2 volume := by
    filter_upwards [h] with k hk
    refine le_trans (le_of_eq ?_) (eLpNorm_restrict_le _ _ _ W)
    rw [← eLpNorm_neg]
    refine eLpNorm_congr_ae ?_
    refine (ae_restrict_iff' hW).2 (Eventually.of_forall fun z hz => ?_)
    simp_all
  have := (eLpNorm_eq_zero_iff two_ne_zero).mp (le_antisymm (ge_of_tendsto (tendsto_mollify_L2 tendsto_stdBump_rOut hu) hle) (zero_le))
  assumption

/-- An `L²` weak solution of `(Δ + E) u = 0` on a connected open set containing the exterior
of a disc vanishes a.e. on that set. -/
theorem ae_eq_zero_of_helmholtz (hE : 0 < E) {D : Set ℂ} (hDo : IsOpen D)
    (hDc : IsConnected D) {R : ℝ} (hR : ∀ z : ℂ, R < ‖z‖ → z ∈ D) {u : ℂ → ℂ}
    (hu : MemLp u 2 volume)
    (hhelm : ∀ φ : ℂ → ℂ, TestFunction D φ → ∫ z, u z * (lap φ z + E * φ z) = 0) :
    ∀ᵐ z ∂(volume.restrict D), u z = 0 := by
  have hul  := hu.locallyIntegrable one_le_two
  set uk : ℕ → ℂ → ℂ := fun k => mollify ((stdBump k).normed volume) u with huk
  have hsm : ∀ k, ContDiff ℝ 2 (uk k) := fun k => contDiff_mollify_bump _ hul
  have hrk : ∀ k, (stdBump k).rOut ≤ 1 := fun k => by
    rw [stdBump_rOut]
    rw [div_le_one (by positivity)]
    linarith
  -- vanishing outside a large disc
  set R' : ℝ := max R 0 + 1 with hR'
  have hout : ∀ k, ∀ z : ℂ, R' < ‖z‖ → uk k z = 0 := by
    intro k
    refine eq_zero_outside_of_helmholtz (hsm k) (memLp_mollify _ hu) hE (by positivity) fun x hx => ?_
    refine mollify_helmholtz hul hhelm _ fun w hw => hR w ?_
    have h1 := norm_sub_norm_le x w
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at hw
    grind
  -- the set where `u` vanishes locally
  set S : Set ℂ := {x | ∃ r > 0, ∀ᵐ z ∂(volume.restrict (ball x r)), u z = 0} with hS
  have hSo : IsOpen S := by
    rw [Metric.isOpen_iff]
    rintro x ⟨r, hr, hx⟩
    refine ⟨r, hr, fun y hy => ⟨r - dist y x, by simp_all, ?_⟩⟩
    refine ae_restrict_of_ae_restrict_of_subset (fun w hw => ?_) hx
    rw [mem_ball] at hw ⊢
    linarith [dist_triangle w y x]
  have hne : (D ∩ S).Nonempty := by
    refine ⟨(R' + 1 : ℝ), hR _ ?_, 1, one_pos, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs]
      grind
    · have := ae_eq_zero_of_mollify_eq_zero hu 
        (measurableSet_lt measurable_const measurable_norm)
        (Eventually.of_forall fun k z hz => hout k z hz)
      refine ae_restrict_of_ae_restrict_of_subset (fun w hw => ?_) this
      rw [mem_ball, dist_eq_norm] at hw
      have h1 := norm_sub_norm_le (((R' + 1 : ℝ) : ℂ)) w
      rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs] at h1
      grind
  rw [ae_restrict_iff' hDo.measurableSet]
  have hnull : volume (D ∩ {z | u z ≠ 0}) = 0 := by
    refine measure_null_of_locally_null _ fun x hx => ?_
    obtain ⟨r, hr, hxr⟩ := hDc.isPreconnected.subset_of_closure_inter_subset hSo hne (by
    rintro x ⟨hxc, hxD⟩
    obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hDo x hxD
    set r := ε / 4
    have hr : 0 < r := by positivity
    have hrε : ε = 4 * r := by ring
    obtain ⟨y, ⟨δ, hδ, hy⟩, hxy⟩ := Metric.mem_closure_iff.mp hxc r hr
    set η := min r δ / 2
    have hη : 0 < η := by positivity
    have hk : ∀ᶠ k in atTop, ∀ z ∈ ball y (2 * r), uk k z = 0 := by
      filter_upwards [tendsto_stdBump_rOut.eventually (gt_mem_nhds hη)] with k hk
      refine eq_zero_on_ball_of_helmholtz (hsm k) (E := E) (δ := δ - (stdBump k).rOut)
        (by grind) ?_ ?_
      · intro z hz
        refine mollify_helmholtz hul hhelm _ fun w hw => hεD ?_
        rw [mem_closedBall] at hw
        rw [mem_ball] at hz ⊢
        have := min_le_left r δ
        simp only [η] at hk
        linarith [dist_triangle w z x, dist_triangle z y x, dist_comm x y]
      · intro z hz
        exact mollify_eq_zero_of_ae _ hy hz
    refine ⟨r, hr, ae_restrict_of_ae_restrict_of_subset (fun w hw => ?_)
      (ae_eq_zero_of_mollify_eq_zero hu measurableSet_ball hk)⟩
    rw [mem_ball] at hw ⊢
    linarith [dist_triangle w x y]) hx.1
    refine ⟨D ∩ {z | u z ≠ 0} ∩ ball x r, inter_mem_nhdsWithin _ (ball_mem_nhds x hr), ?_⟩
    rw [ae_restrict_iff' measurableSet_ball] at hxr
    refine measure_mono_null (fun w hw => ?_) (ae_iff.mp hxr)
    simp_all
  refine measure_mono_null (fun w hw => ?_) hnull
  simp_all

end PolyaNeumann
