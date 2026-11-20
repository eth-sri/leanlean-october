module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalMass
public import RequestProject.ChainRule
public import RequestProject.PlanarNotation

/-!
# Genuine componentwise conformal transport

The checked physical mass identity extends through the dense H¹ inclusion
to a norm-preserving weighted L² pullback. Bounded coordinate ratios of the
actual Jacobian then transport each actual weak gradient component.
This uses the supplied local conformal map and no plane homeomorphism.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology

private theorem gradient_extendOfNorm_eq
    {H X Y : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (V : H →L[ℂ] X) (M : H →L[ℂ] Y) (hd : DenseRange V)
    (hn : ∀ u, ‖M u‖ = ‖V u‖) (u : H) :
    M.toLinearMap.extendOfNorm V.toLinearMap (V u) = M u := LinearMap.extendOfNorm_eq   hd
    ⟨1, fun w => by simp [*]⟩ u

private theorem gradient_norm_extendOfNorm
    {H X Y : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (V : H →L[ℂ] X) (M : H →L[ℂ] Y) (hd : DenseRange V)
    (hn : ∀ u, ‖M u‖ = ‖V u‖) (v : X) :
    ‖M.toLinearMap.extendOfNorm V.toLinearMap v‖ = ‖v‖ := by
  
  refine hd.induction_on  v ?_ ?_
  · exact isClosed_eq (M.toLinearMap.extendOfNorm V.toLinearMap).continuous.norm continuous_norm
  · intro u
    exact (congrArg norm (gradient_extendOfNorm_eq V M hd hn u)).trans (hn u)

private theorem gradient_eq_of_dense
    {S H Y : Type*} [TopologicalSpace H] [TopologicalSpace Y] [T2Space Y]
    (ι : S → H) (hd : DenseRange ι) (A B : H → Y)
    (hA : Continuous A) (hB : Continuous B)
    (he : ∀ s, A (ι s) = B (ι s)) (u : H) : A u = B u := hd.induction_on u (isClosed_eq hA hB) he

section Coordinates

section

variable (Φ : ControlledDiskMap) (u : NeumannH1 Φ.domain)

private theorem mass_norm_eq_value :
    ‖Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper u‖ =
      ‖h1Value Φ.domain u‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (norm_sq_localConformalMassPullback Φ u)

/-- The actual Jacobian-weighted pullback on the whole physical L² space. -/
def SmoothDiskMap.weightedL2Pullback (Φ : SmoothDiskMap) {K : ℝ}
    (hL : IsLipschitzDomain Φ.domain) (hK : ∀ z ∈ unitDisk, ‖fderiv ℝ Φ.map z 1‖ ≤ K) :
    L2 Φ.domain →L[ℂ] L2 unitDisk :=
  (Φ.massPullback hL hK).toLinearMap.extendOfNorm
    (h1Value Φ.domain).toLinearMap

theorem localConformalWeightedL2Pullback_h1Value :
    Φ.weightedL2Pullback Φ.lipschitzDomain Φ.deriv_upper
      (h1Value Φ.domain u) =
        Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper u :=
  gradient_extendOfNorm_eq
    (h1Value Φ.domain)
    (Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper)
    (h1Value_denseRange Φ.lipschitzDomain.1.1)
    (mass_norm_eq_value Φ) u

theorem norm_localConformalWeightedL2Pullback
    (v : L2 Φ.domain) :
    ‖Φ.weightedL2Pullback Φ.lipschitzDomain Φ.deriv_upper v‖ = ‖v‖ :=
  gradient_norm_extendOfNorm
    (h1Value Φ.domain)
    (Φ.massPullback Φ.lipschitzDomain Φ.deriv_upper)
    (h1Value_denseRange Φ.lipschitzDomain.1.1)
    (mass_norm_eq_value Φ) v

theorem localConformalWeightedL2Pullback_injective :
    Function.Injective (Φ.weightedL2Pullback Φ.lipschitzDomain Φ.deriv_upper) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← norm_localConformalWeightedL2Pullback Φ (u - v),
    map_sub, huv, sub_self, norm_zero]

theorem localConformalWeightedL2Pullback_smooth_ae
    (f : smoothTraceTests) :
    (Φ.weightedL2Pullback Φ.lipschitzDomain Φ.deriv_upper
      (h1Value Φ.domain (smoothTraceH1 Φ.domain f)) : ℂ → ℂ)
      =ᵐ[volume.restrict unitDisk]
        fun z => localConformalMassDensity Φ.map z * f (Φ.map z) := by
  rw [localConformalWeightedL2Pullback_h1Value Φ,
    localConformalMassPullback_smooth_eq Φ f]
  filter_upwards [lpBoundedMultiplier_ae (localConformalMassDensity Φ.map)
    (localConformalMassDensity_aemeasurable Φ)
    (localConformalMassDensity_ae_bound Φ.map Φ.deriv_upper)
    ((smoothTraceTests_memLp unitDisk (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f)).toLp _),
    (smoothTraceTests_memLp unitDisk (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f)).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with z hm hv hz
  rw [hm, hv, smoothDiskCompositionLin_eq_closedDisk Φ.one_lt_radius Φ.map Φ.smooth f (ball_subset_closedBall hz)]

end

end Coordinates

section

variable (F : ℂ → ℂ) (Ω : Set ℂ) (hhol : DifferentiableOn ℂ F unitDisk) (f : smoothTraceTests)
    (i j : Fin 2)

include F i j in
/-- A real Jacobian coordinate divided by the actual conformal scale. -/
def localConformalChainRatio (z : ℂ) : ℂ :=
  (coordRe j (fderiv ℝ F z (coordDir i)) / ‖fderiv ℝ F z 1‖ : ℝ)

private theorem real_fderiv_eq_complex_deriv {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (v : ℂ) :
    fderiv ℝ F z v = deriv F z * v := by
  rw [hF.fderiv_restrictScalars ℝ]
  exact fderiv_eq_deriv_mul

private theorem scale_ne_zero {C : ℝ} {F : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hC : ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {z : ℂ} (hz : z ∈ unitDisk) : ‖fderiv ℝ F z 1‖ ≠ 0 := by
  rw [real_fderiv_eq_complex_deriv (hhol.differentiableAt (isOpen_ball.mem_nhds hz)), mul_one]
  intro hzero
  have h := hC z hz
  rw [hzero] at h
  norm_num at h

theorem norm_localConformalChainRatio_le_one {F : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ F unitDisk) (i j : Fin 2)
    {z : ℂ} (hz : z ∈ unitDisk) : ‖localConformalChainRatio F i j z‖ ≤ 1 := by
  have hn : ‖fderiv ℝ F z (coordDir i)‖ = ‖fderiv ℝ F z 1‖ := by
    simp only [real_fderiv_eq_complex_deriv (hhol.differentiableAt (isOpen_ball.mem_nhds hz)),
      norm_mul, norm_coordDir, mul_one]
  have hb := abs_coordRe_le j (fderiv ℝ F z (coordDir i))
  rw [hn] at hb
  unfold localConformalChainRatio
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg _)]
  by_cases hs : ‖fderiv ℝ F z 1‖ = 0
  · simp [hs]
  · bound

theorem localConformalChainRatio_aestronglyMeasurable :
    AEStronglyMeasurable (localConformalChainRatio F i j)
      (volume.restrict unitDisk) := by
  have hn  :=
    (measurable_fderiv_apply_const ℝ F (1 : ℂ)).norm
  exact (Complex.measurable_ofReal.comp ((measurable_coordRe_fderiv F i j).div hn)).aestronglyMeasurable

include hhol i j in
def localConformalChainRatioMultiplier :
    L2 unitDisk →L[ℂ] L2 unitDisk :=
  lpBoundedMultiplier (C := (1 : ℝ)) (localConformalChainRatio F i j)
    (localConformalChainRatio_aestronglyMeasurable F i j)
    (by filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact norm_localConformalChainRatio_le_one hhol i j hz)

theorem localConformalChainRatioMultiplier_ae
    (v : L2 unitDisk) :
    (localConformalChainRatioMultiplier F hhol i j v : ℂ → ℂ)
      =ᵐ[volume.restrict unitDisk] fun z => localConformalChainRatio F i j z * v z :=
  lpBoundedMultiplier_ae  (localConformalChainRatio F i j)
    (localConformalChainRatio_aestronglyMeasurable F i j)
    (by filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact norm_localConformalChainRatio_le_one hhol i j hz) v

private theorem chainRatio_mul_massDensity {C : ℝ} (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hC : ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (i j : Fin 2) {z : ℂ} (hz : z ∈ unitDisk) :
    localConformalChainRatio F i j z * localConformalMassDensity F z =
      (coordRe j (fderiv ℝ F z (coordDir i)) : ℂ) := by
  unfold localConformalChainRatio localConformalMassDensity
  rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (scale_ne_zero hhol hC hz)]

include f j in
private def smoothTraceDirectionalTest : smoothTraceTests :=
  ⟨dirD (f : ℂ → ℂ) (coordDir j), f.property.dirD (coordDir j)⟩

private theorem smoothTraceDirectionalTest_value :
    h1Value Ω (smoothTraceH1 Ω (smoothTraceDirectionalTest f j)) =
      h1Gradient Ω j (smoothTraceH1 Ω f) := by
  exact MemLp.toLp_congr (smoothTraceTests_memLp Ω (smoothTraceDirectionalTest f j))
    (smoothTraceTests_memLp_deriv Ω f j) (Eventually.of_forall fun _ => rfl)

end

section Components

section

variable (Φ : ControlledDiskMap) (u : NeumannH1 Φ.domain) (i : Fin 2)

def SmoothDiskMap.gradientComponent (Φ : SmoothDiskMap) {K : ℝ}
    (hL : IsLipschitzDomain Φ.domain) (hhol : DifferentiableOn ℂ Φ.map unitDisk)
    (hK : ∀ z ∈ unitDisk, ‖fderiv ℝ Φ.map z 1‖ ≤ K) (i : Fin 2) :
    NeumannH1 Φ.domain →L[ℂ] L2 unitDisk :=
  ∑ j : Fin 2, (localConformalChainRatioMultiplier Φ.map hhol i j).comp
    ((Φ.weightedL2Pullback hL hK).comp
      (h1Gradient Φ.domain j))

private theorem localConformalGradientComponent_smooth
    (f : smoothTraceTests) :
    h1Gradient unitDisk i
      (Φ.h1Pullback Φ.lipschitzDomain (smoothTraceH1 Φ.domain f)) =
      Φ.gradientComponent Φ.lipschitzDomain Φ.holomorphic Φ.deriv_upper i
        (smoothTraceH1 Φ.domain f) := by
  rw [localConformalH1Pullback_smooth Φ f,
    h1Gradient_smoothTraceH1]
  let v (j : Fin 2) := Φ.weightedL2Pullback Φ.lipschitzDomain Φ.deriv_upper
    (h1Gradient Φ.domain j (smoothTraceH1 Φ.domain f))
  have hv (j : Fin 2) : (v j : ℂ → ℂ) =ᵐ[volume.restrict unitDisk]
      fun z => localConformalMassDensity Φ.map z * dirD (f : ℂ → ℂ) (coordDir j) (Φ.map z) := by
    dsimp only [v]
    rw [← smoothTraceDirectionalTest_value]
    exact localConformalWeightedL2Pullback_smooth_ae Φ (smoothTraceDirectionalTest f j)
  simp only [SmoothDiskMap.gradientComponent, Fin.sum_univ_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  
  apply Lp.ext
  filter_upwards [(smoothTraceTests_memLp_deriv unitDisk
    (smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f) i).coeFn_toLp,
    Lp.coeFn_add (localConformalChainRatioMultiplier Φ.map Φ.holomorphic i 0 (v 0))
      (localConformalChainRatioMultiplier Φ.map Φ.holomorphic i 1 (v 1)),
    localConformalChainRatioMultiplier_ae Φ.map Φ.holomorphic i 0 (v 0),
    localConformalChainRatioMultiplier_ae Φ.map Φ.holomorphic i 1 (v 1), hv 0, hv 1,
    ae_restrict_mem measurableSet_ball] with z hd ha h₀ h₁ hv₀ hv₁ hz
  rw [hd, ha]
  simp
  rw [h₀, h₁, hv₀, hv₁, ← mul_assoc, ← mul_assoc,
    chainRatio_mul_massDensity Φ.map Φ.holomorphic Φ.deriv_lower i 0 hz, chainRatio_mul_massDensity Φ.map Φ.holomorphic Φ.deriv_lower i 1 hz,
    fderiv_smoothDiskCompositionLin Φ.one_lt_radius Φ.map Φ.smooth f (ball_subset_closedBall hz)]
  simpa [Fin.sum_univ_two, smul_eq_mul, dirD] using (clm_apply_eq_sum_coordRe (fderiv ℝ (f : ℂ → ℂ) (Φ.map z))
      (fderiv ℝ Φ.map z (coordDir i)))

/-- The full componentwise chain rule for every genuine physical H¹ input. -/
theorem localConformalH1Pullback_gradient_component :
    h1Gradient unitDisk i (Φ.h1Pullback Φ.lipschitzDomain u) =
      Φ.gradientComponent Φ.lipschitzDomain Φ.holomorphic Φ.deriv_upper i u := by
  have hd  :=
    denseRange_smoothTraceH1Lin Φ.bounded Φ.lipschitzDomain
  exact gradient_eq_of_dense
     
    
    (smoothTraceH1 Φ.domain) hd
    (fun v => h1Gradient unitDisk i (Φ.h1Pullback Φ.lipschitzDomain v))
    (Φ.gradientComponent Φ.lipschitzDomain Φ.holomorphic Φ.deriv_upper i)
    ((h1Gradient unitDisk i).continuous.comp
      (Φ.h1Pullback Φ.lipschitzDomain).continuous)
    (Φ.gradientComponent Φ.lipschitzDomain Φ.holomorphic Φ.deriv_upper i).continuous
    (localConformalGradientComponent_smooth Φ i) u

end

end Components

section

variable (F : ℂ → ℂ) (z : ℂ) (hhol : DifferentiableOn ℂ F unitDisk) (v : L2 unitDisk)

include F z in
/-- The actual unit phase converting the antiholomorphic physical derivative
to its conformal-coordinate derivative. -/
def localConformalAntiholomorphicPhase : ℂ :=
  star (fderiv ℝ F z 1) / (‖fderiv ℝ F z 1‖ : ℂ)

theorem antiholomorphicPhase_measurable :
    Measurable (localConformalAntiholomorphicPhase F) := by
  have hd := measurable_fderiv_apply_const ℝ F 1
  exact (Complex.continuous_conj.measurable.comp hd).div (Complex.measurable_ofReal.comp hd.norm)

theorem norm_antiholomorphicPhase_le_one :
    ‖localConformalAntiholomorphicPhase F z‖ ≤ 1 := by
  unfold localConformalAntiholomorphicPhase
  rw [norm_div, norm_star, Complex.norm_of_nonneg (norm_nonneg _)]
  by_cases h : ‖fderiv ℝ F z 1‖ = 0
  · simp [h]
  · simp [*]

include F in
def localConformalAntiholomorphicPhaseMultiplier :
    L2 unitDisk →L[ℂ] L2 unitDisk :=
  lpBoundedMultiplier (localConformalAntiholomorphicPhase F)
    (antiholomorphicPhase_measurable F).aestronglyMeasurable
    (Eventually.of_forall (norm_antiholomorphicPhase_le_one F))

theorem localConformalAntiholomorphicPhaseMultiplier_ae :
    (localConformalAntiholomorphicPhaseMultiplier F v : ℂ → ℂ)
      =ᵐ[volume.restrict unitDisk]
        fun z => localConformalAntiholomorphicPhase F z * v z :=
  lpBoundedMultiplier_ae (localConformalAntiholomorphicPhase F)
    (antiholomorphicPhase_measurable F).aestronglyMeasurable
    (Eventually.of_forall (norm_antiholomorphicPhase_le_one F)) v

include F in
private def antiholomorphicPhaseInverseMultiplier :
    L2 unitDisk →L[ℂ] L2 unitDisk :=
  lpBoundedMultiplier  (fun z => star (localConformalAntiholomorphicPhase F z))
    (Complex.continuous_conj.measurable.comp (antiholomorphicPhase_measurable F)).aestronglyMeasurable
    (Eventually.of_forall (fun z : ℂ => by
      rw [norm_star]
      exact norm_antiholomorphicPhase_le_one F z))

private theorem antiholomorphicPhaseInverseMultiplier_ae :
    (antiholomorphicPhaseInverseMultiplier F v : ℂ → ℂ)
      =ᵐ[volume.restrict unitDisk]
        fun z => star (localConformalAntiholomorphicPhase F z) * v z :=
  lpBoundedMultiplier_ae  (fun z => star (localConformalAntiholomorphicPhase F z))
    (Complex.continuous_conj.measurable.comp (antiholomorphicPhase_measurable F)).aestronglyMeasurable
    (Eventually.of_forall (fun z : ℂ => by
      rw [norm_star]
      exact norm_antiholomorphicPhase_le_one F z)) v

private theorem norm_antiholomorphicPhase_eq_one {C : ℝ} (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hC : ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {z : ℂ} (hz : z ∈ unitDisk) :
    ‖localConformalAntiholomorphicPhase F z‖ = 1 := by
  unfold localConformalAntiholomorphicPhase
  rw [norm_div, norm_star, Complex.norm_of_nonneg (norm_nonneg _),
    div_self (scale_ne_zero hhol hC hz)]

/-- Cancellation of this genuine Jacobian phase on the actual disk L² space. -/
theorem localConformalAntiholomorphicPhaseMultiplier_injective {C : ℝ} (F : ℂ → ℂ)
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hC : ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv F z‖ ^ 2) :
    Function.Injective (localConformalAntiholomorphicPhaseMultiplier F) := by
  have hinv : Function.LeftInverse (antiholomorphicPhaseInverseMultiplier F)
      (localConformalAntiholomorphicPhaseMultiplier F) := by
    intro v
    apply Lp.ext
    filter_upwards [antiholomorphicPhaseInverseMultiplier_ae F
      (localConformalAntiholomorphicPhaseMultiplier F v),
      localConformalAntiholomorphicPhaseMultiplier_ae F v,
      ae_restrict_mem measurableSet_ball] with z hi hd hz
    rw [hi, hd, ← mul_assoc]
    
    simp
    rw [Complex.conj_mul', norm_antiholomorphicPhase_eq_one F hhol hC hz]
    simp
  exact hinv.injective

private theorem antiholomorphicPhase_eq_ratios :
    localConformalAntiholomorphicPhase F z = localConformalChainRatio F 0 0 z +
      (-Complex.I) * localConformalChainRatio F 0 1 z := by
  apply Complex.ext <;>
    simp [localConformalAntiholomorphicPhase, localConformalChainRatio,
      coordDir, coordRe, Complex.div_ofReal_re, Complex.div_ofReal_im, neg_div]

private theorem antiholomorphicPhaseMultiplier_eq_ratios :
    localConformalAntiholomorphicPhaseMultiplier F v =
      localConformalChainRatioMultiplier F hhol 0 0 v +
        (-Complex.I) • localConformalChainRatioMultiplier F hhol 0 1 v := by
  apply Lp.ext
  filter_upwards [localConformalAntiholomorphicPhaseMultiplier_ae F v,
    localConformalChainRatioMultiplier_ae F hhol 0 0 v,
    localConformalChainRatioMultiplier_ae F hhol 0 1 v,
    Lp.coeFn_add (localConformalChainRatioMultiplier F hhol 0 0 v)
      ((-Complex.I) • localConformalChainRatioMultiplier F hhol 0 1 v),
    Lp.coeFn_smul (-Complex.I) (localConformalChainRatioMultiplier F hhol 0 1 v)]
    with z hd h₀ h₁ ha hs
  rw [hd, ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp [smul_eq_mul, h₀, h₁, antiholomorphicPhase_eq_ratios] <;> ring

end

/-- The true chain rule specialized to an actual weak antiholomorphic vector. -/
theorem localConformalH1Pullback_gradient_antiholomorphic (Φ : ControlledDiskMap)
    (u : NeumannH1 Φ.domain)
    (hu : h1Gradient Φ.domain 0 u =
      Complex.I • h1Gradient Φ.domain 1 u) :
    h1Gradient unitDisk 0 (Φ.h1Pullback Φ.lipschitzDomain u) =
      localConformalAntiholomorphicPhaseMultiplier Φ.map
        (Φ.weightedL2Pullback Φ.lipschitzDomain Φ.deriv_upper
          (h1Gradient Φ.domain 0 u)) := by
  have hy : h1Gradient Φ.domain 1 u =
      (-Complex.I) • h1Gradient Φ.domain 0 u := by
    simp [hu, smul_smul]
  rw [localConformalH1Pullback_gradient_component Φ u 0,
    antiholomorphicPhaseMultiplier_eq_ratios Φ.map Φ.holomorphic]
  simp only [SmoothDiskMap.gradientComponent, Fin.sum_univ_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, hy, map_smul]

end PolyaNeumann

end
