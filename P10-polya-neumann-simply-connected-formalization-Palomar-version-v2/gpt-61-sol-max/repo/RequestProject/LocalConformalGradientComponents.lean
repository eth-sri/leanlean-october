module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.LocalConformalMass
public import RequestProject.ChainRule

/-!
# Genuine componentwise conformal transport

The checked physical mass identity extends through the dense H¹ inclusion
to a norm-preserving weighted L² pullback. Bounded coordinate ratios of the
actual Jacobian then transport each actual weak gradient component.
This uses the supplied local conformal map and no plane homeomorphism.
-/

@[expose] public section

open scoped ContDiff


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter

private theorem gradient_extendOfNorm_eq
    {H X Y : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (V : H →L[ℂ] X) (M : H →L[ℂ] Y) (hd : DenseRange V)
    (hn : ∀ u, ‖M u‖ = ‖V u‖) u :
    M.toLinearMap.extendOfNorm V.toLinearMap (V u) = M u := LinearMap.extendOfNorm_eq (f := M.toLinearMap) (e := V.toLinearMap) hd
    ⟨1, fun w => by rw [one_mul]; exact (hn w).le⟩ u

private theorem gradient_norm_extendOfNorm
    {H X Y : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (V : H →L[ℂ] X) (M : H →L[ℂ] Y) (hd : DenseRange V)
    (hn : ∀ u, ‖M u‖ = ‖V u‖) v :
    ‖M.toLinearMap.extendOfNorm V.toLinearMap v‖ = ‖v‖ := by
  let A  := M.toLinearMap.extendOfNorm V.toLinearMap
  refine hd.induction_on (p := fun w => ‖A w‖ = ‖w‖) v ?_ ?_
  · exact isClosed_eq A.continuous.norm continuous_norm
  grind only [gradient_extendOfNorm_eq]

private theorem gradient_eq_of_dense
    {S H Y : Type*} [TopologicalSpace H] [TopologicalSpace Y] [T2Space Y]
    (ι : S → H) (hd : DenseRange ι) (A B : H → Y)
    (hA : Continuous A) (hB : Continuous B)
    (he : ∀ s, A (ι s) = B (ι s)) u : A u = B u := hd.induction_on u (isClosed_eq hA hB) he

section Coordinates

variable {R C K } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)
local notation "massPullbackFixed" => localConformalMassPullback hR F hFs hL hK


include hb hhol hinj hC in
private theorem mass_norm_eq_value u :
    ‖massPullbackFixed u‖ =
      ‖h1Value (F '' unitDisk) u‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (norm_sq_localConformalMassPullback hR F hFs hb hL hhol hinj hC hK u)

/-- The actual Jacobian-weighted pullback on the whole physical L² space. -/
def localConformalWeightedL2Pullback :
    L2 (F '' unitDisk) →L[ℂ] L2 unitDisk :=
  (massPullbackFixed).toLinearMap.extendOfNorm
    (h1Value (F '' unitDisk)).toLinearMap

section
include hb hhol hinj hC

theorem localConformalWeightedL2Pullback_h1Value
    u :
    localConformalWeightedL2Pullback hR F hFs hL hK
      (h1Value (F '' unitDisk) u) =
        massPullbackFixed u :=
  gradient_extendOfNorm_eq
    (h1Value (F '' unitDisk))
    massPullbackFixed
    (h1Value_denseRange hL.1.1)
    (mass_norm_eq_value hR F hFs hb hL hhol hinj hC hK) u

theorem norm_localConformalWeightedL2Pullback
    v :
    ‖localConformalWeightedL2Pullback hR F hFs hL hK v‖ = ‖v‖ :=
  gradient_norm_extendOfNorm
    (h1Value (F '' unitDisk))
    massPullbackFixed
    (h1Value_denseRange hL.1.1)
    (mass_norm_eq_value hR F hFs hb hL hhol hinj hC hK) v

theorem localConformalWeightedL2Pullback_injective :
    Function.Injective (localConformalWeightedL2Pullback hR F hFs hL hK) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← norm_localConformalWeightedL2Pullback hR F hFs hb hL hhol hinj hC hK (u - v),
    map_sub, huv, sub_self, norm_zero]

theorem localConformalWeightedL2Pullback_smooth_ae f :
    (localConformalWeightedL2Pullback hR F hFs hL hK
      (h1Value (F '' unitDisk) (smoothTraceH1 (F '' unitDisk) f)) : PlaneMap)
      =ᵐ[volume.restrict unitDisk]
        fun z => localConformalMassDensity F z * f (F z) := by
  rw [localConformalWeightedL2Pullback_h1Value hR F hFs hb hL hhol hinj hC hK,
    localConformalMassPullback_smooth_eq hR F hFs hb hL hhol hinj hC hK f]
  filter_upwards [lpBoundedMultiplier_ae (localConformalMassDensity F)
    (localConformalMassDensity_aemeasurable hR F hFs)
    (localConformalMassDensity_ae_bound F hK)
    ((smoothTraceTests_memLp (ball 0 1) (smoothDiskCompositionLin hR F hFs f)).toLp _),
    (smoothTraceTests_memLp (ball 0 1) (smoothDiskCompositionLin hR F hFs f)).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with z hm hv hz
  rw [hm, hv, smoothDiskCompositionLin_eq_closedDisk hR F hFs f (ball_subset_closedBall hz)]

end


end Coordinates

/-- A real Jacobian coordinate divided by the actual conformal scale. -/
def localConformalChainRatio (F : PlaneMap) (i j : Coord) (z : ℂ) : ℂ :=
  (coordRe j (fderiv ℝ F z (coordDir i)) / ‖fderiv ℝ F z 1‖ : ℝ)

private theorem real_fderiv_eq_complex_deriv  
    (hF : DifferentiableAt ℂ F z) (v : ℂ) :
    fderiv ℝ F z v = deriv F z * v := by
  rw [hF.fderiv_restrictScalars ℝ]
  change fderiv ℂ F z v = _
  exact fderiv_eq_deriv_mul

private theorem scale_ne_zero  {F : PlaneMap}
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hC : DiskInverseJacobianBound F C)
     (hz : z ∈ unitDisk) : ‖fderiv ℝ F z 1‖ ≠ 0 := by
  rw [real_fderiv_eq_complex_deriv (hhol.differentiableAt (isOpen_ball.mem_nhds hz)), mul_one]
  intro hzero
  have h := hC z hz
  rw [hzero] at h
  norm_num at h

theorem norm_localConformalChainRatio_le_one 
    (hhol : DifferentiableOn ℂ F unitDisk) i j
     (hz : z ∈ unitDisk) : ‖localConformalChainRatio F i j z‖ ≤ 1 := by
  have hn : ‖fderiv ℝ F z (coordDir i)‖ = ‖fderiv ℝ F z 1‖ := by
    simp  [real_fderiv_eq_complex_deriv (hhol.differentiableAt (isOpen_ball.mem_nhds hz)), norm_coordDir]
  have hb := abs_coordRe_le j (fderiv ℝ F z (coordDir i))
  rw [hn] at hb
  unfold localConformalChainRatio
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg _)]
  by_cases hs : ‖fderiv ℝ F z 1‖ = 0
  · simp [hs]
  · exact (div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs))).mpr hb

theorem localConformalChainRatio_aestronglyMeasurable F i j :
    AEStronglyMeasurable (localConformalChainRatio F i j)
      (volume.restrict unitDisk) := (Measurable.aestronglyMeasurable (Measurable.comp Complex.measurable_ofReal (Measurable.div (measurable_coordRe_fderiv F i j) (Measurable.norm (measurable_fderiv_apply_const ℝ F 1)))))

def localConformalChainRatioMultiplier (F : PlaneMap)
    (hhol : DifferentiableOn ℂ F unitDisk) (i j : Coord) :
    L2 unitDisk →L[ℂ] L2 unitDisk :=
  lpBoundedMultiplier (C := (1 : ℝ)) (localConformalChainRatio F i j)
    (localConformalChainRatio_aestronglyMeasurable F i j)
    (by filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        simp_all [norm_localConformalChainRatio_le_one])

theorem localConformalChainRatioMultiplier_ae F
    hhol i j
    v :
    (localConformalChainRatioMultiplier F hhol i j v : PlaneMap)
      =ᵐ[volume.restrict unitDisk] fun z => localConformalChainRatio F i j z * v z :=
  lpBoundedMultiplier_ae (C := (1 : ℝ)) (localConformalChainRatio F i j)
    (localConformalChainRatio_aestronglyMeasurable F i j)
    (by filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        simp_all [norm_localConformalChainRatio_le_one]) v

private theorem chainRatio_mul_massDensity  F
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    i j  (hz : z ∈ unitDisk) :
    localConformalChainRatio F i j z * localConformalMassDensity F z =
      (coordRe j (fderiv ℝ F z (coordDir i)) : ℂ) := by
  unfold localConformalChainRatio localConformalMassDensity
  rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (scale_ne_zero hhol hC hz)]

private def smoothTraceDirectionalTest (f : smoothTraceTests) (j : Coord) : smoothTraceTests :=
  ⟨dirD (f : PlaneMap) (coordDir j), f.property.dirD (coordDir j)⟩

private theorem smoothTraceDirectionalTest_value Ω f j :
    h1Value Ω (smoothTraceH1 Ω (smoothTraceDirectionalTest f j)) =
      h1Gradient Ω j (smoothTraceH1 Ω f) := by
  rw [h1Value_smoothTraceH1, h1Gradient_smoothTraceH1]
  exact MemLp.toLp_congr (smoothTraceTests_memLp Ω (smoothTraceDirectionalTest f j))
    (smoothTraceTests_memLp_deriv Ω f j) (Eventually.of_forall fun _ => rfl)

section Components

variable {R C K } (hR : 1 < R) (F )
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)

def localConformalGradientComponent (i : Coord) :
    NeumannH1 (F '' unitDisk) →L[ℂ] L2 unitDisk :=
  ∑ j : Coord, (localConformalChainRatioMultiplier F hhol i j).comp
    ((localConformalWeightedL2Pullback hR F hFs hL hK).comp
      (h1Gradient (F '' unitDisk) j))

section
include hb hinj hC

private theorem localConformalGradientComponent_smooth i f :
    h1Gradient unitDisk i
      (localConformalH1Pullback hR F hFs hL (smoothTraceH1 (F '' unitDisk) f)) =
      localConformalGradientComponent hR F hFs hL hhol hK i
        (smoothTraceH1 (F '' unitDisk) f) := by
  rw [localConformalH1Pullback_smooth hR F hFs hb hL hhol hinj hC f,
    h1Gradient_smoothTraceH1]
  let v (j : Coord) := localConformalWeightedL2Pullback hR F hFs hL hK
    (h1Gradient (F '' ball 0 1) j (smoothTraceH1 (F '' ball 0 1) f))
  have hv (j : Coord) : (v j : PlaneMap) =ᵐ[volume.restrict unitDisk]
      fun z => localConformalMassDensity F z * dirD (f : PlaneMap) (coordDir j) (F z) := by
    dsimp only [v]
    rw [← smoothTraceDirectionalTest_value]
    exact localConformalWeightedL2Pullback_smooth_ae hR F hFs hb hL hhol hinj hC hK
      (smoothTraceDirectionalTest f j)
  simp only [localConformalGradientComponent, Fin.sum_univ_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  change (smoothTraceTests_memLp_deriv (ball 0 1)
    (smoothDiskCompositionLin hR F hFs f) i).toLp _ =
      localConformalChainRatioMultiplier F hhol i 0 (v 0) +
        localConformalChainRatioMultiplier F hhol i 1 (v 1)
  apply Lp.ext
  filter_upwards [(smoothTraceTests_memLp_deriv (ball 0 1)
    (smoothDiskCompositionLin hR F hFs f) i).coeFn_toLp,
    Lp.coeFn_add (localConformalChainRatioMultiplier F hhol i 0 (v 0))
      (localConformalChainRatioMultiplier F hhol i 1 (v 1)),
    localConformalChainRatioMultiplier_ae F hhol i 0 (v 0),
    localConformalChainRatioMultiplier_ae F hhol i 1 (v 1), hv 0, hv 1,
    ae_restrict_mem measurableSet_ball] with z hd ha h₀ h₁ hv₀ hv₁ hz
  rw [hd, ha]
  simp  
  rw [h₀, h₁, hv₀, hv₁, ← mul_assoc, ← mul_assoc,
    chainRatio_mul_massDensity F hhol hC i 0 hz, chainRatio_mul_massDensity F hhol hC i 1 hz,
    fderiv_smoothDiskCompositionLin hR F hFs f (ball_subset_closedBall hz)]
  change (fderiv ℝ f (F z)) (fderiv ℝ F z (coordDir i)) = _
  simpa only [Fin.sum_univ_two, smul_eq_mul, dirD] using
    (clm_apply_eq_sum_coordRe (fderiv ℝ f (F z))
      (fderiv ℝ F z (coordDir i)))

/-- The full componentwise chain rule for every genuine physical H¹ input. -/
theorem localConformalH1Pullback_gradient_component
    u i :
    h1Gradient unitDisk i (localConformalH1Pullback hR F hFs hL u) =
      localConformalGradientComponent hR F hFs hL hhol hK i u := by
  have hd  :=
    denseRange_smoothTraceH1Lin hb hL
  exact gradient_eq_of_dense
    (S := smoothTraceTests) (H := NeumannH1 (F '' ball 0 1))
    (Y := L2 (ball 0 1))
    ((smoothTraceH1 (F '' ball 0 1))) hd
    (fun v => h1Gradient (ball 0 1) i (localConformalH1Pullback hR F hFs hL v))
    ((localConformalGradientComponent hR F hFs hL hhol hK i))
    ((h1Gradient (ball 0 1) i).continuous.comp
      (localConformalH1Pullback hR F hFs hL).continuous)
    (localConformalGradientComponent hR F hFs hL hhol hK i).continuous
    (localConformalGradientComponent_smooth hR F hFs hb hL hhol hinj hC hK i) u

end


end Components

/-- The actual unit phase converting the antiholomorphic physical derivative
to its conformal-coordinate derivative. -/
def localConformalAntiholomorphicPhase F (z : ℂ)  :=
  star (fderiv ℝ F z 1) / (‖fderiv ℝ F z 1‖ : ℂ)

theorem antiholomorphicPhase_measurable F :
    Measurable (localConformalAntiholomorphicPhase F) := by
  have hd := measurable_fderiv_apply_const ℝ F 1
  exact (Complex.continuous_conj.measurable.comp hd).div (Complex.measurable_ofReal.comp hd.norm)

theorem norm_antiholomorphicPhase_le_one F z :
    ‖localConformalAntiholomorphicPhase F z‖ ≤ 1 := by
  unfold localConformalAntiholomorphicPhase
  rw [norm_div, norm_star, Complex.norm_of_nonneg (norm_nonneg _)]
  bound

def localConformalAntiholomorphicPhaseMultiplier (F : PlaneMap) :
    L2 unitDisk →L[ℂ] L2 unitDisk :=
  lpBoundedMultiplier (localConformalAntiholomorphicPhase F)
    (antiholomorphicPhase_measurable F).aestronglyMeasurable
    (Eventually.of_forall (norm_antiholomorphicPhase_le_one F))

theorem localConformalAntiholomorphicPhaseMultiplier_ae F
    v :
    (localConformalAntiholomorphicPhaseMultiplier F v : PlaneMap)
      =ᵐ[volume.restrict unitDisk]
        fun z => localConformalAntiholomorphicPhase F z * v z :=
  lpBoundedMultiplier_ae (localConformalAntiholomorphicPhase F)
    (antiholomorphicPhase_measurable F).aestronglyMeasurable
    (Eventually.of_forall (norm_antiholomorphicPhase_le_one F)) v

private def antiholomorphicPhaseInverseMultiplier (F : PlaneMap) :
    L2 unitDisk →L[ℂ] L2 unitDisk :=
  lpBoundedMultiplier (C := (1 : ℝ)) (fun z => star (localConformalAntiholomorphicPhase F z))
    (Complex.continuous_conj.measurable.comp (antiholomorphicPhase_measurable F)).aestronglyMeasurable
    (Eventually.of_forall (fun z : ℂ => by
      simp_all [norm_antiholomorphicPhase_le_one]))

private theorem antiholomorphicPhaseInverseMultiplier_ae F
    v :
    (antiholomorphicPhaseInverseMultiplier F v : PlaneMap)
      =ᵐ[volume.restrict unitDisk]
        fun z => star (localConformalAntiholomorphicPhase F z) * v z :=
  lpBoundedMultiplier_ae (C := (1 : ℝ)) (fun z => star (localConformalAntiholomorphicPhase F z))
    (Complex.continuous_conj.measurable.comp (antiholomorphicPhase_measurable F)).aestronglyMeasurable
    (Eventually.of_forall (fun z : ℂ => by
      simp_all [norm_antiholomorphicPhase_le_one])) v

section
variable {C } (F : PlaneMap) (hhol : DifferentiableOn ℂ F unitDisk) (hC : DiskInverseJacobianBound F C)
include C F hhol hC

private theorem norm_antiholomorphicPhase_eq_one
     (hz : z ∈ unitDisk) :
    ‖localConformalAntiholomorphicPhase F z‖ = 1 := by
  unfold localConformalAntiholomorphicPhase
  rw [norm_div, norm_star, Complex.norm_of_nonneg (norm_nonneg _),
    div_self (scale_ne_zero hhol hC hz)]

/-- Cancellation of this genuine Jacobian phase on the actual disk L² space. -/
theorem localConformalAntiholomorphicPhaseMultiplier_injective :
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

end


private theorem antiholomorphicPhase_eq_ratios F z :
    localConformalAntiholomorphicPhase F z = localConformalChainRatio F 0 0 z +
      (-Complex.I) * localConformalChainRatio F 0 1 z := by
  apply Complex.ext <;>
    simp [localConformalAntiholomorphicPhase, localConformalChainRatio, coordDir, coordRe, neg_div]

private theorem antiholomorphicPhaseMultiplier_eq_ratios F
    hhol v :
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
  simp_all [antiholomorphicPhase_eq_ratios, PolyaNeumann.L2] <;> ring

/-- The true chain rule specialized to an actual weak antiholomorphic vector. -/
theorem localConformalH1Pullback_gradient_antiholomorphic {R C K : ℝ}
    (hR : 1 < R) (F : PlaneMap)
    (hFs : RealSmoothOnBall F R)
    (hb : Bornology.IsBounded (F '' unitDisk))
    (hL : IsLipschitzDomain (F '' unitDisk))
    (hhol : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hC : DiskInverseJacobianBound F C)
    (hK : DiskDerivativeBound F K)
    (u : NeumannH1 (F '' unitDisk))
    (hu : h1Gradient (F '' unitDisk) 0 u =
      Complex.I • h1Gradient (F '' unitDisk) 1 u) :
    h1Gradient unitDisk 0 (localConformalH1Pullback hR F hFs hL u) =
      localConformalAntiholomorphicPhaseMultiplier F
        (localConformalWeightedL2Pullback hR F hFs hL hK
          (h1Gradient (F '' unitDisk) 0 u)) := by
  have hy : h1Gradient (F '' unitDisk) 1 u =
      (-Complex.I) • h1Gradient (F '' unitDisk) 0 u := by
    rw [hu, smul_smul]
    simp
  rw [localConformalH1Pullback_gradient_component hR F hFs hb hL hhol hinj hC hK u 0,
    antiholomorphicPhaseMultiplier_eq_ratios F hhol]
  simp  [localConformalGradientComponent, hy]

end PolyaNeumann

end
