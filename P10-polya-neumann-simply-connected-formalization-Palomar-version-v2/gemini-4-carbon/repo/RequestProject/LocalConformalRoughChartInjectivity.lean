module

public import RequestProject.BoundaryFourier
public import RequestProject.BoundaryFourierMultiplier
public import RequestProject.FiniteFourierChartRemainder
public import RequestProject.LocalConformalPrincipalFactorization
public import RequestProject.PhysicalDrivenIntegrable
public import RequestProject.PhysicalDrivenHardyRegularity
public import RequestProject.PhysicalMomentHardyCriterion
public import RequestProject.LocalConformalArcReparam
public import RequestProject.LocalConformalVekuaTransport
public import RequestProject.LocalConformalHardySubspace
public import RequestProject.LocalConformalRadialVekua
public import RequestProject.PositiveFourierBasis
public import RequestProject.ObservationLp
public import RequestProject.ReducedForm

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann

open Set MeasureTheory Filter Metric ContinuousLinearMap
open AbsolutelyContinuousOnInterval
open scoped Topology InnerProductSpace ComplexConjugate

local instance roughChartTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
local notation "H₀" => nonpositiveFourierSubspace

/-! ### Shared boundary AC & L² helpers -/

private theorem rough_smul_contOn_memLp (p : BoundaryL2) {k : ℝ → Ell2}
    (hk : ContinuousOn k (Icc 0 (2 * Real.pi))) : MemLp (fun θ => p θ • k θ) 2 μB := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hk
  refine (Lp.memLp p).of_le_mul (c := C) ((Lp.memLp p).aestronglyMeasurable.smul
    ((hk.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  change ‖p θ • k θ‖ ≤ C * ‖p θ‖
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC θ (Ioc_subset_Icc_self hθ)) (norm_nonneg _)

/-! ### Rough normalized Fourier primitive -/

private def roughPrimSym (n : ℤ) : ℂ :=
  if n = 0 then 0 else (Real.sqrt (sobWeight n) : ℂ) / (Complex.I * (n : ℂ))

private theorem norm_roughPrimSym_le (n : ℤ) : ‖roughPrimSym n‖ ≤ 2 := by
  by_cases hn : n = 0
  · simp [roughPrimSym, hn]
  · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have hle : Real.sqrt (sobWeight n) ≤ 2 * |(n : ℝ)| := by
      rw [Real.sqrt_le_left (by positivity)]; unfold sobWeight; nlinarith
    simp only [roughPrimSym, if_neg hn, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
    exact (div_le_iff₀ (by positivity)).mpr hle

private def roughNormalizedPrimitive (y : L2Z) : BoundaryL2 :=
  boundaryFourier.symm (diagOp roughPrimSym 2 norm_roughPrimSym_le y)

private theorem roughNormalizedPrimitive_deriv_ne_zero (y : L2Z) {n : ℤ} (hn : n ≠ 0) :
    (Complex.I * (n : ℂ)) * boundaryFourier (roughNormalizedPrimitive y) n =
      (Real.sqrt (sobWeight n) : ℂ) * y n := by
  simp only [roughNormalizedPrimitive, boundaryFourier.apply_symm_apply, diagOp_apply,
    roughPrimSym, if_neg hn, ← mul_assoc]
  rw [mul_div_cancel₀ _ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn))]

private theorem roughNormalizedPrimitive_deriv (y : L2Z) (n : ℤ) :
    (Complex.I * (n : ℂ)) * boundaryFourier (roughNormalizedPrimitive y) n =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (y - zeroModeProjection y) n := by
  by_cases hn : n = 0
  · subst n; simp [zeroModeProjection_apply]
  · rw [roughNormalizedPrimitive_deriv_ne_zero y hn, ← Real.sqrt_eq_rpow]
    simp only [lp.coeFn_sub, Pi.sub_apply, zeroModeProjection_apply, if_neg hn, zero_mul, sub_zero]

private theorem finiteFourierChart_half_of_rough_primitive_pos_one {d : ℕ}
    (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite) (z : H₀ᗮ)
    (hp : IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive (finiteFourierChart u v z))) : ℤ → ℂ)) :
    IsSobolevSeq (1 / 2 : ℝ) (finiteFourierChart u v z : ℤ → ℂ) := by
  let y := finiteFourierChart u v z
  have hypos : IsSobolevSeq (1 / 2 : ℝ) (posProj y : ℤ → ℂ) := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_) hp
    by_cases hn : 0 < n
    · have he := congrArg norm (roughNormalizedPrimitive_deriv_ne_zero y hn.ne')
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at he
      simp only [posProj, diagOp_apply, if_pos hn, one_mul, Real.rpow_one, ← Real.sqrt_eq_rpow, ← he]
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right
        (by unfold sobWeight; linarith [abs_nonneg (n : ℝ)]) (norm_nonneg _)) 2
    · simp [posProj, diagOp_apply, hn]
  have hfin : (Function.support (((1 - posProj) y : L2Z) : ℤ → ℂ)).Finite := by
    have hmem : y - (z : L2Z) ∈ finiteFourierSubmodule := by
      simp only [y, finiteFourierChart, ContinuousLinearMap.add_apply, Submodule.subtypeL_apply,
        add_sub_cancel_left, ContinuousLinearMap.sum_apply]
      exact Submodule.sum_mem _ fun r _ => by
        rw [InnerProductSpace.rankOne_apply]; exact finiteFourierSubmodule.smul_mem _ (hv r)
    have hz0 : (1 - posProj) (z : L2Z) = 0 := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        ← nonpositive_orthogonal_starProjection, Submodule.starProjection_mem_subspace_eq_self, sub_self]
    set w : L2Z := y - (z : L2Z)
    rw [show (1 - posProj) y = (1 - posProj) w by dsimp [w]; rw [map_sub, hz0, sub_zero]]
    refine hmem.subset fun n hn => by
      by_contra h0
      have hwz : w n = 0 := not_not.mp h0
      exact hn (by simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        lp.coeFn_sub, Pi.sub_apply, posProj, diagOp_apply, hwz])
  change y ∈ fourierSobolevSubmodule (1 / 2 : ℝ)
  rw [show y = posProj y + (1 - posProj) y by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]; abel]
  exact (fourierSobolevSubmodule (1 / 2 : ℝ)).add_mem hypos
    (isSobolevSeq_of_finite_fourier_support (1 / 2 : ℝ) hfin)

/-! ### Rough Vekua transport & periodic regular correction -/

private def roughVekuaRegularForce (γ : ℝ → ℂ) (E : ℝ) (p : BoundaryL2) (m : ℂ) (θ : ℝ) : Ell2 :=
  p θ • transportCoeff γ E θ (basisVec 0) + m • basisVec 0

private def roughVekuaRegularCorrection (γ : ℝ → ℂ) (E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2) (p : BoundaryL2) (m α : ℂ) (θ : ℝ) : Ell2 :=
  W θ (α • basisVec 0 + (-(Complex.I / (Real.sqrt 2 : ℂ))) •
    (∫ s in (0 : ℝ)..θ,
      ContinuousLinearMap.adjoint (W s) (roughVekuaRegularForce γ E p m s)))

private def roughVekuaDrivenVector (γ : ℝ → ℂ) (E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2) (p : BoundaryL2) (m α : ℂ) (θ : ℝ) : Ell2 :=
  (-(Complex.I / (Real.sqrt 2 : ℂ)) * p θ) • basisVec 0 +
    roughVekuaRegularCorrection γ E W p m α θ

section RoughTransport

variable {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) (hγ : ContDiff ℝ 1 γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)

include hγ in
private theorem rough_transportCoeff_continuous : Continuous (transportCoeff γ E) := by
  have hd := hγ.continuous_deriv_one
  have hc := Complex.continuous_conj.comp hd
  unfold transportCoeff; fun_prop

include hK hγ hW in
private theorem roughVekuaRegularIntegrand_memLp (p : BoundaryL2) (m : ℂ) :
    MemLp (fun θ => ContinuousLinearMap.adjoint (W θ) (roughVekuaRegularForce γ E p m θ)) 2 μB := by
  have hk : ContinuousOn (fun θ => transportCoeff γ E θ (basisVec 0)) (Icc 0 (2 * Real.pi)) :=
    (rough_transportCoeff_continuous (E := E) hγ).continuousOn.clm_apply continuousOn_const
  have hA : MemLp (roughVekuaRegularForce γ E p m) 2 μB :=
    (rough_smul_contOn_memLp p hk).add (memLp_const (m • basisVec 0))
  have hWa := (ContinuousLinearMap.adjoint.continuous.comp_continuousOn hW.1).mono Ioc_subset_Icc_self
  refine hA.of_le_mul (c := 1) ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    ((hWa.aestronglyMeasurable measurableSet_Ioc).prodMk hA.aestronglyMeasurable)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  refine ((ContinuousLinearMap.adjoint (W θ)).le_opNorm _).trans ?_
  rw [LinearIsometryEquiv.norm_map, one_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (norm_transport_le_one (E := E) (W := W) hK hW (Ioc_subset_Icc_self hθ)) (norm_nonneg _)

include hK hγ hW in
private theorem roughVekuaRegularIntegrand_intervalIntegrable (p : BoundaryL2) (m : ℂ) :
    IntervalIntegrable (fun θ => ContinuousLinearMap.adjoint (W θ)
      (roughVekuaRegularForce γ E p m θ)) volume 0 (2 * Real.pi) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
    ((roughVekuaRegularIntegrand_memLp hK hγ hW p m).integrable (by norm_num))

include hK hγ hW in
private theorem roughVekuaRegularCorrection_continuousOn (p : BoundaryL2) (m α : ℂ) :
    ContinuousOn (roughVekuaRegularCorrection γ E W p m α) (Icc 0 (2 * Real.pi)) := by
  have hi : IntegrableOn (fun θ => ContinuousLinearMap.adjoint (W θ)
      (roughVekuaRegularForce γ E p m θ)) (uIcc 0 (2 * Real.pi)) := by
    rw [uIcc_of_le Real.two_pi_pos.le, integrableOn_Icc_iff_integrableOn_Ioc]
    exact (roughVekuaRegularIntegrand_memLp hK hγ hW p m).integrable (by norm_num)
  have hp := intervalIntegral.continuousOn_primitive_interval hi
  rw [uIcc_of_le Real.two_pi_pos.le] at hp
  have hc : ContinuousOn (fun θ => α • basisVec 0 + (-(Complex.I / (Real.sqrt 2 : ℂ))) •
      (∫ s in (0 : ℝ)..θ,
        ContinuousLinearMap.adjoint (W s) (roughVekuaRegularForce γ E p m s)))
      (Icc 0 (2 * Real.pi)) :=
    continuousOn_const.add (ContinuousOn.const_smul hp (-(Complex.I / (Real.sqrt 2 : ℂ))))
  exact hW.1.clm_apply hc

include hK hγ hW in
private theorem roughVekuaRegularCorrection_absolutelyContinuous (p : BoundaryL2) (m α : ℂ) :
    AbsolutelyContinuousOnInterval (roughVekuaRegularCorrection γ E W p m α) 0 (2 * Real.pi) := by
  obtain ⟨L, hL⟩ := volterra_lipschitzOn (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) hW.1 hW.2
  have hWA : AbsolutelyContinuousOnInterval W 0 (2 * Real.pi) :=
    (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hL :
      LipschitzOnWith L W _).absolutelyContinuousOnInterval
  have hp := absolutelyContinuousOnInterval_intervalIntegral_banach
    (roughVekuaRegularIntegrand_intervalIntegrable hK hγ hW p m)
    (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩)
  exact absolutelyContinuousOnInterval_clm_apply hWA
    ((LipschitzWith.const (α • basisVec 0)).lipschitzOnWith.absolutelyContinuousOnInterval.add
      (hp.const_smul _))

include hK hγ hW in
private theorem roughVekuaRegularCorrection_ae_hasDerivAt (p : BoundaryL2) (m α : ℂ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (roughVekuaRegularCorrection γ E W p m α)
        (transportCoeff γ E θ (roughVekuaRegularCorrection γ E W p m α θ) +
          (-(Complex.I / (Real.sqrt 2 : ℂ))) • roughVekuaRegularForce γ E p m θ) θ := by
  filter_upwards [ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le
    (roughVekuaRegularIntegrand_intervalIntegrable hK hγ hW p m)] with θ hA hθ
  have hc := Ioo_subset_Icc_self hθ
  have hdW := (hasDerivWithinAt_transport hγ.continuous_deriv_one.continuousOn hW hc).hasDerivAt
    (Icc_mem_nhds hθ.1 hθ.2)
  have hd := hasDerivAt_clm_apply_real hdW
    ((hasDerivAt_const θ (α • basisVec 0)).add ((hA hθ).const_smul (-(Complex.I / (Real.sqrt 2 : ℂ)))))
  have hcancel : W θ (ContinuousLinearMap.adjoint (W θ) (roughVekuaRegularForce γ E p m θ)) =
      roughVekuaRegularForce γ E p m θ := by
    rw [← ContinuousLinearMap.mul_apply, transport_mul_adjoint hK hW hc, ContinuousLinearMap.one_apply]
  have hd' : HasDerivAt (roughVekuaRegularCorrection γ E W p m α) _ θ := hd
  refine hd'.congr_deriv ?_
  dsimp only [roughVekuaRegularCorrection]
  simp only [Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.mul_apply, map_zero,
    add_zero, zero_add, map_smul, hcancel]

include hW in
private theorem roughVekuaRegularCorrection_zero (p : BoundaryL2) (m α : ℂ) :
    roughVekuaRegularCorrection γ E W p m α 0 = α • basisVec 0 := by
  simp [roughVekuaRegularCorrection, transport_zero_eq hW]

private def roughProjObsDeriv (γ : ℝ → ℂ) (E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2) (v : Ell2) (θ : ℝ) : ℂ :=
  -⟪ContinuousLinearMap.adjoint (W θ) (transportCoeff γ E θ (basisVec 0)),
    cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) v⟫_ℂ

include hγ hW in
private theorem roughProjObs_hasDerivAt (v : Ell2) {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    HasDerivAt (fun t => ⟪projObsRow W t, v⟫_ℂ) (roughProjObsDeriv γ E W v θ) θ := by
  have hdW := (hasDerivWithinAt_transport hγ.continuous_deriv_one.continuousOn hW
    (Ioo_subset_Icc_self hθ)).hasDerivAt (Icc_mem_nhds hθ.1 hθ.2)
  have hdA : HasDerivAt (fun t => ContinuousLinearMap.adjoint (W t))
      (-(ContinuousLinearMap.adjoint (W θ) * transportCoeff γ E θ)) θ := by
    have hstar := hdW.star
    rw [star_mul, transportCoeff_star γ E θ, ContinuousLinearMap.star_eq_adjoint, mul_neg] at hstar
    exact hstar
  have hd0 : HasDerivAt (fun t => ContinuousLinearMap.adjoint (W t) (basisVec 0))
      (-(ContinuousLinearMap.adjoint (W θ) (transportCoeff γ E θ (basisVec 0)))) θ := by
    simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply, map_zero, add_zero] using
      hasDerivAt_clm_apply_real hdA (hasDerivAt_const θ (basisVec 0))
  let Q := cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
  convert ((Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ hd0).inner ℂ
    (hasDerivAt_const θ v) using 1 <;>
    simp [projObsRow, roughProjObsDeriv, Q, Function.comp_def, ContinuousLinearMap.coe_restrictScalars,
      map_neg, inner_zero_right, inner_neg_left, inner_cutProj_left, inner_conj_symm]

include hK hW in
private theorem roughProjObs_ac (v : Ell2) :
    AbsolutelyContinuousOnInterval (fun t => ⟪projObsRow W t, v⟫_ℂ) 0 (2 * Real.pi) := by
  let M : NNReal := ⟨Real.sqrt E * shiftConst * K * ‖v‖,
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) shiftConst_nonneg) K.coe_nonneg)
      (norm_nonneg _)⟩
  have hl : LipschitzOnWith M (fun t => ⟪projObsRow W t, v⟫_ℂ) (Icc 0 (2 * Real.pi)) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      rw [dist_eq_norm, ← inner_sub_left, Real.dist_eq]
      calc ‖⟪projObsRow W x - projObsRow W y, v⟫_ℂ‖
          ≤ ‖projObsRow W x - projObsRow W y‖ * ‖v‖ := norm_inner_le_norm _ _
        _ ≤ (Real.sqrt E * shiftConst * K * |x - y|) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (norm_projObsRow_sub_le hK hW hx hy) (norm_nonneg _)
        _ = M * |x - y| := by change _ = (Real.sqrt E * shiftConst * K * ‖v‖) * |x - y|; ring
  exact (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hl :
    LipschitzOnWith M _ _).absolutelyContinuousOnInterval

include hK hγ hW in
private theorem roughVekuaRegularCorrection_exists_periodic_of_projObsDual_eq_zero
    (y : L2Z) (hy : projObsDual W y = 0) :
    ∃ α : ℂ, roughVekuaRegularCorrection γ E W (roughNormalizedPrimitive y)
      (y 0 / (Real.sqrt (2 * Real.pi) : ℂ)) α (2 * Real.pi) = α • basisVec 0 := by
  let p := roughNormalizedPrimitive y
  let m : ℂ := y 0 / (Real.sqrt (2 * Real.pi) : ℂ)
  let c : Ell2 := cutC (W (2 * Real.pi)) (basisVec 0)
  let k : ℝ → Ell2 := fun θ => ContinuousLinearMap.adjoint (W θ) (transportCoeff γ E θ (basisVec 0))
  have hk : ContinuousOn k (Icc 0 (2 * Real.pi)) :=
    (ContinuousLinearMap.adjoint.continuous.comp_continuousOn hW.1).clm_apply
      ((rough_transportCoeff_continuous (E := E) hγ).continuousOn.clm_apply continuousOn_const)
  have h0 : ContinuousOn (fun θ => ContinuousLinearMap.adjoint (W θ) (basisVec 0)) (Icc 0 (2 * Real.pi)) :=
    continuousOn_adjoint_apply hW.1 (basisVec 0)
  have hik : IntervalIntegrable (fun θ => p θ • k θ) volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
      ((rough_smul_contOn_memLp p hk).integrable (by norm_num))
  have hi0 : IntervalIntegrable (fun θ => ContinuousLinearMap.adjoint (W θ) (basisVec 0))
      volume 0 (2 * Real.pi) :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le Real.two_pi_pos.le] using h0)
  let I_y : Ell2 := ∫ θ in (0 : ℝ)..(2 * Real.pi),
    ContinuousLinearMap.adjoint (W θ) (roughVekuaRegularForce γ E p m θ)
  have hsplit_I : I_y = (∫ θ in (0 : ℝ)..(2 * Real.pi), p θ • k θ) +
      m • (∫ θ in (0 : ℝ)..(2 * Real.pi), ContinuousLinearMap.adjoint (W θ) (basisVec 0)) := by
    have him : IntervalIntegrable (fun θ => m • ContinuousLinearMap.adjoint (W θ) (basisVec 0))
        volume 0 (2 * Real.pi) := hi0.smul m
    rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_add hik him]
    exact intervalIntegral.integral_congr fun θ _ => by
      simp only [roughVekuaRegularForce, k, map_add, map_smul]
  have hproj : cutProj c I_y = 0 := by
    apply ext_inner_left ℂ; intro v
    rw [inner_zero_right, ← inner_cutProj_left, hsplit_I, inner_add_right, inner_smul_right]
    let g := projectedObservationBoundary hK hW v
    have hg'_mem : MemLp (roughProjObsDeriv γ E W v) 2 μB :=
      continuousOn_memLp_boundary (hk.inner continuousOn_const).neg
    let g' : BoundaryL2 := hg'_mem.toLp (roughProjObsDeriv γ E W v)
    have hp_end : (⟪projObsRow W 0, v⟫_ℂ) = ⟪projObsRow W (2 * Real.pi), v⟫_ℂ := by
      rw [projObsRow_endpoint hW]
    have hg_sob : IsSobolevSeq 1 (boundaryFourier g : ℤ → ℂ) := by
      have hr := isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt
        (roughProjObs_ac hK hW v) hg'_mem
        (Eventually.of_forall fun θ hθ => roughProjObs_hasDerivAt hγ hW v hθ) hp_end
      rw [show (boundaryFourier g : ℤ → ℂ) = (Real.sqrt (2 * Real.pi) : ℂ) •
        fourierCoeffOn Real.two_pi_pos (fun θ => ⟪projObsRow W θ, v⟫_ℂ) from funext fun n => by
          rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos
            (projectedObservationBoundary_coe hK hW v)]; rfl]
      exact isSobolevSeq_smul _ hr
    have hg_half := (sobNormSq_mono (by norm_num : (1 / 2 : ℝ) ≤ 1) hg_sob).1
    have hterm1 : ⟪cutProj c v, ∫ θ in (0 : ℝ)..(2 * Real.pi), p θ • k θ⟫_ℂ =
        ⟪sobVec (1 / 2 : ℝ) (boundaryFourier g : ℤ → ℂ) hg_half, y - zeroModeProjection y⟫_ℂ := by
      have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ (cutProj c v)) hik
      simp only [innerSL_apply_apply] at hcomm
      have hint : ⟪cutProj c v, ∫ θ in (0 : ℝ)..(2 * Real.pi), p θ • k θ⟫_ℂ = -⟪g', p⟫_ℂ := by
        rw [← hcomm, L2.inner_def, intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_neg]
        refine integral_congr_ae ?_
        filter_upwards [hg'_mem.coeFn_toLp] with θ hθ
        simp only [innerSL_apply_apply, inner_smul_right, RCLike.inner_apply', g', hθ,
          roughProjObsDeriv, map_neg, inner_conj_symm, k, c]
        ring
      rw [hint, ← boundaryFourier.inner_map_map, lp.inner_eq_tsum, lp.inner_eq_tsum, ← tsum_neg]
      refine tsum_congr fun n => ?_
      have hd_four : boundaryFourier g' n = (Complex.I * (n : ℂ)) * boundaryFourier g n := by
        simp only [g', g, boundaryFourier_apply]
        rw [fourierCoeffOn_congr_ae Real.two_pi_pos hg'_mem.coeFn_toLp,
          fourierCoeffOn_of_ac_ae_hasDerivAt (roughProjObs_ac hK hW v) hg'_mem
            (Eventually.of_forall fun θ hθ => roughProjObs_hasDerivAt hγ hW v hθ) hp_end,
          fourierCoeffOn_congr_ae Real.two_pi_pos (projectedObservationBoundary_coe hK hW v)]
        ring
      simp only [RCLike.inner_apply', sobVec_apply, hd_four, map_mul, Complex.conj_I,
        map_intCast, Complex.conj_ofReal]
      calc -((-Complex.I * (n : ℂ) * conj (boundaryFourier g n)) * boundaryFourier p n)
          = conj (boundaryFourier g n) * ((Complex.I * (n : ℂ)) * boundaryFourier p n) := by ring
        _ = conj (boundaryFourier g n) *
              (((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (y - zeroModeProjection y) n) := by
              rw [roughNormalizedPrimitive_deriv]
        _ = _ := by ring
    have hterm2 : m * ⟪cutProj c v, ∫ θ in (0 : ℝ)..(2 * Real.pi),
          ContinuousLinearMap.adjoint (W θ) (basisVec 0)⟫_ℂ =
        ⟪sobVec (1 / 2 : ℝ) (boundaryFourier g : ℤ → ℂ) hg_half, zeroModeProjection y⟫_ℂ := by
      have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ (cutProj c v)) hi0
      simp only [innerSL_apply_apply] at hcomm
      rw [← hcomm]
      have hinner (θ : ℝ) : ⟪cutProj c v, ContinuousLinearMap.adjoint (W θ) (basisVec 0)⟫_ℂ =
          conj (⟪projObsRow W θ, v⟫_ℂ) :=
        (inner_cutProj_left _ v _).trans (inner_conj_symm v _).symm
      simp only [hinner]
      rw [intervalIntegral_conj, zeroModeProjection_eq_single, lp.inner_single_right,
        RCLike.inner_apply', sobVec_apply]
      simp only [sobWeight, Int.cast_zero, abs_zero, add_zero, Real.one_rpow, Complex.ofReal_one,
        one_mul]
      rw [boundaryFourier_apply,
        fourierCoeffOn_congr_ae Real.two_pi_pos (projectedObservationBoundary_coe hK hW v),
        fourierCoeffOn_eq_integral]
      simp only [neg_zero, fourier_zero, one_smul, sub_zero, Complex.real_smul,
        map_mul, Complex.conj_ofReal, m]
      have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 :=
        by exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
      have hsq : (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 = ((2 * Real.pi : ℝ) : ℂ) :=
        by exact_mod_cast Real.sq_sqrt Real.two_pi_pos.le
      have hT : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
      field_simp [hs, hT, Real.pi_ne_zero]
      rw [hsq]
      have hprod : ((Real.pi * 2 : ℝ) : ℂ) * ((Real.pi⁻¹ * (1 / 2) : ℝ) : ℂ) = 1 := by
        exact_mod_cast (by field_simp [Real.pi_ne_zero] :
          (Real.pi * 2) * (Real.pi⁻¹ * (1 / 2)) = (1 : ℝ))
      calc _ = (y 0) * conj (∫ x in (0 : ℝ)..Real.pi * 2, ⟪projObsRow W x, v⟫_ℂ) * 1 := by ring
        _ = (y 0) * conj (∫ x in (0 : ℝ)..Real.pi * 2, ⟪projObsRow W x, v⟫_ℂ) *
              (((Real.pi * 2 : ℝ) : ℂ) * ((Real.pi⁻¹ * (1 / 2) : ℝ) : ℂ)) := by rw [hprod]
        _ = _ := by ring
    have hwF : sobVec (1 / 2 : ℝ) (boundaryFourier g : ℤ → ℂ) hg_half =
        (Real.sqrt (2 * Real.pi) : ℂ) • rowAnalysis (normProjObsRow W) (summable_normProjObsRow hK hW) v := by
      apply lp.ext; funext n
      simp only [sobVec_apply, g, boundaryFourier_projectedObservation hK hW, lp.coeFn_smul,
        Pi.smul_apply, smul_eq_mul, rowAnalysis_apply, normProjObsRow, inner_smul_left,
        Complex.conj_ofReal, ← Real.sqrt_eq_rpow]
      change (Real.sqrt (sobWeight n) : ℂ) *
          ((Real.sqrt (2 * Real.pi) : ℂ) * ⟪projObsCoeffVec W n, v⟫_ℂ) =
        (Real.sqrt (2 * Real.pi) : ℂ) *
          ((Real.sqrt (sobWeight n) : ℂ) * ⟪projObsCoeffVec W n, v⟫_ℂ)
      ring
    rw [hterm1, hterm2, ← inner_add_right, sub_add_cancel, hwF, inner_smul_left,
      Complex.conj_ofReal, ← ContinuousLinearMap.adjoint_inner_right]
    change (Real.sqrt (2 * Real.pi) : ℂ) *
      ⟪v, rowSynth (normProjObsRow W) (summable_normProjObsRow hK hW) y⟫_ℂ = 0
    rw [← projObsDual_eq hK hW, hy, inner_zero_right, mul_zero]
  let β : ℂ := (((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪c, I_y⟫_ℂ)
  have hIβ : I_y = β • c := by
    simp only [cutProj, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply, smul_smul] at hproj
    exact sub_eq_zero.mp hproj
  refine ⟨-(Complex.I / (Real.sqrt 2 : ℂ)) * β, ?_⟩
  change W (2 * Real.pi) (((-(Complex.I / (Real.sqrt 2 : ℂ)) * β) • basisVec 0) +
    (-(Complex.I / (Real.sqrt 2 : ℂ))) • I_y) = _
  rw [hIβ, smul_smul, ← smul_add, show basisVec 0 + c =
    ContinuousLinearMap.adjoint (W (2 * Real.pi)) (basisVec 0) by simp only [c, cutC]; abel,
    map_smul, ← ContinuousLinearMap.mul_apply,
    transport_mul_adjoint hK hW ⟨Real.two_pi_pos.le, le_rfl⟩, ContinuousLinearMap.one_apply]

private theorem roughVekuaDrivenVector_positive_coord (p : BoundaryL2) (m α : ℂ) (n : ℕ) (θ : ℝ) :
    (roughVekuaDrivenVector γ E W p m α θ : ℕ → ℂ) (n + 1) =
      (roughVekuaRegularCorrection γ E W p m α θ : ℕ → ℂ) (n + 1) := by
  simp only [roughVekuaDrivenVector, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    basisVec_coord, Nat.succ_ne_zero, if_false, smul_eq_mul, mul_zero, zero_add]

private theorem roughVekuaRegularCorrection_derivative_eq_transportCoeff
    (p : BoundaryL2) (m α : ℂ) (θ : ℝ) :
    transportCoeff γ E θ (roughVekuaRegularCorrection γ E W p m α θ) +
      (-(Complex.I / (Real.sqrt 2 : ℂ))) • roughVekuaRegularForce γ E p m θ =
    transportCoeff γ E θ (roughVekuaDrivenVector γ E W p m α θ) +
      (-(Complex.I / (Real.sqrt 2 : ℂ)) * m) • basisVec 0 := by
  simp only [roughVekuaRegularForce, roughVekuaDrivenVector, map_add, map_smul,
    smul_add, smul_smul, smul_eq_mul]
  abel

include hK hγ hW in
private theorem roughVekuaDrivenScaledRow_succ_ae_hasDerivAt (p : BoundaryL2) (m α : ℂ) (n : ℕ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) (n + 1))
        (deriv γ θ * physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) (n + 2) θ +
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) n θ) θ := by
  filter_upwards [roughVekuaRegularCorrection_ae_hasDerivAt hK hγ hW p m α] with θ hθ hmem
  have hd := ((innerSL ℂ (basisVec (n + 1))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ (hθ hmem)
  simp only [ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply] at hd
  rw [roughVekuaRegularCorrection_derivative_eq_transportCoeff] at hd
  have hd_row : HasDerivAt (physicalDrivenRow (roughVekuaDrivenVector γ E W p m α) (n + 1))
      (physicalDrivenQ E * (deriv γ θ * physicalDrivenRow (roughVekuaDrivenVector γ E W p m α) (n + 2) θ +
        conj (deriv γ θ) * physicalDrivenRow (roughVekuaDrivenVector γ E W p m α) n θ)) θ := by
    convert hd using 1
    · funext t
      simp only [Function.comp_apply, physicalDrivenRow, Nat.succ_ne_zero, if_false,
        roughVekuaDrivenVector_positive_coord]
      exact (inner_basisVec _ _).symm
    · simp only [inner_basisVec, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
        smul_eq_mul, basisVec_coord, Nat.succ_ne_zero, if_false, mul_zero, add_zero]
      rw [transportCoeff_apply_coord, shiftN_apply_succ]
      cases n with
      | zero => simp [physicalDrivenRow, physicalDrivenQ, shiftWeight]
      | succ n => simp [physicalDrivenRow, physicalDrivenQ, shiftWeight, Nat.add_assoc]
  convert hd_row.const_mul (physicalDrivenQ E ^ (n + 1)) using 1
  · funext t; rfl
  · simp only [physicalDrivenScaledRow]; ring

/-! ### Factorial gauge regularity & moments -/

private theorem roughVekuaGauge_scaledRow_zero_split (p : BoundaryL2) (m α : ℂ) (θ : ℝ) :
    physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) 0 θ =
      -Complex.I * p θ +
        physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 0 θ := by
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 :=
    by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  simp only [physicalDrivenScaledRow, pow_zero, one_mul, physicalDrivenRow, if_true,
    roughVekuaDrivenVector, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, basisVec_coord, mul_one]
  field_simp [hs0] <;> ring

private theorem roughVekuaGauge_scaledRow_succ_eq (p : BoundaryL2) (m α : ℂ) (n : ℕ) (θ : ℝ) :
    physicalDrivenScaledRow E (roughVekuaDrivenVector γ E W p m α) (n + 1) θ =
      physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) (n + 1) θ := by
  simp [physicalDrivenScaledRow, physicalDrivenRow, roughVekuaDrivenVector_positive_coord]

private theorem roughVekuaGauge_partial_succ_eq (p : BoundaryL2) (m α : ℂ) (j N : ℕ) (θ : ℝ) :
    physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N θ =
      physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) (j + 1) N θ :=
  Finset.sum_congr rfl fun _ _ => by
    simp only [physicalDrivenGaugeTerm, ← Nat.add_assoc, roughVekuaGauge_scaledRow_succ_eq]

private theorem roughVekuaGauge_succ_eq (p : BoundaryL2) (m α : ℂ) (j : ℕ) (θ : ℝ) :
    physicalDrivenGauge γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) θ =
      physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) (j + 1) θ :=
  tsum_congr fun _ => by
    simp only [physicalDrivenGaugeTerm, ← Nat.add_assoc, roughVekuaGauge_scaledRow_succ_eq]

private theorem roughVekuaGauge_zero_split (p : BoundaryL2) (m α : ℂ) (θ : ℝ) :
    physicalDrivenGauge γ E (roughVekuaDrivenVector γ E W p m α) 0 θ =
      -Complex.I * p θ + physicalDrivenGauge γ E
        (roughVekuaRegularCorrection γ E W p m α) 0 θ := by
  rw [physicalDrivenGauge, (summable_norm_physicalDrivenGaugeTerm γ E
      (roughVekuaDrivenVector γ E W p m α) 0 θ).of_norm.tsum_eq_zero_add,
    physicalDrivenGauge, (summable_norm_physicalDrivenGaugeTerm γ E
      (roughVekuaRegularCorrection γ E W p m α) 0 θ).of_norm.tsum_eq_zero_add,
    show (fun l : ℕ => physicalDrivenGaugeTerm γ E (roughVekuaDrivenVector γ E W p m α) 0 (l + 1) θ) =
      fun l => physicalDrivenGaugeTerm γ E (roughVekuaRegularCorrection γ E W p m α) 0 (l + 1) θ from
      funext fun l => by simp only [physicalDrivenGaugeTerm, Nat.add_zero, roughVekuaGauge_scaledRow_succ_eq]]
  simp only [physicalDrivenGaugeTerm, physicalDrivenPower, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul, Nat.zero_add, roughVekuaGauge_scaledRow_zero_split]
  ring

private theorem roughVekuaGauge_partial_zero_split (p : BoundaryL2) (m α : ℂ) (N : ℕ) (θ : ℝ) :
    physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) 0 N θ =
      -Complex.I * p θ + physicalDrivenGaugePartial γ E
        (roughVekuaRegularCorrection γ E W p m α) 0 N θ := by
  induction N with
  | zero =>
    simpa [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower] using
      roughVekuaGauge_scaledRow_zero_split p m α θ
  | succ N ih =>
    simp only [physicalDrivenGaugePartial, Finset.sum_range_succ] at ih ⊢
    rw [ih]; simp only [physicalDrivenGaugeTerm, Nat.add_zero, roughVekuaGauge_scaledRow_succ_eq]; ring

include hK hγ hW in
private theorem roughVekuaGauge_regular_memLp (p : BoundaryL2) (m α : ℂ) (j : ℕ) :
    MemLp (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) j) 2 μB :=
  continuousOn_memLp_boundary (physicalDrivenGauge_continuousOn γ hγ.continuous E _
    (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α) j)

include hK hγ hW in
private theorem roughVekuaGauge_zero_memLp (p : BoundaryL2) (m α : ℂ) :
    MemLp (physicalDrivenGauge γ E (roughVekuaDrivenVector γ E W p m α) 0) 2 μB :=
  MemLp.ae_eq (Eventually.of_forall fun θ => (roughVekuaGauge_zero_split p m α θ).symm)
    (((Lp.memLp p).const_smul (-Complex.I)).add (roughVekuaGauge_regular_memLp hK hγ hW p m α 0))

include hK hγ hW in
private theorem roughGauge_regular_partial_ac (p : BoundaryL2) (m α : ℂ) (j N : ℕ) :
    AbsolutelyContinuousOnInterval
      (physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) j N)
      0 (2 * Real.pi) := by
  have hrow (n : ℕ) : AbsolutelyContinuousOnInterval
      (physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) n) 0 (2 * Real.pi) := by
    have hc := absolutelyContinuousOnInterval_clm_comp (innerSL ℂ (basisVec n))
      (roughVekuaRegularCorrection_absolutelyContinuous hK hγ hW p m α)
    by_cases hn : n = 0
    · subst n; convert hc.const_smul (Real.sqrt 2 : ℂ) using 1 <;> ext θ <;>
        simp [physicalDrivenScaledRow, physicalDrivenRow, inner_basisVec]
    · convert hc.const_smul (physicalDrivenQ E ^ n) using 1 <;> ext θ <;>
        simp [physicalDrivenScaledRow, physicalDrivenRow, hn, inner_basisVec]
  have ht (l : ℕ) : AbsolutelyContinuousOnInterval
      (physicalDrivenGaugeTerm γ E (roughVekuaRegularCorrection γ E W p m α) j l) 0 (2 * Real.pi) := by
    have hp : ContDiff ℝ 1 (physicalDrivenPower γ l) :=
      ((hγ.sub contDiff_const).neg.pow l).div_const _
    unfold physicalDrivenGaugeTerm
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def] using
      (c1_absolutelyContinuousOnInterval hp).smul (hrow (l + j))
  induction N with
  | zero =>
    rw [show physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) j 0 =
      physicalDrivenGaugeTerm γ E (roughVekuaRegularCorrection γ E W p m α) j 0 from
        funext fun _ => Finset.sum_range_one _]
    exact ht 0
  | succ N ih =>
    rw [show physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) j (N + 1) =
      fun θ => physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) j N θ +
        physicalDrivenGaugeTerm γ E (roughVekuaRegularCorrection γ E W p m α) j (N + 1) θ from
          funext fun _ => Finset.sum_range_succ _ _]
    exact ih.add (ht (N + 1))

include hK hγ hW in
private theorem roughVekuaGauge_partial_succ_ae_hasDerivAt (p : BoundaryL2) (m α : ℂ) (j N : ℕ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt
        (physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N)
        (physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
          physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) j N θ +
          deriv γ θ * physicalDrivenPower γ N θ * physicalDrivenScaledRow E
            (roughVekuaDrivenVector γ E W p m α) (N + j + 2) θ) θ := by
  induction N with
  | zero =>
    filter_upwards [roughVekuaDrivenScaledRow_succ_ae_hasDerivAt hK hγ hW p m α j] with θ hθ hmem
    convert hθ hmem using 1
    · funext s
      simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower,
        physicalDrivenScaledRow, physicalDrivenRow, Finset.sum_range_succ, Finset.range_zero,
        Nat.add_assoc, add_comm]
    · simp [physicalDrivenGaugePartial, physicalDrivenGaugeTerm, physicalDrivenPower,
        physicalDrivenScaledRow, physicalDrivenRow]; ring
  | succ N ih =>
    filter_upwards [ih, roughVekuaDrivenScaledRow_succ_ae_hasDerivAt hK hγ hW p m α (N + j + 1)]
      with θ hθ hd hmem
    have he (k : ℕ) : physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) k (N + 1) =
        fun s => physicalDrivenGaugePartial γ E (roughVekuaDrivenVector γ E W p m α) k N s +
          physicalDrivenGaugeTerm γ E (roughVekuaDrivenVector γ E W p m α) k (N + 1) s :=
      funext fun _ => Finset.sum_range_succ _ _
    rw [he]
    convert (hθ hmem).add ((physicalDrivenPower_hasDerivAt_succ hγ N θ).mul (hd hmem)) using 1
    · funext s; simp only [physicalDrivenGaugeTerm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Pi.add_apply, Pi.mul_apply]
    · rw [he]; simp only [physicalDrivenGaugeTerm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]; ring

include hK hγ hW in
private theorem roughVekuaGauge_momentPartial_recurrence (p : BoundaryL2) (m α : ℂ)
    (hα : roughVekuaRegularCorrection γ E W p m α (2 * Real.pi) = α • basisVec 0)
    (j N k : ℕ) :
    physicalDrivenQ E ^ 2 * physicalDrivenMomentPartial γ E
      (roughVekuaDrivenVector γ E W p m α) j N k +
      (k : ℂ) * physicalDrivenMomentPartial γ E
        (roughVekuaDrivenVector γ E W p m α) (j + 1) N (k - 1) =
      -physicalDrivenTailMoment γ E (roughVekuaDrivenVector γ E W p m α) j N k := by
  let f := roughVekuaDrivenVector γ E W p m α
  let v := roughVekuaRegularCorrection γ E W p m α
  let z : ℝ → ℂ := fun θ => conj (physicalDrivenCentered γ θ)
  let s := physicalDrivenGaugePartial γ E f (j + 1) N
  let a : ℝ → ℂ := fun θ => conj (deriv γ θ) * physicalDrivenGaugePartial γ E f j N θ * z θ ^ k
  let b : ℝ → ℂ := fun θ => conj (deriv γ θ) * s θ * z θ ^ (k - 1)
  let t : ℝ → ℂ := fun θ => deriv γ θ * physicalDrivenPower γ N θ *
    physicalDrivenScaledRow E f (N + j + 2) θ * z θ ^ k
  let r : ℝ → ℂ := fun θ => physicalDrivenQ E ^ 2 * a θ + (k : ℂ) * b θ + t θ
  have hz1 : ContDiff ℝ 1 z := Complex.conjCLE.contDiff.comp (hγ.sub contDiff_const)
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  have hpart_mem (q : ℕ) : MemLp (physicalDrivenGaugePartial γ E f q N) 2 μB := by
    have hc := continuousOn_memLp_boundary (physicalDrivenGaugePartial_continuousOn γ hγ.continuous E v hv q N)
    cases q with
    | zero => exact MemLp.ae_eq (Eventually.of_forall fun θ =>
        (roughVekuaGauge_partial_zero_split p m α N θ).symm) (((Lp.memLp p).const_smul (-Complex.I)).add hc)
    | succ q => exact MemLp.ae_eq (Eventually.of_forall fun θ =>
        (roughVekuaGauge_partial_succ_eq p m α q N θ).symm) hc
  have hs_ac : AbsolutelyContinuousOnInterval s 0 (2 * Real.pi) := by
    dsimp only [s, f]
    rw [funext (roughVekuaGauge_partial_succ_eq p m α j N)]
    exact roughGauge_regular_partial_ac hK hγ hW p m α (j + 1) N
  have hsz' : AbsolutelyContinuousOnInterval (fun θ => s θ * z θ ^ k) 0 (2 * Real.pi) := by
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def] using hs_ac.smul (c1_absolutelyContinuousOnInterval (hz1.pow k))
  have ha : MemLp a 2 μB := by
    have hw : Continuous (fun θ => conj (deriv γ θ) * z θ ^ k) :=
      (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul (hz1.continuous.pow k)
    simpa only [a, mul_assoc, mul_left_comm, mul_comm] using
      continuous_mul_memLp_boundary hw (hpart_mem j)
  have hb : MemLp b 2 μB := by
    have hw : Continuous (fun θ => conj (deriv γ θ) * z θ ^ (k - 1)) :=
      (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul (hz1.continuous.pow (k - 1))
    simpa only [b, s, mul_assoc, mul_left_comm, mul_comm] using
      continuous_mul_memLp_boundary hw (hpart_mem (j + 1))
  have ht : MemLp t 2 μB := by
    have hp : Continuous (physicalDrivenPower γ N) :=
      ((hγ.continuous.sub continuous_const).neg.pow N).div_const _
    have ht_eq : t = fun θ => deriv γ θ * physicalDrivenPower γ N θ *
        physicalDrivenScaledRow E v (N + j + 2) θ * z θ ^ k :=
      funext fun θ => congrArg (fun q => deriv γ θ * physicalDrivenPower γ N θ * q * z θ ^ k)
        (roughVekuaGauge_scaledRow_succ_eq p m α (N + j + 1) θ)
    rw [ht_eq]
    exact continuousOn_memLp_boundary (((hγ.continuous_deriv_one.mul hp).continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn v hv (N + j + 2)))).mul
      (hz1.continuous.pow k).continuousOn)
  have hr : MemLp r 2 μB := by
    simpa only [r, smul_eq_mul, Pi.add_def, Pi.smul_def] using
      ((ha.const_smul (physicalDrivenQ E ^ 2)).add (hb.const_smul (k : ℂ))).add ht
  have hd : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) → HasDerivAt (fun θ => s θ * z θ ^ k) (r θ) θ := by
    filter_upwards [roughVekuaGauge_partial_succ_ae_hasDerivAt hK hγ hW p m α j N] with θ hθ hmem
    have hdz : HasDerivAt z (conj (deriv γ θ)) θ := by
      simpa only [z, physicalDrivenCentered, Complex.star_def] using
        ((hγ.differentiable_one θ).hasDerivAt.sub_const (γ 0)).star
    convert (hθ hmem).mul (hdz.pow k) using 1
    dsimp only [r, a, b, t, s, f]; simp only [Pi.pow_apply]; ring
  have hri : IntegrableOn r (Icc 0 (2 * Real.pi)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]; exact hr.integrable (by norm_num)
  have he := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
    hsz' hri hd (2 * Real.pi) ⟨Real.two_pi_pos.le, le_rfl⟩
  have hs0 : s 0 = 0 := Finset.sum_eq_zero fun l _ => by
    simp [f, physicalDrivenGaugeTerm, show l + (j + 1) = (l + j) + 1 by omega,
      physicalDrivenScaledRow, physicalDrivenRow, roughVekuaDrivenVector_positive_coord,
      roughVekuaRegularCorrection_zero hW, basisVec_coord]
  have hsT : s (2 * Real.pi) = 0 := Finset.sum_eq_zero fun l _ => by
    simp [f, physicalDrivenGaugeTerm, show l + (j + 1) = (l + j) + 1 by omega,
      physicalDrivenScaledRow, physicalDrivenRow, roughVekuaDrivenVector_positive_coord,
      hα, basisVec_coord]
  simp only [hs0, hsT, zero_mul, zero_add] at he
  have hia := intervalIntegrable_boundary_of_memLp a ha
  have hib := intervalIntegrable_boundary_of_memLp b hb
  have hit := intervalIntegrable_boundary_of_memLp t ht
  dsimp only [r] at he
  rw [intervalIntegral.integral_add ((hia.const_mul _).add (hib.const_mul _)) hit,
    intervalIntegral.integral_add (hia.const_mul _) (hib.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  exact eq_neg_of_add_eq_zero_left he.symm

include hK hγ hW in
private theorem roughVekuaGauge_momentPartial_tendsto (p : BoundaryL2) (m α : ℂ) (j k : ℕ) :
    Tendsto (fun N : ℕ => physicalDrivenMomentPartial γ E
      (roughVekuaDrivenVector γ E W p m α) j N k) atTop
      (𝓝 (physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) j k)) := by
  let v := roughVekuaRegularCorrection γ E W p m α
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  cases j with
  | succ j =>
    have he (N : ℕ) : physicalDrivenMomentPartial γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) N k =
        physicalDrivenMomentPartial γ E v (j + 1) N k :=
      intervalIntegral.integral_congr fun θ _ => by
        dsimp only [physicalDrivenMomentPartial, v]; rw [roughVekuaGauge_partial_succ_eq]
    have he' : physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) (j + 1) k =
        physicalDrivenMoment γ E v (j + 1) k :=
      intervalIntegral.integral_congr fun θ _ => by
        dsimp only [physicalDrivenMoment, v]; rw [roughVekuaGauge_succ_eq]
    simpa only [he, he'] using physicalDrivenMomentPartial_tendsto γ hγ E v hv (j + 1) k
  | zero =>
    let w : ℝ → ℂ := fun θ => conj (deriv γ θ) * conj (physicalDrivenCentered γ θ) ^ k
    let c : ℂ := ∫ θ in (0 : ℝ)..(2 * Real.pi), w θ * (-Complex.I * p θ)
    have hw : Continuous w := (Complex.continuous_conj.comp hγ.continuous_deriv_one).mul
      ((Complex.continuous_conj.comp (hγ.continuous.sub continuous_const)).pow k)
    have hbase : MemLp (fun θ : ℝ => w θ * (-Complex.I * p θ)) 2 μB := by
      simpa only [Pi.smul_def, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
        (continuous_mul_memLp_boundary hw (Lp.memLp p)).const_smul (-Complex.I)
    have hi := intervalIntegrable_boundary_of_memLp _ hbase
    have hsplit (g : ℝ → ℂ) (hg : MemLp g 2 μB) :
        (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * (-Complex.I * p θ + g θ) *
          conj (physicalDrivenCentered γ θ) ^ k) =
        c + ∫ θ in (0 : ℝ)..(2 * Real.pi), conj (deriv γ θ) * g θ *
          conj (physicalDrivenCentered γ θ) ^ k := by
      have ht := intervalIntegrable_boundary_of_memLp _ (continuous_mul_memLp_boundary hw hg)
      calc _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), w θ * (-Complex.I * p θ) + w θ * g θ :=
              intervalIntegral.integral_congr fun θ _ => by dsimp only [w]; ring
        _ = c + _ := by
              rw [intervalIntegral.integral_add hi ht]
              exact congrArg (c + ·) (intervalIntegral.integral_congr fun θ _ => by dsimp only [w]; ring)
    have he (N : ℕ) : physicalDrivenMomentPartial γ E (roughVekuaDrivenVector γ E W p m α) 0 N k =
        c + physicalDrivenMomentPartial γ E v 0 N k := by
      refine (intervalIntegral.integral_congr fun θ _ => ?_).trans (hsplit _
        (continuousOn_memLp_boundary (physicalDrivenGaugePartial_continuousOn γ hγ.continuous E v hv 0 N)))
      dsimp only [physicalDrivenMomentPartial, v]; rw [roughVekuaGauge_partial_zero_split]
    have he' : physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) 0 k =
        c + physicalDrivenMoment γ E v 0 k := by
      refine (intervalIntegral.integral_congr fun θ _ => ?_).trans
        (hsplit _ (roughVekuaGauge_regular_memLp hK hγ hW p m α 0))
      dsimp only [physicalDrivenMoment, v]; rw [roughVekuaGauge_zero_split]
    simpa only [he, he'] using (physicalDrivenMomentPartial_tendsto γ hγ E v hv 0 k).const_add c

include hK hγ hW in
private theorem roughVekuaGauge_physicalMoment_eq_zero (hE : 0 < E) (p : BoundaryL2) (m α : ℂ)
    (hα : roughVekuaRegularCorrection γ E W p m α (2 * Real.pi) = α • basisVec 0)
    (j k : ℕ) :
    physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) j k = 0 := by
  have hrec (q r : ℕ) :
      physicalDrivenQ E ^ 2 * physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) q r +
        (r : ℂ) * physicalDrivenMoment γ E (roughVekuaDrivenVector γ E W p m α) (q + 1) (r - 1) = 0 := by
    have hl := ((roughVekuaGauge_momentPartial_tendsto hK hγ hW p m α q r).const_mul
      (physicalDrivenQ E ^ 2)).add
      ((roughVekuaGauge_momentPartial_tendsto hK hγ hW p m α (q + 1) (r - 1)).const_mul (r : ℂ))
    have htail : Tendsto (fun N : ℕ => physicalDrivenTailMoment γ E
        (roughVekuaDrivenVector γ E W p m α) q N r) atTop (𝓝 0) := by
      have he (N : ℕ) : physicalDrivenTailMoment γ E (roughVekuaDrivenVector γ E W p m α) q N r =
          physicalDrivenTailMoment γ E (roughVekuaRegularCorrection γ E W p m α) q N r :=
        intervalIntegral.integral_congr fun θ _ => by
          rw [roughVekuaGauge_scaledRow_succ_eq p m α (N + q + 1) θ]
      simpa only [he] using physicalDrivenTailMoment_tendsto_zero γ hγ E _
        (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α) q r
    exact tendsto_nhds_unique hl (by
      simpa only [roughVekuaGauge_momentPartial_recurrence hK hγ hW p m α hα, neg_zero] using htail.neg)
  induction k generalizing j with
  | zero =>
    have h := hrec j 0
    simp only [Nat.cast_zero, zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (physicalDrivenQ_sq_ne_zero hE)
  | succ k ih =>
    have h := hrec j (k + 1)
    rw [Nat.add_sub_cancel, ih (j + 1), mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (physicalDrivenQ_sq_ne_zero hE)

include hK hγ hW in
private theorem roughGauge_regular_zero_ae_hasDerivAt (p : BoundaryL2) (m α : ℂ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 0)
        (2 * deriv γ θ * physicalDrivenScaledRow E
          (roughVekuaRegularCorrection γ E W p m α) 1 θ - Complex.I * m) θ := by
  filter_upwards [roughVekuaRegularCorrection_ae_hasDerivAt hK hγ hW p m α] with θ hθ hmem
  have hd := (((innerSL ℂ (basisVec 0)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ
    (hθ hmem)).const_mul (Real.sqrt 2 : ℂ)
  change HasDerivAt (fun t : ℝ => (Real.sqrt 2 : ℂ) * inner ℂ (basisVec 0)
      (roughVekuaRegularCorrection γ E W p m α t))
    ((Real.sqrt 2 : ℂ) * inner ℂ (basisVec 0)
      (transportCoeff γ E θ (roughVekuaRegularCorrection γ E W p m α θ) +
        (-(Complex.I / (Real.sqrt 2 : ℂ))) • roughVekuaRegularForce γ E p m θ)) θ at hd
  rw [roughVekuaRegularCorrection_derivative_eq_transportCoeff] at hd
  simp only [inner_basisVec] at hd
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [show physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 0 =
    fun t : ℝ => (Real.sqrt 2 : ℂ) * (roughVekuaRegularCorrection γ E W p m α t : ℕ → ℂ) 0 from
      funext fun _ => by simp [physicalDrivenScaledRow, physicalDrivenRow]]
  refine hd.congr_deriv ?_
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    basisVec_coord, if_true, mul_one]
  rw [transportCoeff_apply_coord, shiftN_apply_zero, roughVekuaDrivenVector_positive_coord]
  simp only [physicalDrivenScaledRow, physicalDrivenRow, pow_one, physicalDrivenQ,
    Nat.one_ne_zero, if_false, shiftWeight, if_true, mul_zero, add_zero]
  rw [mul_add, show (Real.sqrt 2 : ℂ) * (-(Complex.I / (Real.sqrt 2 : ℂ)) * m) = -Complex.I * m by
    field_simp [hs0]]
  have hcoup (a b c : ℂ) :
      (Real.sqrt 2 : ℂ) * (a * (b * ((Real.sqrt 2 : ℂ) * c))) = 2 * b * (a * c) := by
    calc _ = (Real.sqrt 2 : ℂ) ^ 2 * (b * (a * c)) := by ring
      _ = _ := by rw [hs]; ring
  rw [hcoup]; ring

include hK hγ hW in
private theorem roughGauge_regular_positive_ae_hasDerivAt (p : BoundaryL2) (m α : ℂ) (n : ℕ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt
        (physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) (n + 1))
        (deriv γ θ * physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) (n + 2) θ +
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            ((if n = 0 then -Complex.I * p θ else 0) +
              physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) n θ)) θ := by
  filter_upwards [roughVekuaDrivenScaledRow_succ_ae_hasDerivAt hK hγ hW p m α n] with θ hθ hmem
  rw [funext (roughVekuaGauge_scaledRow_succ_eq p m α n)] at hθ
  convert hθ hmem using 1
  cases n with
  | zero => rw [roughVekuaGauge_scaledRow_succ_eq, roughVekuaGauge_scaledRow_zero_split]; rfl
  | succ n => simp [roughVekuaGauge_scaledRow_succ_eq]

private def roughVekuaGaugeRegularDerivative (γ : ℝ → ℂ) (E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2) (p : BoundaryL2) (m α : ℂ) (θ : ℝ) : ℂ :=
  physicalDrivenGaugeZeroContinuousPart γ E (roughVekuaRegularCorrection γ E W p m α) θ -
    Complex.I * m - Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
      physicalDrivenPower γ 1 θ * p θ

include hγ in
private theorem roughGauge_sub_memLp {c : ℝ → ℂ}
    (hc : ContinuousOn c (Icc 0 (2 * Real.pi))) (p : BoundaryL2) (m : ℂ) :
    MemLp (fun s => c s - Complex.I * m -
      Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) * physicalDrivenPower γ 1 s * p s) 2 μB :=
  ((continuousOn_memLp_boundary hc).sub (memLp_const (Complex.I * m))).sub
    (continuous_mul_memLp_boundary
      ((continuous_const.mul (Complex.continuous_conj.comp hγ.continuous_deriv_one)).mul
        (((hγ.continuous.sub continuous_const).neg.pow 1).div_const _))
      (Lp.memLp p))

include hK hγ hW in
private theorem roughVekuaGauge_regular_derivative_memLp (p : BoundaryL2) (m α : ℂ) :
    MemLp (roughVekuaGaugeRegularDerivative γ E W p m α) 2 μB :=
  roughGauge_sub_memLp hγ (physicalDrivenGaugeZeroContinuousPart_continuousOn hγ E _
    (roughVekuaRegularCorrection_continuousOn hK hγ hW p m α)) p m

include hK hγ hW in
private theorem roughGauge_regular_partial_zero_ae_hasDerivAt
    (p : BoundaryL2) (m α : ℂ) (N : ℕ) :
    ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt
        (physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) 0 (N + 1))
        (deriv γ θ * physicalDrivenScaledRow E (roughVekuaRegularCorrection γ E W p m α) 1 θ -
          Complex.I * m + deriv γ θ * physicalDrivenGaugeTerm γ E
            (roughVekuaRegularCorrection γ E W p m α) 1 (N + 1) θ +
          physicalDrivenQ E ^ 2 * conj (deriv γ θ) *
            ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E
              (roughVekuaRegularCorrection γ E W p m α) l θ -
          Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ θ) * physicalDrivenPower γ 1 θ * p θ) θ := by
  induction N with
  | zero =>
    filter_upwards [roughGauge_regular_zero_ae_hasDerivAt hK hγ hW p m α,
      roughGauge_regular_positive_ae_hasDerivAt hK hγ hW p m α 0] with θ h0 h1 hmem
    convert (h0 hmem).add ((physicalDrivenPower_hasDerivAt_succ hγ 0 θ).mul (h1 hmem)) using 1
    · funext s
      norm_num [physicalDrivenGaugePartial, Finset.sum_range_succ, physicalDrivenGaugeTerm,
        physicalDrivenShiftedGaugeTerm, physicalDrivenPower, physicalDrivenScaledRow,
        physicalDrivenRow, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
      simp [physicalDrivenGaugeTerm, physicalDrivenShiftedGaugeTerm, physicalDrivenPower,
        physicalDrivenScaledRow, physicalDrivenRow, Nat.factorial]; ring
  | succ N ih =>
    filter_upwards [ih, roughGauge_regular_positive_ae_hasDerivAt hK hγ hW p m α (N + 1)]
      with θ hθ hd hmem
    rw [show N + 1 + 1 = N + 2 from rfl,
      show physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) 0 (N + 2) =
        fun t => physicalDrivenGaugePartial γ E (roughVekuaRegularCorrection γ E W p m α) 0 (N + 1) t +
          physicalDrivenGaugeTerm γ E (roughVekuaRegularCorrection γ E W p m α) 0 (N + 2) t from
            funext fun _ => Finset.sum_range_succ _ _]
    convert (hθ hmem).add ((physicalDrivenPower_hasDerivAt_succ hγ (N + 1) θ).mul (hd hmem)) using 1
    · funext t; simp only [Pi.add_apply, Pi.mul_apply, physicalDrivenGaugeTerm]
    · rw [show N + 2 = (N + 1) + 1 from rfl, Finset.sum_range_succ]
      simp only [physicalDrivenGaugeTerm, physicalDrivenShiftedGaugeTerm, Nat.succ_ne_zero,
        if_false, zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        physicalDrivenPower, physicalDrivenCentered, physicalDrivenScaledRow, physicalDrivenRow]
      rw [show N + 2 = (N + 1) + 1 from rfl, Nat.factorial_succ]
      have hf : ((N + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N + 1)
      field_simp [hf]; ring

include hK hγ hW in
private theorem roughVekuaGauge_regular_primitive (p : BoundaryL2) (m α : ℂ)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0 θ =
      (Real.sqrt 2 : ℂ) * α +
        ∫ s in (0 : ℝ)..θ, roughVekuaGaugeRegularDerivative γ E W p m α s := by
  classical
  let v := roughVekuaRegularCorrection γ E W p m α
  let a : ℝ → ℂ := fun s => deriv γ s * physicalDrivenScaledRow E v 1 s - Complex.I * m -
    Complex.I * physicalDrivenQ E ^ 2 * conj (deriv γ s) * physicalDrivenPower γ 1 s * p s
  let b : ℝ → ℂ := fun s => conj (deriv γ s) * physicalDrivenShiftedGauge γ E v s
  have hv := roughVekuaRegularCorrection_continuousOn hK hγ hW p m α
  have ha : MemLp a 2 μB := roughGauge_sub_memLp hγ
    (hγ.continuous_deriv_one.continuousOn.mul
      (continuousOn_const.mul (physicalDrivenRow_continuousOn _ hv 1))) p m
  have hsub : uIcc 0 θ ⊆ Icc 0 (2 * Real.pi) := by
    rw [uIcc_of_le hθ.1]; exact Icc_subset_Icc le_rfl hθ.2
  have hai : IntervalIntegrable a volume 0 θ := by
    have hI : IntegrableOn a (Icc 0 (2 * Real.pi)) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]; exact ha.integrable (by norm_num)
    exact (hI.mono_set hsub).intervalIntegrable
  have hpart (N : ℕ) :
      physicalDrivenGaugePartial γ E v 0 (N + 1) θ =
        (Real.sqrt 2 : ℂ) * α + (∫ s in (0 : ℝ)..θ, a s) +
        (∫ s in (0 : ℝ)..θ, deriv γ s * physicalDrivenGaugeTerm γ E v 1 (N + 1) s) +
        physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
          ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E v l s) := by
    let t : ℝ → ℂ := fun s => deriv γ s * physicalDrivenGaugeTerm γ E v 1 (N + 1) s
    let bN : ℝ → ℂ := fun s => conj (deriv γ s) *
      ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E v l s
    have ht : ContinuousOn t (Icc 0 (2 * Real.pi)) :=
      hγ.continuous_deriv_one.continuousOn.mul
        (physicalDrivenGaugeTerm_continuousOn γ hγ.continuous E v hv 1 (N + 1))
    have hbN : ContinuousOn bN (Icc 0 (2 * Real.pi)) :=
      (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
        (continuousOn_finset_sum _ fun l _ =>
          physicalDrivenShiftedGaugeTerm_continuousOn γ hγ.continuous E v hv l)
    have hr : MemLp (fun s => a s + t s + physicalDrivenQ E ^ 2 * bN s) 2 μB := by
      simpa only [smul_eq_mul, Pi.add_def, Pi.smul_def] using
        (ha.add (continuousOn_memLp_boundary ht)).add
          ((continuousOn_memLp_boundary hbN).const_smul (physicalDrivenQ E ^ 2))
    have hd : ∀ᵐ s, s ∈ Ioo 0 (2 * Real.pi) →
        HasDerivAt (physicalDrivenGaugePartial γ E v 0 (N + 1))
          (a s + t s + physicalDrivenQ E ^ 2 * bN s) s := by
      filter_upwards [roughGauge_regular_partial_zero_ae_hasDerivAt hK hγ hW p m α N] with s hs hmem
      convert hs hmem using 1; dsimp only [a, t, bN, v]; ring
    have hri : IntegrableOn (fun s => a s + t s + physicalDrivenQ E ^ 2 * bN s)
        (Icc 0 (2 * Real.pi)) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]; exact hr.integrable (by norm_num)
    have he := eq_add_intervalIntegral_of_ac_ae_hasDerivAt Real.two_pi_pos.le
      (roughGauge_regular_partial_ac hK hγ hW p m α 0 (N + 1)) hri hd θ hθ
    have h0 : physicalDrivenGaugePartial γ E v 0 (N + 1) 0 = (Real.sqrt 2 : ℂ) * α := by
      have hv0 := roughVekuaRegularCorrection_zero hW p m α
      rw [physicalDrivenGaugePartial, Finset.sum_eq_single 0]
      · simp [v, physicalDrivenGaugeTerm, physicalDrivenPower, physicalDrivenScaledRow,
          physicalDrivenRow, hv0, basisVec_coord]
      · intro l _ hl; simp [v, physicalDrivenGaugeTerm, physicalDrivenScaledRow,
          physicalDrivenRow, hv0, basisVec_coord, hl]
      · simp
    rw [h0, intervalIntegral.integral_add (hai.add (ht.mono hsub).intervalIntegrable)
      (((hbN.mono hsub).intervalIntegrable).const_mul _),
      intervalIntegral.integral_add hai (ht.mono hsub).intervalIntegrable,
      intervalIntegral.integral_const_mul] at he
    simpa only [a, t, bN, v, add_assoc] using he
  have hp : Tendsto (fun N : ℕ => physicalDrivenGaugePartial γ E v 0 (N + 1) θ) atTop
      (𝓝 (physicalDrivenGauge γ E v 0 θ)) := by
    simpa [physicalDrivenGaugePartial, physicalDrivenGauge, Function.comp_def] using
      ((summable_norm_physicalDrivenGaugeTerm γ E v 0 θ).of_norm.hasSum.tendsto_sum_nat).comp
        (tendsto_add_atTop_nat 2)
  have ht := ((physicalDrivenGauge_weightedIntegral_hasSum_to γ hγ.continuous E v hv 1
    (deriv γ) hγ.continuous_deriv_one.continuousOn hθ).summable.tendsto_atTop_zero).comp
      (tendsto_add_atTop_nat 1)
  have hs := physicalDrivenShiftedGauge_weightedIntegral_hasSum_to γ hγ.continuous E v hv
    (fun s => conj (deriv γ s))
    (Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn hθ
  have hb : Tendsto (fun N : ℕ => ∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
      ∑ l ∈ Finset.range (N + 1), physicalDrivenShiftedGaugeTerm γ E v l s) atTop
      (𝓝 (∫ s in (0 : ℝ)..θ, b s)) := by
    refine (hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr' (Eventually.of_forall fun N => ?_)
    simp_rw [Finset.mul_sum]
    exact (intervalIntegral.integral_finset_sum fun l _ =>
      (((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
        (physicalDrivenShiftedGaugeTerm_continuousOn γ hγ.continuous E v hv l)).mono
          hsub).intervalIntegrable).symm
  have hlim : physicalDrivenGauge γ E v 0 θ =
      (Real.sqrt 2 : ℂ) * α + (∫ s in (0 : ℝ)..θ, a s) +
        physicalDrivenQ E ^ 2 * (∫ s in (0 : ℝ)..θ, b s) :=
    tendsto_nhds_unique hp ((by
      simpa only [add_zero, Function.comp_apply] using
        ((tendsto_const_nhds (x := (Real.sqrt 2 : ℂ) * α + ∫ s in (0 : ℝ)..θ, a s)).add ht).add
          (hb.const_mul (physicalDrivenQ E ^ 2)) : Tendsto _ atTop _).congr'
      (Eventually.of_forall fun N => (hpart N).symm))
  have hbi : IntervalIntegrable b volume 0 θ :=
    (((Complex.continuous_conj.comp hγ.continuous_deriv_one).continuousOn.mul
      (physicalDrivenShiftedGauge_continuousOn γ hγ.continuous E v hv)).mono hsub).intervalIntegrable
  rw [hlim, ← intervalIntegral.integral_const_mul, add_assoc,
    ← intervalIntegral.integral_add hai (hbi.const_mul _)]
  exact congrArg _ (intervalIntegral.integral_congr fun s _ => by
    dsimp only [a, b, roughVekuaGaugeRegularDerivative, physicalDrivenGaugeZeroContinuousPart, v]; ring)

include hK hγ hW in
private theorem roughVekuaGauge_regular_isSobolevSeq_one (p : BoundaryL2) (m α : ℂ)
    (hα : roughVekuaRegularCorrection γ E W p m α (2 * Real.pi) = α • basisVec 0) :
    IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos
      (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0)) := by
  have hi := intervalIntegrable_boundary_of_memLp _
    (roughVekuaGauge_regular_derivative_memLp hK hγ hW p m α)
  have hac_prim := ((LipschitzWith.const ((Real.sqrt 2 : ℂ) * α)).lipschitzOnWith.absolutelyContinuousOnInterval).add
    (absolutelyContinuousOnInterval_intervalIntegral_banach hi
      (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩))
  have hac : AbsolutelyContinuousOnInterval
      (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0) 0 (2 * Real.pi) := by
    unfold AbsolutelyContinuousOnInterval at hac_prim ⊢
    refine hac_prim.congr' ?_
    unfold Filter.EventuallyEq; rw [eventually_inf_principal]
    exact Eventually.of_forall fun B hB => Finset.sum_congr rfl fun i hi' => by
      have hx := (hB.1 i hi').1; have hy := (hB.1 i hi').2
      rw [uIcc_of_le Real.two_pi_pos.le] at hx hy
      rw [roughVekuaGauge_regular_primitive hK hγ hW p m α hx,
        roughVekuaGauge_regular_primitive hK hγ hW p m α hy]; rfl
  have hderiv : ∀ᵐ θ, θ ∈ Ioo 0 (2 * Real.pi) →
      HasDerivAt (physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0)
        (roughVekuaGaugeRegularDerivative γ E W p m α θ) θ := by
    filter_upwards [ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le hi] with θ hθ hmem
    refine ((hθ hmem).const_add ((Real.sqrt 2 : ℂ) * α)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with t ht
    exact roughVekuaGauge_regular_primitive hK hγ hW p m α (Ioo_subset_Icc_self ht)
  have hend {θ : ℝ} (hv : roughVekuaRegularCorrection γ E W p m α θ = α • basisVec 0) :
      physicalDrivenGauge γ E (roughVekuaRegularCorrection γ E W p m α) 0 θ =
        (Real.sqrt 2 : ℂ) * α := by
    rw [physicalDrivenGauge, (summable_norm_physicalDrivenGaugeTerm γ E
      (roughVekuaRegularCorrection γ E W p m α) 0 θ).of_norm.tsum_eq_zero_add,
      show (fun l : ℕ => physicalDrivenGaugeTerm γ E
        (roughVekuaRegularCorrection γ E W p m α) 0 (l + 1) θ) = fun _ => (0 : ℂ) from
          funext fun _ => by simp [physicalDrivenGaugeTerm, physicalDrivenScaledRow,
            physicalDrivenRow, hv, basisVec_coord], tsum_zero, add_zero]
    simp [physicalDrivenGaugeTerm, physicalDrivenPower, physicalDrivenScaledRow,
      physicalDrivenRow, hv, basisVec_coord]
  exact isSobolevSeq_one_fourierCoeffOn_of_ac_ae_hasDerivAt hac
    (roughVekuaGauge_regular_derivative_memLp hK hγ hW p m α) hderiv
    ((hend (roughVekuaRegularCorrection_zero hW p m α)).trans (hend hα).symm)

end RoughTransport

/-! ### Hardy support from L² physical moments -/

private theorem localConformal_physicalMoments_nonpositive_of_memLp_of_smoothInverse
    {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target) (H : ℝ → ℂ)
    (hH : MemLp H 2 μB)
    (hmom : ∀ m : ℕ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (conj (deriv (physicalCircleTrace F) θ) * H θ) *
        (conj (physicalCircleTrace F θ) - conj (physicalCircleTrace F 0)) ^ m) = 0) :
    IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H) := by
  have hinj : InjOn F (closedBall (0 : ℂ) 1) := by rw [← he]; exact e.injOn.mono hsource
  have hnz : ∀ z ∈ closedBall (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0 := fun z hz hzero => by
    have hzs := hsource hz
    have hzt : F z ∈ e.target := by rw [← he]; exact e.mapsTo hzs
    have hdF := ((hFs.contDiffAt (isOpen_ball.mem_nhds
      (closedBall_subset_ball hR hz))).differentiableAt (by simp)).hasFDerivAt
    have hdG := ((hes.contDiffAt (e.open_target.mem_nhds hzt)).differentiableAt (by simp)).hasFDerivAt
    have hid : HasFDerivAt (fun x : ℂ => x) ((fderiv ℝ e.symm (F z)).comp (fderiv ℝ F z)) z := by
      refine (hdG.comp z hdF).congr_of_eventuallyEq ?_
      filter_upwards [e.open_source.mem_nhds hzs] with x hx
      rw [← he]; exact (e.left_inv hx).symm
    have hval := congrArg (fun A : ℂ →L[ℝ] ℂ => A 1) (hid.unique (hasFDerivAt_id z))
    change fderiv ℝ e.symm (F z) (fderiv ℝ F z 1) = (1 : ℂ) at hval
    rw [hzero, map_zero] at hval; exact zero_ne_one hval
  exact localConformal_physicalMoments_nonpositive_of_memLp hb hL hR F hFs hhol hinj hnz rfl H hH hmom

/-! ### Fixed-complement projected-observation injectivity -/

private def halfRegularCoordinateLoad (y : L2Z)
    (hy : IsSobolevSeq (1 / 2 : ℝ) (y : ℤ → ℂ)) : BoundaryL2 :=
  boundaryFourier.symm (sobVec (1 / 2 : ℝ) (y : ℤ → ℂ) hy)

private theorem roughNormalizedPrimitive_pos_one_of_raw_hardy_split
    (y : L2Z) (H K : ℝ → ℂ) (hH2 : MemLp H 2 μB) (hK2 : MemLp K 2 μB)
    (hH : IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H))
    (hK1 : IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos K))
    (hsplit : H =ᵐ[μB] fun θ => -Complex.I * roughNormalizedPrimitive y θ + K θ) :
    IsSobolevSeq 1 (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ) := by
  let p : L2Z := posProj (boundaryFourier (roughNormalizedPrimitive y))
  let k : L2Z := posProj (boundaryFourier (hK2.toLp K))
  have hzero : posProj (boundaryFourier (hH2.toLp H)) = 0 := lp.ext <| funext fun n => by
    by_cases hn : 0 < n
    · simp only [posProj, diagOp_apply, if_pos hn, boundaryFourier_apply,
        fourierCoeffOn_congr_ae Real.two_pi_pos hH2.coeFn_toLp, hH n hn, mul_zero,
        lp.coeFn_zero, Pi.zero_apply]
    · simp only [posProj, diagOp_apply, if_neg hn, zero_mul, lp.coeFn_zero, Pi.zero_apply]
  have hLp : hH2.toLp H = -Complex.I • roughNormalizedPrimitive y + hK2.toLp K := Lp.ext <| by
    filter_upwards [hH2.coeFn_toLp, hK2.coeFn_toLp, hsplit,
      Lp.coeFn_add (-Complex.I • roughNormalizedPrimitive y) (hK2.toLp K),
      Lp.coeFn_smul (-Complex.I) (roughNormalizedPrimitive y)] with θ hh hk hs ha hm
    simpa only [hh, hk, ha, hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hs
  have hs := congrArg (fun B : BoundaryL2 => posProj (boundaryFourier B)) hLp
  change posProj (boundaryFourier (hH2.toLp H)) =
    posProj (boundaryFourier (-Complex.I • roughNormalizedPrimitive y + hK2.toLp K)) at hs
  rw [hzero, map_add, map_smul, map_add, map_smul] at hs
  have hi := congrArg (fun B : L2Z => Complex.I • B) hs
  simp only [smul_zero, smul_add, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul] at hi
  have hp : p = -Complex.I • k := by
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hi.symm
  have hKB : IsSobolevSeq 1 (boundaryFourier (hK2.toLp K) : ℤ → ℂ) := by
    rw [show (boundaryFourier (hK2.toLp K) : ℤ → ℂ) =
      (Real.sqrt (2 * Real.pi) : ℂ) • fourierCoeffOn Real.two_pi_pos K from
      funext fun n => by rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hK2.coeFn_toLp]; rfl]
    exact isSobolevSeq_smul _ hK1
  change p ∈ fourierSobolevSubmodule 1
  rw [hp]
  exact (fourierSobolevSubmodule 1).smul_mem _ (isSobolevSeq_posProj hKB)

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (Metric.ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' Metric.ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' Metric.ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1))
    (hinj : InjOn F (Metric.ball (0 : ℂ) 1))
    (hC : ∀ z ∈ Metric.ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : Metric.closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

local notation "ΓF" => physicalCircleTrace F
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NF" => normalizedConormal hβF haF hgF

include hR hFs hb hL hhol hinj hC hK e he hsource hes in
private theorem half_regular_kernel_mem_conormal_range
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (y : L2Z) (hy : IsSobolevSeq (1 / 2 : ℝ) (y : ℤ → ℂ))
    (hobs : projObsDual W y = 0) :
    ∃ b : L2Z, IsNonpositiveFourierSupport b ∧ NF (E : ℂ) b = y := by
  let g := halfRegularCoordinateLoad y hy
  have hgnorm : sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier g) = y := by
    dsimp only [g, halfRegularCoordinateLoad]
    rw [boundaryFourier.apply_symm_apply]
    exact lp.ext <| funext fun n => congrFun (fromL2_sobVec (1 / 2 : ℝ) (y : ℤ → ℂ) hy) n
  have hproj : cutProj (cutC (W (2 * Real.pi)) (basisVec 0)) (observationAdj W (g : ℝ → ℂ)) = 0 := by
    have h := projObsDual_boundary_normalized hΓLip hW g
    rw [map_smul, hgnorm, hobs, smul_zero] at h
    exact h.symm
  let c : Ell2 := cutC (W (2 * Real.pi)) (basisVec 0)
  let α : ℂ := (((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ * ⟪c, observationAdj W (g : ℝ → ℂ)⟫_ℂ)
  let t : ℂ := -Complex.I * α
  let r : BoundaryL2 := localConformalRadialCoordinateLoad F hΓLip E 1
  have hspan : observationAdj W (g : ℝ → ℂ) = α • c := by
    simp only [cutProj, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply, smul_smul] at hproj
    exact sub_eq_zero.mp hproj
  have hrad : observationAdj W (r : ℝ → ℂ) = Complex.I • c := by
    simpa only [r, c, mul_one] using localConformalRadialCoordinateLoad_observationAdj F hΓLip hW (1 : ℂ)
  let g₀ : BoundaryL2 := g - t • r
  have hO : observationAdj W (g₀ : ℝ → ℂ) = 0 := by
    have hgI := integrable_boundary_observation_load hΓLip hW g
    have hrI := integrable_boundary_observation_load hΓLip hW r
    have hsub : observationAdj W (g₀ : ℝ → ℂ) =
        observationAdj W (g : ℝ → ℂ) - t • observationAdj W (r : ℝ → ℂ) := by
      rw [observationAdj, observationAdj, observationAdj,
        intervalIntegral.integral_of_le Real.two_pi_pos.le,
        intervalIntegral.integral_of_le Real.two_pi_pos.le,
        intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_smul]
      refine (integral_congr_ae ?_).trans (integral_sub hgI (hrI.smul t))
      filter_upwards [Lp.coeFn_sub g (t • r), Lp.coeFn_smul t r] with θ hs ht
      simp only [g₀, hs, ht, Pi.sub_apply, Pi.smul_apply, sub_smul, smul_smul, smul_eq_mul]
    rw [hsub, hspan, hrad, smul_smul,
      show t * Complex.I = α by dsimp [t]; linear_combination (-α) * Complex.I_sq, sub_self]
  have hΓF := contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  let b₀ : L2Z := physicalDrivenKernelInput hΓLip hΓF hW (g₀ : ℝ → ℂ) (Lp.memLp g₀) hO
  have hb₀ : IsNonpositiveFourierSupport b₀ :=
    physicalDrivenKernelInput_nonpositive hR F hFs hb hL hhol hC e he hsource hΓLip hE hW
      (g₀ : ℝ → ℂ) (Lp.memLp g₀) hO
  have hNC₀ : NF (E : ℂ) b₀ = sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier g₀) := by
    simpa only [b₀, Lp.toLp_coeFn] using
      physicalDrivenKernelH1_normalizedConormal_eq_coordinateLoad hR F hFs hb hL
        hhol hinj hC hK e he hsource hes hΓLip hE hW (g₀ : ℝ → ℂ) (Lp.memLp g₀) hO
  have hNCr : NF (E : ℂ) radialVekuaInput =
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier r) := by
    simpa only [one_smul, r] using
      localConformalRadial_normalizedConormal_eq_coordinateLoad hR F hFs hb hL hhol hinj
        hC hK e he hsource hes hΓLip hE (1 : ℂ)
  refine ⟨b₀ + t • radialVekuaInput, fun n hn => by
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
      hb₀ n hn, radialVekuaInput_nonpositive n hn, smul_zero, add_zero], ?_⟩
  rw [map_add, map_smul, hNC₀, hNCr]
  dsimp only [g₀]
  rw [map_sub, map_smul, map_sub, map_smul, hgnorm]
  abel

include hR hFs hb hL hhol hinj hC hK e he hsource hes in
theorem exists_localConformal_fixed_fourier_complement_projectedObservation_injective
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E₀ : ℝ} (hE₀ : 0 < E₀)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E₀ W)
    (hcut : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → L2Z),
      Function.Injective ((projObsDual W).comp (finiteFourierChart u v)) ∧
      ∃ U ∈ 𝓝 E₀,
        ∀ E ∈ U, IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
          (finiteFourierChart u v) ∘L H₀ᗮ.orthogonalProjection) := by
  have hJ : Continuous fun E : ℝ => (NF (E : ℂ)).comp (H₀).subtypeL :=
    ((continuous_normalizedConormal hβF haF hgF).comp Complex.continuous_ofReal).clm_comp continuous_const
  have hcpt : IsCompactOperator ((NF (E₀ : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
      Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection - (1 : L2Z →L[ℂ] L2Z)) := by
    rw [show (NF (E₀ : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
        Submodule.subtypeL H₀ᗮ ∘L H₀ᗮ.orthogonalProjection - (1 : L2Z →L[ℂ] L2Z) =
        (NF (E₀ : ℂ) - (1 : L2Z →L[ℂ] L2Z)) ∘L ((H₀).subtypeL ∘L (H₀).orthogonalProjection) from
      ContinuousLinearMap.ext fun x => by
        have hx := (H₀).starProjection_add_starProjection_orthogonal x
        rw [Submodule.starProjection_apply, Submodule.starProjection_apply] at hx
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, Submodule.subtypeL_apply]
        rw [← sub_eq_zero, show (H₀ᗮ.orthogonalProjection x : L2Z) =
          x - ((H₀).orthogonalProjection x : L2Z) by rw [eq_sub_iff_add_eq, add_comm]; exact hx]
        abel]
    exact (isCompactOperator_normalizedConormal_sub_one hβF haF hgF E₀).comp_clm _
  have hinj0 : Function.Injective ((NF (E₀ : ℂ)).comp (H₀).subtypeL) := fun b d hbd =>
    Subtype.ext <| (localConformalVekuaConormal_injective_on_nonpositive_of_cutC_ne_zero
      hR F hFs hb hL hhol hinj hC hK e he hsource hes E₀ hE₀.le hW hcut) b.property d.property hbd
  obtain ⟨d, u, v, _, hv0, U, hU, hunit, _⟩ :=
    exists_fixed_complement_basis H₀ hJ hcpt hinj0 stdBasisZ positiveFourierHilbertBasis
  have hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite :=
    fun r => finite_support_of_mem_span_stdBasisZ (hv0 r)
  refine ⟨d, u, v, ?_, U, hU, hunit⟩
  intro z₁ z₂ heq
  set z := z₁ - z₂
  have hobs : projObsDual W (finiteFourierChart u v z) = 0 := by
    change (projObsDual W).comp (finiteFourierChart u v) z = 0
    rw [map_sub, heq, sub_self]
  have hΓ : ContDiff ℝ 1 ΓF :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
  let y := finiteFourierChart u v z
  let m : ℂ := y 0 / (Real.sqrt (2 * Real.pi) : ℂ)
  obtain ⟨α, hαT⟩ := roughVekuaRegularCorrection_exists_periodic_of_projObsDual_eq_zero
    hΓLip hΓ hW y hobs
  have hH2 := roughVekuaGauge_zero_memLp hΓLip hΓ hW (roughNormalizedPrimitive y) m α
  have hHn : IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos
      (physicalDrivenGauge ΓF E₀ (roughVekuaDrivenVector ΓF E₀ W (roughNormalizedPrimitive y) m α) 0)) := by
    refine localConformal_physicalMoments_nonpositive_of_memLp_of_smoothInverse
      hR F hFs hb hL hhol e he hsource hes _ hH2 fun k => ?_
    simpa only [physicalDrivenMoment, physicalDrivenCentered, map_sub, mul_assoc] using
      roughVekuaGauge_physicalMoment_eq_zero hΓLip hΓ hW hE₀ (roughNormalizedPrimitive y) m α hαT 0 k
  have hy_half : IsSobolevSeq (1 / 2 : ℝ) (y : ℤ → ℂ) :=
    finiteFourierChart_half_of_rough_primitive_pos_one u v hv z
      (roughNormalizedPrimitive_pos_one_of_raw_hardy_split y _ _ hH2
        (roughVekuaGauge_regular_memLp hΓLip hΓ hW (roughNormalizedPrimitive y) m α 0)
        hHn
        (roughVekuaGauge_regular_isSobolevSeq_one hΓLip hΓ hW (roughNormalizedPrimitive y) m α hαT)
        (Eventually.of_forall (roughVekuaGauge_zero_split (roughNormalizedPrimitive y) m α)))
  obtain ⟨b, hbn, hb'⟩ := half_regular_kernel_mem_conormal_range hR F hFs hb hL
    hhol hinj hC hK e he hsource hes hΓLip hE₀ hW y hy_half hobs
  obtain ⟨u₀, hu₀⟩ := hunit E₀ (mem_of_mem_nhds hU)
  have hchart_inj : Function.Injective ((NF (E₀ : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
      finiteFourierChart u v ∘L H₀ᗮ.orthogonalProjection) := by
    erw [← hu₀]
    exact fun x₁ x₂ hx => by
      simpa only [← ContinuousLinearMap.mul_apply, Units.inv_mul, ContinuousLinearMap.one_apply] using
        congrArg (fun x : L2Z => (↑u₀⁻¹ : L2Z →L[ℂ] L2Z) x) hx
  exact sub_eq_zero.mp ((chart_range_inter_eq_zero H₀ ((NF (E₀ : ℂ)).comp (H₀).subtypeL)
    (finiteFourierChart u v) hchart_inj ⟨b, hbn⟩ z hb'.symm).1)

end PhysicalCoordinates

end PolyaNeumann

end
