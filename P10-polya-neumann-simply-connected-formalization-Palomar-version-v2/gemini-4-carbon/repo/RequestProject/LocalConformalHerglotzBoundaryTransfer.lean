module

public import RequestProject.LocalConformalRoughChartInjectivity
public import RequestProject.LocalConformalVekuaTransport
public import RequestProject.LocalConformalHardySubspace
public import RequestProject.LocalConformalRadialVekua
public import RequestProject.LocalConformalVekuaConormalBridge
public import RequestProject.CorrectedKernelSymm
public import RequestProject.CorrectedKernelEnergy
public import RequestProject.ConormalNormalization
public import RequestProject.SobolevMultiplier
public import RequestProject.NeumannNormalizedBoundary
public import RequestProject.NeumannTraceInjective
public import RequestProject.NeumannResonanceDimension
public import RequestProject.NeumannConstantTrace
public import RequestProject.NeumannHerglotzBoundary
public import RequestProject.HerglotzReduction
public import RequestProject.ObservationLp
public import RequestProject.PhysicalHardySupport
public import RequestProject.KernelFourierAction
public import RequestProject.Reconstruction
public import RequestProject.TraceReparam
public import RequestProject.FiniteFourierChartRemainder
public import RequestProject.FiniteRankCompletion
public import RequestProject.ReducedForm
public import RequestProject.HerglotzForm
public import RequestProject.PeriodicForm
public import RequestProject.Reparam
public import RequestProject.PhysicalHardyWeights
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Filter Metric Real ContinuousLinearMap InnerProductSpace
open scoped Real Topology InnerProductSpace ComplexConjugate

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
local notation "H₀" => nonpositiveFourierSubspace
local notation "H₁" => nonpositiveFourierSubspaceᗮ

def originalNeumannMultiplicity (Ω : Set ℂ) (E : ℝ) : ℕ :=
  {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard.toNat

/-! ### Part 1: Periodic Fourier derivative, boundary transport & Volterra helpers -/

private theorem eq_add_integral_of_L2_periodic_fourier_derivative
    {v : ℝ → ℂ} (hv : Continuous v)
    (hvper : Function.Periodic v (2 * Real.pi)) (d : BoundaryL2)
    (hcoeff : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos (d : ℝ → ℂ) n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos v n)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    v θ = v 0 + ∫ s in (0 : ℝ)..θ, d s := by
  let P : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, d s
  have hPi := intervalIntegrable_boundaryL2 d
  have hPAC : AbsolutelyContinuousOnInterval P 0 (2 * Real.pi) :=
    absolutelyContinuousOnInterval_intervalIntegral_banach hPi
      (by rw [uIcc_of_le Real.two_pi_pos.le]; exact ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hPC : ContinuousOn P (Icc 0 (2 * Real.pi)) := by
    simpa only [uIcc_of_le Real.two_pi_pos.le] using hPAC.continuousOn
  have hPD : ∀ᵐ t, t ∈ Ioo 0 (2 * Real.pi) → HasDerivAt P (d t) t :=
    ae_hasDerivAt_intervalIntegral_banach Real.two_pi_pos.le hPi
  have hP0 : P 0 = 0 := by simp [P]
  have hPT : P (2 * Real.pi) = 0 := integral_eq_zero_of_periodic_fourier_derivative hcoeff
  have hncoeff (n : ℤ) (hn : n ≠ 0) :
      fourierCoeffOn Real.two_pi_pos v n = fourierCoeffOn Real.two_pi_pos P n :=
    mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn))
      ((hcoeff n).symm.trans (fourierCoeffOn_of_ac_ae_hasDerivAt hPAC (Lp.memLp d) hPD (hP0.trans hPT.symm) n))
  let f : ℝ → ℂ := fun t => v t - P t
  have hfc : ContinuousOn f (Icc 0 (2 * Real.pi)) := hv.continuousOn.sub hPC
  have hfe : f 0 = f (2 * Real.pi) := by
    dsimp only [f]; rw [hP0, hPT, sub_zero, sub_zero]; simpa only [zero_add] using (hvper 0).symm
  let F : ℝ → ℂ := fun t => AddCircle.liftIco (2 * Real.pi) 0 f (t : AddCircle (2 * Real.pi))
  have hFc : Continuous F := (AddCircle.liftIco_zero_continuous hfe hfc).comp (AddCircle.continuous_mk' _)
  have hFp : Function.Periodic F (2 * Real.pi) := fun t => by dsimp only [F]; rw [AddCircle.coe_add_period]
  have hFf : EqOn F f (Icc 0 (2 * Real.pi)) := fun t ht => by
    by_cases htT : t = 2 * Real.pi
    · subst t; dsimp only [F]
      have hzero : AddCircle.liftIco (2 * Real.pi) 0 f (0 : AddCircle (2 * Real.pi)) = f 0 :=
        AddCircle.liftIco_zero_coe_apply ⟨le_rfl, Real.two_pi_pos⟩
      rw [AddCircle.coe_period, hzero, hfe]
    · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, lt_of_le_of_ne ht.2 htT⟩
  have hconst := eq_at_zero_of_periodic_nonzero_fourier_eq_zero hFc hFp
    (fun n hn => by
      rw [fourierCoeffOn_congr_Icc hFf n, fourierCoeffOn_sub_of_continuousOn hv.continuousOn hPC n,
        hncoeff n hn, sub_self]) θ
  rw [hFf hθ, hFf ⟨le_rfl, Real.two_pi_pos.le⟩] at hconst
  change v θ - P θ = v 0 - P 0 at hconst
  rw [hP0, sub_zero] at hconst
  simpa only [add_comm] using sub_eq_iff_eq_add.mp hconst

private theorem isSobolevSeq_one_fromL2_half_of_half_regular (b : L2Z)
    (hb : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) :
    IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) :=
  hb.congr fun n => by
    rw [fromL2, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (sobWeight_pos n) (-(1 / 2 : ℝ))),
      ← mul_assoc, ← Real.rpow_add (sobWeight_pos n),
      show (1 : ℝ) + -(1 / 2 : ℝ) = 1 / 2 by ring]

private theorem normalizedConormal_preserves_half_regular
    {β a g : ℤ → ℂ} (hβ : IsWL1 (1 / 2 : ℝ) β)
    (ha : IsWL1 (1 / 2 : ℝ) a) (hg : IsWL1 (1 / 2 : ℝ) g)
    (E : ℂ) (b : L2Z) (hb : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) :
    IsSobolevSeq (1 / 2 : ℝ) (normalizedConormal hβ ha hg E b : ℤ → ℂ) := by
  have he := congrArg (fun A : L2Z →L[ℂ] L2Z => A b) (normalizedConormal_sub_one_eq hβ ha hg E)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply] at he
  have hr : IsSobolevSeq (1 / 2 : ℝ)
      (sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβ ha hg E b - b) : ℤ → ℂ) :=
    (sobNormSq_mono (by norm_num : (1 / 2 : ℝ) ≤ 1) (isSobolevSeq_fromL2 1 _)).1
  rw [show normalizedConormal hβ ha hg E b =
    b + sobolevSmoothing 1 zero_le_one (conormalRemOp (by norm_num) hβ ha hg E b - b) by rw [← he]; abel]
  simpa only [lp.coeFn_add] using isSobolevSeq_add hb hr

private theorem driven_eq_transport_add_physicalDrivenVector_boundaryL2
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ)
    (hγ : ContDiff ℝ 1 γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (g : BoundaryL2) {y : ℝ → Ell2} (hy : ContinuousOn y (Icc 0 (2 * Real.pi)))
    (hyint : ∀ θ ∈ Icc 0 (2 * Real.pi),
      y θ = y 0 + ∫ s in (0 : ℝ)..θ, transportCoeff γ E s (y s) +
        (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    y θ = W θ (y 0) + physicalDrivenVector W (g : ℝ → ℂ) θ := by
  let Y := physicalDrivenVector W (g : ℝ → ℂ)
  let f : ℝ → Ell2 := fun s => (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0
  have hg := intervalIntegrable_boundaryL2 g
  have hY := physicalDrivenVector_continuousOn_of_intervalIntegrable hW.1 (g : ℝ → ℂ) hg
  have hC : Continuous (transportCoeff γ E) := by
    have hd := hγ.continuous_deriv_one; have hc := Complex.continuous_conj.comp hd
    unfold transportCoeff; fun_prop
  have hfi : IntegrableOn f (Icc 0 (2 * Real.pi)) := by
    have hgi : IntegrableOn (g : ℝ → ℂ) (Icc 0 (2 * Real.pi)) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hg
    exact (hgi.const_mul _).smul_const _
  have hyi : IntegrableOn (fun s => transportCoeff γ E s (y s) + f s) (Icc 0 (2 * Real.pi)) :=
    ((hC.continuousOn.clm_apply hy).integrableOn_Icc).add hfi
  have hYi : IntegrableOn (fun s => transportCoeff γ E s (Y s) + f s) (Icc 0 (2 * Real.pi)) :=
    ((hC.continuousOn.clm_apply hY).integrableOn_Icc).add hfi
  have hdiff (t : ℝ) (ht : t ∈ Icc 0 (2 * Real.pi)) :
      (y t - Y t) = (y 0 - Y 0) + ∫ s in (0 : ℝ)..t, transportCoeff γ E s (y s - Y s) + (0 : Ell2) := by
    have hsub : uIoc 0 t ⊆ Icc 0 (2 * Real.pi) := by
      rw [uIoc_of_le ht.1]; exact fun _ hs' => ⟨hs'.1.le, hs'.2.trans ht.2⟩
    dsimp only [Y]
    rw [hyint t ht, physicalDrivenVector_integral_eq_of_intervalIntegrable hγLip hγ hW (g : ℝ → ℂ) hg ht]
    simp only [physicalDrivenVector_zero, sub_zero]
    rw [show (fun s => transportCoeff γ E s (y s - Y s) + (0 : Ell2)) =
      fun s => (transportCoeff γ E s (y s) + f s) - (transportCoeff γ E s (Y s) + f s) by
        funext s; rw [map_sub]; abel,
      intervalIntegral.integral_sub (intervalIntegrable_iff.mpr (hyi.mono_set hsub))
        (intervalIntegrable_iff.mpr (hYi.mono_set hsub))]
    abel
  have hd := driven_eq_transport hγLip hW
    (continuous_const.aestronglyMeasurable : AEStronglyMeasurable (fun _ : ℝ => (0 : Ell2)) volume)
    (B := 0) (fun _ => by simp) (hy.sub hY) hdiff θ hθ
  have heq : y θ - Y θ = W θ (y 0) := by
    simpa only [Y, physicalDrivenVector_zero, sub_zero, map_zero, Pi.sub_apply,
      intervalIntegral.integral_zero, add_zero] using hd
  simpa only [Y, add_comm] using sub_eq_iff_eq_add.mp heq

private theorem volterraOp_add_adj_boundaryL2
    {γ : ℝ → ℂ} {L : NNReal} (hγLip : LipschitzWith L γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (g : BoundaryL2)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    volterraOp W (g : ℝ → ℂ) θ + volterraOpAdj W (g : ℝ → ℂ) θ =
      observation W (observationAdj W (g : ℝ → ℂ)) θ := by
  have hk (s : ℝ) : conj (volterraKernel W s θ) = volterraKernel W θ s := by
    simp only [volterraKernel]
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]
  have hkc : ContinuousOn (fun s => volterraKernel W θ s) (Icc 0 (2 * Real.pi)) :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0))
  have hint : IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume 0 (2 * Real.pi) :=
    (intervalIntegrable_boundaryL2 g).continuousOn_mul (by simpa only [uIcc_of_le Real.two_pi_pos.le] using hkc)
  have hi0 : IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume 0 θ :=
    hint.mono_set' (by simp only [uIoc_of_le hθ.1, uIoc_of_le Real.two_pi_pos.le]; exact Ioc_subset_Ioc le_rfl hθ.2)
  have hi1 : IntervalIntegrable (fun s => volterraKernel W θ s * g s) volume θ (2 * Real.pi) :=
    hint.mono_set' (by simp only [uIoc_of_le hθ.2, uIoc_of_le Real.two_pi_pos.le]; exact Ioc_subset_Ioc hθ.1 le_rfl)
  simp only [volterraOp, volterraOpAdj, hk]
  rw [intervalIntegral.integral_add_adjacent_intervals hi0 hi1, observation, observationAdj]
  have hi : IntervalIntegrable (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) volume 0 (2 * Real.pi) :=
    intervalIntegrable_iff.mpr (by simpa only [IntegrableOn, uIoc_of_le Real.two_pi_pos.le] using
      integrable_boundary_observation_load hγLip hW g)
  have h := ((innerSL ℂ (basisVec 0)).comp (W θ)).intervalIntegral_comp_comm hi
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at h
  rw [← h]
  exact intervalIntegral.integral_congr fun _ _ => by simp only [map_smul, inner_smul_right, volterraKernel]; ring

private theorem stdBasis_isSobolevSeq_half (n : ℤ) : IsSobolevSeq (1 / 2 : ℝ) (stdBasisZ n : ℤ → ℂ) :=
  summable_of_ne_finset_zero (s := {n}) fun k hk => by
    simp [stdBasisZ_apply, lp.single_apply, Finset.notMem_singleton.mp hk]

private theorem clm_eq_zero_of_nonpositive_stdBasis {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (T : L2Z →L[ℂ] Y) (hstd : ∀ n : ℤ, ¬ 0 < n → T (stdBasisZ n) = 0)
    (b : L2Z) (hbn : IsNonpositiveFourierSupport b) : T b = 0 := by
  have hop : T.comp (1 - posProj) = 0 := by
    apply ContinuousLinearMap.ext_on ((Submodule.dense_iff_topologicalClosure_eq_top).2 stdBasisZ.dense_span)
    rintro _ ⟨n, rfl⟩
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
    rw [show (1 - posProj) (stdBasisZ n) = if 0 < n then 0 else stdBasisZ n from lp.ext <| funext fun k => by
      by_cases hn : 0 < n <;> by_cases hkn : k = n <;>
        simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, posProj, diagOp_apply,
          stdBasisZ_apply, lp.single_apply, hn, hkn]]
    split_ifs with hn
    · exact map_zero T
    · exact hstd n hn
  have hkeep : (1 - posProj) b = b := lp.ext <| funext fun n => by
    by_cases hn : 0 < n <;>
      simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, posProj, diagOp_apply, hn, hbn n]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, hkeep] using
    congrArg (fun A : L2Z →L[ℂ] Y => A b) hop

/-! ### Part 2: Normalized periodic regular & boundary operator families -/

private theorem isCompactOperator_normalizedInverseAbsOperator_sub_one :
    IsCompactOperator (normalizedInverseAbsOperator - (1 : L2Z →L[ℂ] L2Z)) := by
  have hfac : normalizedInverseAbsOperator - (1 : L2Z →L[ℂ] L2Z) =
      (sobolevSmoothing 1 zero_le_one).comp normalizedInverseAbsOperator - zeroModeProjection := by
    apply ContinuousLinearMap.ext; intro b; apply lp.ext; funext n
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.comp_apply, lp.coeFn_sub, Pi.sub_apply,
      normalizedInverseAbsOperator_apply, sobolevSmoothing, diagOp_apply, zeroModeProjection_apply]
    by_cases hn : n = 0
    · subst n; simp [normalizedInverseAbsSymbol]
    · have hw : sobWeight n ≠ 0 := (sobWeight_pos n).ne'
      have habs : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr (Int.cast_ne_zero.mpr hn)
      have hsym : normalizedInverseAbsSymbol n - 1 =
          ((sobWeight n ^ (-(1 : ℝ)) : ℝ) : ℂ) * normalizedInverseAbsSymbol n := by
        simp only [normalizedInverseAbsSymbol, if_neg hn]
        exact_mod_cast (by
          rw [Real.rpow_neg (sobWeight_pos n).le, Real.rpow_one]
          field_simp [hw, habs]; simp only [sobWeight]; ring :
          sobWeight n / |(n : ℝ)| - 1 = sobWeight n ^ (-(1 : ℝ)) * (sobWeight n / |(n : ℝ)|))
      simp only [if_neg hn, zero_mul, sub_zero]
      calc normalizedInverseAbsSymbol n * b n - b n
          = (normalizedInverseAbsSymbol n - 1) * b n := by ring
        _ = _ := by rw [hsym]; ring
  rw [hfac]
  exact ((isCompactOperator_sobolevSmoothing zero_lt_one).comp_clm
    normalizedInverseAbsOperator).sub isCompactOperator_zeroModeProjection

private def correctedRemainderOperator (W : ℝ → Ell2 →L[ℂ] Ell2) (δ s : ℝ) : L2Z →L[ℂ] L2Z := by
  classical
  exact if h : Summable (fun p => ‖correctedRemainderMatrix W δ s p‖ ^ 2) then
    hsMatrixOp (correctedRemainderMatrix W δ s) h else 0

private theorem correctedRemainderOperator_eq (W : ℝ → Ell2 →L[ℂ] Ell2) (δ s : ℝ)
    (h : Summable fun p => ‖correctedRemainderMatrix W δ s p‖ ^ 2) :
    correctedRemainderOperator W δ s = hsMatrixOp (correctedRemainderMatrix W δ s) h := by
  simp only [correctedRemainderOperator, dif_pos h]

private def normalizedPeriodicRegularFamily {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ : ℝ) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2)
    (E : ℝ) : L2Z →L[ℂ] L2Z :=
  (2 : ℂ) • (normalizedNeumannRegular Q E₀ E - normalizedInverseAbsOperator) +
    principalNormalized + correctedRemainderOperator (Ws E) 0 0

private def normalizedPeriodicBoundaryFamily {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2)
    (E : ℝ) : L2Z →L[ℂ] L2Z :=
  (2 : ℂ) • (normalizedNeumannBoundary Q E - normalizedInverseAbsOperator) +
    principalNormalized + correctedRemainderOperator (Ws E) 0 0

private theorem continuousAt_normalizedPeriodicRegularFamily {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) {E₀ : ℝ}
    (hu : IsUnit (h1ComplementForm Ω E₀ E₀))
    {γ : ℝ → ℂ} {K K' : NNReal} {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ Icc 0 (2 * π), ∀ y ∈ Icc 0 (2 * π), ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hWs : ∀ E, IsTransport γ E (Ws E))
    (hc : cutC (Ws E₀ (2 * π)) (basisVec 0) ≠ 0) :
    ContinuousAt (normalizedPeriodicRegularFamily Q E₀ Ws) E₀ := by
  obtain ⟨u, hu_eq⟩ := hu
  have hi : ContinuousAt (fun E => Ring.inverse (h1ComplementForm Ω E₀ E)) E₀ :=
    (hu_eq ▸ NormedRing.inverse_continuousAt u).comp (continuous_h1ComplementForm Ω E₀).continuousAt
  have hres : ContinuousAt (h1RegularResolvent Ω E₀) E₀ :=
    @ContinuousAt.clm_comp ℂ _ (NeumannH1 Ω) _ _ (h1ResonantSpace Ω E₀)ᗮ _
      (h1ComplementNormedSpace Ω E₀) (NeumannH1 Ω) _ _ ℝ _ _ _ E₀ continuousAt_const
      (@ContinuousAt.clm_comp ℂ _ (NeumannH1 Ω) _ _ (h1ResonantSpace Ω E₀)ᗮ _
        (h1ComplementNormedSpace Ω E₀) (h1ResonantSpace Ω E₀)ᗮ _ (h1ComplementNormedSpace Ω E₀)
        ℝ _ _ _ E₀ hi continuousAt_const)
  have hN : ContinuousAt (normalizedNeumannRegular Q E₀) E₀ :=
    continuousAt_const.clm_comp (hres.clm_comp continuousAt_const)
  have href := summable_correctedRemainderMatrix hK hγ' (hWs E₀) hc
    (le_refl 0) (by norm_num) (le_refl 0) (by norm_num)
  obtain ⟨hsum, hlim⟩ := tendsto_correctedRemainder_energy hK hγ' hWs E₀ hc
    (le_refl 0) (by norm_num) (le_refl 0) (by norm_num)
  have hrem : ContinuousAt (fun E => correctedRemainderOperator (Ws E) 0 0) E₀ := by
    rw [ContinuousAt, correctedRemainderOperator_eq _ _ _ href]
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    filter_upwards [hsum, hlim ε hε] with E hE hnorm
    rw [correctedRemainderOperator_eq _ _ _ hE, dist_eq_norm]
    exact hnorm hE
  exact (((hN.sub continuousAt_const).const_smul (2 : ℂ)).add continuousAt_const).add hrem

private theorem periodic_projected_trace_gram
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (S : Submodule ℂ H) [CompleteSpace S] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ S) (Q : H →L[ℂ] G) (c : ℝ) (hc : 0 ≤ c) :
    (c : ℂ) • (Q ∘L S.starProjection ∘L adjoint Q) =
      ∑ i, InnerProductSpace.rankOne ℂ ((Real.sqrt c : ℂ) • Q (b i))
        ((Real.sqrt c : ℂ) • Q (b i)) := by
  classical
  have hs : (Real.sqrt c : ℂ) * (Real.sqrt c : ℂ) = (c : ℂ) := by exact_mod_cast Real.mul_self_sqrt hc
  have hgram : Q ∘L S.starProjection ∘L adjoint Q =
      (Q.comp S.subtypeL).comp (adjoint (Q.comp S.subtypeL)) := by
    simp only [adjoint_comp, Submodule.adjoint_subtypeL, Submodule.starProjection, comp_assoc]
  rw [hgram]
  apply ContinuousLinearMap.ext; intro g
  have hre := b.sum_repr' (adjoint (Q.comp S.subtypeL) g)
  change (c : ℂ) • Q ((adjoint (Q.comp S.subtypeL) g : S) : H) = _
  simp_rw [ContinuousLinearMap.sum_apply, InnerProductSpace.rankOne_apply, inner_smul_left,
    Complex.conj_ofReal, smul_smul]
  rw [← hre]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, adjoint_inner_right,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => congrArg (· • Q (b i)) ?_
  rw [← hs]; ring

private theorem normalizedNeumannResidue_eq_sum_rankOne {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (h1ResonantSpace Ω E₀)) :
    normalizedNeumannResidue Q E₀ = ∑ i,
      InnerProductSpace.rankOne ℂ ((Real.sqrt (E₀ + 1) : ℂ) • Q (b i))
        ((Real.sqrt (E₀ + 1) : ℂ) • Q (b i)) :=
  periodic_projected_trace_gram (h1ResonantSpace Ω E₀) b Q (E₀ + 1) (by linarith)

private theorem h1Resonant_starProjection_eq_zero_of_form_isUnit {Ω : Set ℂ} {E₀ : ℝ}
    (hunit : IsUnit (h1HelmholtzForm Ω E₀)) (u : NeumannH1 Ω) :
    (h1ResonantSpace Ω E₀).starProjection u = 0 :=
  (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).injective <| by
    rw [map_zero]; exact ((h1ResonantSpace Ω E₀).orthogonalProjection u).property

private theorem normalizedNeumannBoundary_eq_regular_at_nonresonant_reference {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1HelmholtzForm Ω E₀)) :
    normalizedNeumannBoundary Q E₀ = normalizedNeumannRegular Q E₀ E₀ :=
  ContinuousLinearMap.ext fun b => by
    have h := normalizedNeumannRegular_eq_trace_of_solution_at_reference Q hb hL hE₀
      b (normalizedNeumannPoisson Q E₀ b) (normalizedNeumannPoisson_isSolution Q hunit b)
    rw [h1Resonant_starProjection_eq_zero_of_form_isUnit hunit, map_zero, sub_zero] at h
    exact h.symm

private theorem normalizedPeriodicBoundaryFamily_isSelfAdjoint {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) {γ : ℝ → ℂ} {K : NNReal}
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E (Ws E))
    (hbase : Summable fun p => ‖correctedRemainderMatrix (Ws E) 0 0 p‖ ^ 2) :
    IsSelfAdjoint (normalizedPeriodicBoundaryFamily Q Ws E) := by
  rw [normalizedPeriodicBoundaryFamily, correctedRemainderOperator_eq _ _ _ hbase]
  have hm := hsMatrixOp_isSelfAdjoint _ hbase fun m n => by
    have hc := correctedKernelCoeff_conj_symm hK hW (-n) m
    simp only [neg_neg] at hc
    simp only [correctedRemainderMatrix, hc, map_mul, Complex.conj_ofReal]
    congr 1; norm_num; ring
  have h1 := normalizedNeumannBoundary_isSelfAdjoint Q E
  have h2 : IsSelfAdjoint normalizedInverseAbsOperator := by
    apply diagOp_isSelfAdjoint; intro n; unfold normalizedInverseAbsSymbol; split_ifs <;> simp
  have h3 : IsSelfAdjoint principalNormalized := by
    apply diagOp_isSelfAdjoint; intro n; unfold principalSymbol
    split_ifs
    · exact map_zero _
    · exact Complex.conj_ofReal _
  simp only [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] at hm h1 h2 h3 ⊢
  rw [map_add, map_add, map_smulₛₗ, map_sub, h1, h2, h3, hm, map_ofNat]

private theorem normalizedPeriodicBoundaryFamily_eq_pole_add_regular {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2)
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀) (hfull : IsUnit (h1HelmholtzForm Ω E))
    (hunit : IsUnit (h1ComplementForm Ω E₀ E)) :
    normalizedPeriodicBoundaryFamily Q Ws E =
      ((-2 / (E - E₀) : ℝ) : ℂ) • normalizedNeumannResidue Q E₀ +
        normalizedPeriodicRegularFamily Q E₀ Ws E := by
  have hpole : normalizedNeumannBoundary Q E =
      (-((E - E₀ : ℝ) : ℂ)⁻¹) • normalizedNeumannResidue Q E₀ +
        normalizedNeumannRegular Q E₀ E := by
    by_cases hne : E ≠ E₀
    · exact normalizedNeumannBoundary_eq_pole_add_regular Q hb hL hE₀ hne hunit
    · obtain rfl : E = E₀ := not_ne_iff.mp hne
      rw [sub_self, Complex.ofReal_zero, inv_zero, neg_zero,
        normalizedNeumannBoundary_eq_regular_at_nonresonant_reference Q hb hL hE₀ hfull]
      ext x; simp
  have hc : (2 : ℂ) * (-((E - E₀ : ℝ) : ℂ)⁻¹) = ((-2 / (E - E₀) : ℝ) : ℂ) := by push_cast; ring
  rw [normalizedPeriodicBoundaryFamily, hpole]
  simp only [normalizedPeriodicRegularFamily, smul_sub, smul_add, smul_smul, hc]
  abel

/-! ### Part 3: Sawtooth & corrected boundary operators on `BoundaryL2` -/

private theorem regular_sawtooth_measurable : Measurable (Function.uncurry sawtoothKernel) := by
  unfold sawtoothKernel Function.uncurry
  exact (measurable_const.mul (Complex.measurable_ofReal.comp
    (measurable_real_sign.comp (measurable_fst.sub measurable_snd)))).sub
    (measurable_const.mul (((Complex.measurable_ofReal.comp measurable_fst).sub
      (Complex.measurable_ofReal.comp measurable_snd)).div_const (π : ℂ)))

private theorem regular_sawtooth_norm_le {θ s : ℝ}
    (hθ : θ ∈ Icc 0 (2 * π)) (hs : s ∈ Icc 0 (2 * π)) :
    ‖sawtoothKernel θ s‖ ≤ 3 := by
  have hd : |θ - s| ≤ 2 * π := abs_le.mpr ⟨by linarith [hθ.1, hs.2], by linarith [hθ.2, hs.1]⟩
  have hdiv : |(θ - s) / π| ≤ 2 := by
    rw [abs_div, abs_of_pos pi_pos]; exact (div_le_iff₀ pi_pos).mpr (by linarith)
  calc ‖sawtoothKernel θ s‖
      ≤ ‖Complex.I * (Real.sign (θ - s) : ℂ)‖ + ‖Complex.I * (((θ - s) / π : ℝ) : ℂ)‖ := by
          simpa only [sawtoothKernel, Complex.ofReal_div, Complex.ofReal_sub] using
            norm_sub_le (Complex.I * (Real.sign (θ - s) : ℂ)) (Complex.I * (((θ - s) / π : ℝ) : ℂ))
    _ = |Real.sign (θ - s)| + |(θ - s) / π| := by
          simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    _ ≤ 3 := by linarith [abs_real_sign_le (θ - s)]

private theorem fourierCoeffOn_sawtoothAction {f : ℝ → ℂ} (hf : Integrable f μB) (n : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => ∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * f s) n =
      (2 / (n : ℂ)) * fourierCoeffOn two_pi_pos f n := by
  let μ : Measure ℝ := μB
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      kernelFourierMode (-n) p.1 * sawtoothKernel p.1 p.2 * f p.2) (μ.prod μ) :=
    (((show Continuous (fun p : ℝ × ℝ => kernelFourierMode (-n) p.1) by
      unfold kernelFourierMode; fun_prop).measurable.aestronglyMeasurable.mul
      regular_sawtooth_measurable.aestronglyMeasurable).mul hf.aestronglyMeasurable.comp_snd)
  have hint : Integrable (fun p : ℝ × ℝ =>
      kernelFourierMode (-n) p.1 * sawtoothKernel p.1 p.2 * f p.2) (μ.prod μ) := by
    refine ((hf.norm.comp_snd μ).const_mul 3).mono' hm ?_
    have hae : ∀ᵐ p ∂μ.prod μ, p ∈ Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π) := by
      dsimp [μ]; rw [Measure.prod_restrict]; exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)
    filter_upwards [hae] with p hp
    have hkn : ‖kernelFourierMode (-n) p.1‖ = 1 := by
      rw [← fourier_two_pi_eq_kernelFourierMode, fourier_apply]; exact Circle.norm_coe _
    simp only [norm_mul, hkn, one_mul]
    exact mul_le_mul_of_nonneg_right
      (regular_sawtooth_norm_le (Ioc_subset_Icc_self hp.1) (Ioc_subset_Icc_self hp.2)) (norm_nonneg _)
  have hmode (θ : ℝ) :
      Complex.exp (2 * π * Complex.I * (-n : ℤ) * θ / ((2 * π : ℝ) : ℂ)) = kernelFourierMode (-n) θ := by
    simpa only [fourier_coe_apply] using fourier_two_pi_eq_kernelFourierMode (-n) θ
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp_rw [fourier_coe_apply]
  simp only [sub_zero, Complex.real_smul, smul_eq_mul]
  simp_rw [hmode]; push_cast; simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  change (1 / (2 * π) : ℂ) * (∫ θ, kernelFourierMode (-n) θ * (∫ s, sawtoothKernel θ s * f s ∂μB) ∂μB) = _
  rw [show (fun θ => kernelFourierMode (-n) θ * (∫ s, sawtoothKernel θ s * f s ∂μB)) =
    fun θ => ∫ s, kernelFourierMode (-n) θ * sawtoothKernel θ s * f s ∂μB from funext fun θ => by
      rw [← integral_const_mul]; congr 1; funext s; ring,
    integral_integral_swap hint]
  have heq : (fun s => ∫ θ, kernelFourierMode (-n) θ * sawtoothKernel θ s * f s ∂μB) =ᵐ[μB]
      fun s => (2 / (n : ℂ)) * (kernelFourierMode (-n) s * f s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [integral_mul_const]
    have hswap : (∫ θ in (0 : ℝ)..(2 * π), kernelFourierMode (-n) θ * sawtoothKernel θ s) =
        (2 / (n : ℂ)) * kernelFourierMode (-n) s := by
      have hs' := Ioc_subset_Icc_self hs
      rw [show (fun θ => kernelFourierMode (-n) θ * sawtoothKernel θ s) =
        fun θ => -(sawtoothKernel s θ * kernelFourierMode (-n) θ) from funext fun θ => by
          have hsg : Real.sign (θ - s) = -Real.sign (s - θ) := by rw [← Real.sign_neg, neg_sub]
          simp only [sawtoothKernel, hsg, Complex.ofReal_neg]; ring,
        intervalIntegral.integral_neg]
      by_cases hn : n = 0
      · subst n; simp [kernelFourierMode, integral_sawtoothKernel hs']
      · rw [show (∫ θ in (0 : ℝ)..(2 * π), sawtoothKernel s θ * kernelFourierMode (-n) θ) =
          2 / ((-n : ℤ) : ℂ) * kernelFourierMode (-n) s from
          integral_sawtoothKernel_mul_exp hs' (neg_ne_zero.mpr hn)]
        simp only [Int.cast_neg, div_neg, neg_mul, neg_neg]
    rw [intervalIntegral.integral_of_le two_pi_pos.le] at hswap
    change (∫ θ, kernelFourierMode (-n) θ * sawtoothKernel θ s ∂μB) * f s = _
    rw [hswap]; ring
  rw [integral_congr_ae heq, integral_const_mul]; ring

private theorem memLp_sawtoothAction {f : ℝ → ℂ} (hf : Integrable f μB) :
    MemLp (fun θ => ∫ s in (0 : ℝ)..(2 * π), sawtoothKernel θ s * f s) 2 μB := by
  have hmeas : AEStronglyMeasurable (fun θ => ∫ s, sawtoothKernel θ s * f s ∂μB) μB :=
    (regular_sawtooth_measurable.aestronglyMeasurable.mul
      hf.aestronglyMeasurable.comp_snd).integral_prod_right'
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  refine MemLp.of_bound hmeas (3 * ∫ s, ‖f s‖ ∂μB) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  refine (norm_integral_le_of_norm_le (hf.norm.const_mul 3) ?_).trans (integral_const_mul _ _).le
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (regular_sawtooth_norm_le (Ioc_subset_Icc_self hθ) (Ioc_subset_Icc_self hs)) (norm_nonneg _)

private def sawtoothBoundaryAction (f : BoundaryL2) : BoundaryL2 :=
  (memLp_sawtoothAction ((Lp.memLp f).integrable (by norm_num))).toLp _

private def regularRawInverseDerivative : L2Z →L[ℂ] L2Z :=
  (sobolevSmoothing (1 / 2) (by norm_num)).comp
    ((principalNormalized - (2 : ℂ) • normalizedInverseAbsOperator).comp
      (sobolevSmoothing (1 / 2) (by norm_num)))

private def sawtoothBoundaryOperator : BoundaryL2 →L[ℂ] BoundaryL2 :=
  boundaryFourier.symm.toLinearIsometry.toContinuousLinearMap.comp
    (regularRawInverseDerivative.comp boundaryFourier.toLinearIsometry.toContinuousLinearMap)

private theorem sawtoothBoundaryOperator_eq_action (f : BoundaryL2) :
    sawtoothBoundaryOperator f = sawtoothBoundaryAction f := by
  apply boundaryFourier.injective; apply lp.ext; funext n
  have hraw : regularRawInverseDerivative (boundaryFourier f) n = (2 / (n : ℂ)) * boundaryFourier f n := by
    simp only [regularRawInverseDerivative, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, lp.coeFn_sub, Pi.sub_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, principalNormalized,
      normalizedInverseAbsOperator_apply, sobolevSmoothing, diagOp_apply]
    by_cases hn : n = 0
    · subst n; simp [principalSymbol, normalizedInverseAbsSymbol]
    · have hw : ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (sobWeight n : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.rpow_add (sobWeight_pos n)]
        norm_num; rw [Real.rpow_neg_one, ← Complex.ofReal_mul,
          inv_mul_cancel₀ (sobWeight_pos n).ne', Complex.ofReal_one]
      have hsym : principalSymbol n - 2 * normalizedInverseAbsSymbol n =
          (sobWeight n : ℂ) * (2 / (n : ℂ)) := by
        simp only [principalSymbol, normalizedInverseAbsSymbol, if_neg hn]; push_cast; ring
      calc _ = (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
              (principalSymbol n - 2 * normalizedInverseAbsSymbol n) * boundaryFourier f n := by ring
        _ = (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              (sobWeight n : ℂ)) * (2 / (n : ℂ)) * boundaryFourier f n := by rw [hsym]; ring
        _ = _ := by rw [hw, one_mul]
  change boundaryFourier (boundaryFourier.symm (regularRawInverseDerivative (boundaryFourier f))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply, hraw, boundaryFourier_apply, boundaryFourier_apply]
  dsimp only [sawtoothBoundaryAction]
  rw [fourierCoeffOn_congr_ae two_pi_pos (MemLp.coeFn_toLp (memLp_sawtoothAction
      ((Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)))),
    fourierCoeffOn_sawtoothAction ((Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2))]
  ring

private def regularCorrectedBoundaryOperator {γ : ℝ → ℂ} {K : NNReal} {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hK : LipschitzWith K γ)
    (hW : IsTransport γ E W) (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) :
    BoundaryL2 →L[ℂ] BoundaryL2 :=
  boundaryCircleUnitary.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((correctedKernelL2Op hK hW hc).comp
      boundaryCircleUnitary.toLinearIsometry.toContinuousLinearMap)

private theorem memLp_regularCorrectedAction {γ : ℝ → ℂ} {K : NNReal} {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hK : LipschitzWith K γ) (hW : IsTransport γ E W)
    {f : ℝ → ℂ} (hf : Integrable f μB) :
    MemLp (fun θ => ∫ s in (0 : ℝ)..(2 * π), correctedKernel W θ s * f s) 2 μB := by
  have hmeas : AEStronglyMeasurable (fun θ => ∫ s, correctedKernel W θ s * f s ∂μB) μB :=
    ((aestronglyMeasurable_correctedKernel hW).mul
      hf.aestronglyMeasurable.comp_snd).integral_prod_right'
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  refine MemLp.of_bound hmeas ((4 + ‖cutBE W‖) * ∫ s, ‖f s‖ ∂μB) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  refine (norm_integral_le_of_norm_le (hf.norm.const_mul (4 + ‖cutBE W‖)) ?_).trans
    (integral_const_mul _ _).le
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_correctedKernel_le hK hW (Ioc_subset_Icc_self hθ) (Ioc_subset_Icc_self hs)) (norm_nonneg _)

private theorem regularCorrectedBoundaryOperator_eq_integral_L2
    {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) (g : BoundaryL2) :
    regularCorrectedBoundaryOperator hγLip hW hc g =
      (memLp_regularCorrectedAction hγLip hW
        ((Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2))).toLp _ := by
  apply boundaryFourier.injective; apply lp.ext; funext n
  have hfour : boundaryFourier (regularCorrectedBoundaryOperator hγLip hW hc g) n =
      (Real.sqrt (2 * Real.pi) : ℂ) * fourierCoeffOn Real.two_pi_pos
        (fun θ => ∫ s in (0 : ℝ)..(2 * Real.pi), correctedKernel W θ s * g s) n := by
    change (fourierBasis (T := 2 * Real.pi)).repr
      (boundaryCircleUnitary (boundaryCircleUnitary.symm
        (correctedKernelL2Op hγLip hW hc (boundaryCircleUnitary g)))) n = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    change (fourierBasis (T := 2 * Real.pi)).repr
      (correctedKernelL2Op hγLip hW hc ((Real.sqrt (2 * Real.pi) : ℂ) • boundaryCircleLift g)) n = _
    rw [map_smul, map_smul]
    change (Real.sqrt (2 * Real.pi) : ℂ) *
      (fourierBasis (T := 2 * Real.pi)).repr (correctedKernelL2Op hγLip hW hc (boundaryCircleLift g)) n = _
    congr 1; rw [fourierBasis_repr]
    change fourierCoeff ((memLp_kernelL2Action (measurable_ckPer hW)
      (norm_ckPer_le hγLip hW) (fun θ θ' s _ => ckPer_lip hγLip hW hc θ θ' s)
        (boundaryCircleLift g)).toLp _) n = _
    rw [fourierCoeff_congr_ae (MemLp.coeFn_toLp
      (memLp_kernelL2Action (measurable_ckPer hW) (norm_ckPer_le hγLip hW)
        (fun θ θ' s _ => ckPer_lip hγLip hW hc θ θ' s) (boundaryCircleLift g))),
      fourierCoeff_liftIco_two_pi]
    refine congrFun (fourierCoeffOn_congr_ae Real.two_pi_pos ?_) n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    rw [kernelL2Action_eq_haar_integral]
    have he : (fun x : AddCircle (2 * Real.pi) =>
        ckPer W θ (circRep x) * boundaryCircleLift g x) =ᵐ[AddCircle.haarAddCircle]
        AddCircle.liftIco (2 * Real.pi) 0 (fun s => ckPer W θ s * g s) := by
      filter_upwards [boundaryCircleLift_coe g, boundary_liftIoc_eq_liftIco_ae (g : ℝ → ℂ)] with x hx hrep
      rw [hx, hrep, liftIco_eq_comp, liftIco_eq_comp]
    rw [integral_congr_ae he, two_pi_mul_integral_liftIco]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le Real.two_pi_pos.le] at hs
    rw [ckPer_eq hγLip hW hc (Ioc_subset_Icc_self hθ) hs]
  rw [hfour, boundaryFourier_apply]; congr 1
  exact (congrFun (fourierCoeffOn_congr_ae Real.two_pi_pos
    (MemLp.coeFn_toLp (memLp_regularCorrectedAction hγLip hW
      ((Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2))))) n).symm

private theorem continuous_row_intervalIntegrable
    {a : ℝ → ℂ} (ha : ContinuousOn a (Icc 0 (2 * Real.pi)))
    (g : BoundaryL2) {s t : ℝ} (hs : s ∈ Icc 0 (2 * Real.pi))
    (ht : t ∈ Icc 0 (2 * Real.pi)) :
    IntervalIntegrable (fun x => a x * g x) volume s t := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  have hi : Integrable (fun x => a x * g x) μB :=
    ((Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2)).bdd_mul
      ((ha.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => hB x (Ioc_subset_Icc_self hx))
  exact IntervalIntegrable.mono_set'
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr hi)
    (uIoc_subset_uIoc_of_uIcc_subset_uIcc (by rw [uIcc_of_le Real.two_pi_pos.le]; exact uIcc_subset_Icc hs ht))

private theorem periodicP_eq_kernel_integrals_boundaryL2
    {γ : ℝ → ℂ} {L : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hγLip : LipschitzWith L γ) (hW : IsTransport γ E W)
    (t : ℝ → ℂ) (g : BoundaryL2) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    periodicP W t (g : ℝ → ℂ) θ = 2 * t θ +
      (∫ s in (0 : ℝ)..(2 * Real.pi), sawtoothKernel θ s * g s) +
      (∫ s in (0 : ℝ)..(2 * Real.pi), correctedKernel W θ s * g s) := by
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * Real.pi) := ⟨le_rfl, Real.two_pi_pos.le⟩
  have hT : (2 * Real.pi) ∈ Icc 0 (2 * Real.pi) := ⟨Real.two_pi_pos.le, le_rfl⟩
  have hwc : ContinuousOn (fun s => volterraKernel W θ s) (Icc 0 (2 * Real.pi)) :=
    ((innerSL ℂ (basisVec 0)).comp (W θ)).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0))
  have hwi : ∀ {s t : ℝ}, s ∈ Icc 0 (2 * Real.pi) → t ∈ Icc 0 (2 * Real.pi) →
      IntervalIntegrable (fun x => volterraKernel W θ x * g x) volume s t :=
    fun hs ht => continuous_row_intervalIntegrable hwc g hs ht
  have hk (s : ℝ) : conj (volterraKernel W s θ) = volterraKernel W θ s := by
    simp only [volterraKernel]
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]
  have hv : Complex.I * (volterraOp W (g : ℝ → ℂ) θ - volterraOpAdj W (g : ℝ → ℂ) θ) =
      ∫ s in (0 : ℝ)..(2 * Real.pi), Complex.I *
        ((Real.sign (θ - s) : ℂ) * (volterraKernel W θ s * g s)) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral_sign_mul_of_integrable hθ (hwi h0 hθ) (hwi hθ hT)]
    simp only [volterraOp, volterraOpAdj, hk]
  have hbi : IntervalIntegrable
      (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) volume 0 (2 * Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
      (integrable_boundary_observation_load hγLip hW g)
  have hobs := ((innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))).intervalIntegral_comp_comm hbi
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_smul, smul_eq_mul] at hobs
  have ho : observation W (cutBE W (observationAdj W (g : ℝ → ℂ))) θ =
      ∫ s in (0 : ℝ)..(2 * Real.pi),
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s := by
    rw [observation, observationAdj, ← hobs]
    exact intervalIntegral.integral_congr fun _ _ => by ring
  have hs : IntervalIntegrable (fun s =>
      Complex.I * ((Real.sign (θ - s) : ℂ) * (volterraKernel W θ s * g s))) volume 0 (2 * Real.pi) :=
    (intervalIntegrable_sign_mul_of_integrable hθ (hwi h0 hθ) (hwi hθ hT)).const_mul _
  have hoc : ContinuousOn (fun s =>
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ) (Icc 0 (2 * Real.pi)) :=
    ((innerSL ℂ (basisVec 0)).comp ((W θ).comp (cutBE W))).continuous.comp_continuousOn
      (continuousOn_adjoint_apply hW.1 (basisVec 0))
  have hoi := continuous_row_intervalIntegrable hoc g h0 hT
  have hgi : ∀ {s t : ℝ}, s ∈ Icc 0 (2 * Real.pi) → t ∈ Icc 0 (2 * Real.pi) →
      IntervalIntegrable (fun x => g x) volume s t := fun hs ht => by
    simpa only [one_mul] using continuous_row_intervalIntegrable (continuousOn_const (c := (1 : ℂ))) g hs ht
  have hsaw : IntervalIntegrable (fun s => sawtoothKernel θ s * g s) volume 0 (2 * Real.pi) :=
    (((intervalIntegrable_sign_mul_of_integrable hθ (hgi h0 hθ) (hgi hθ hT)).const_mul Complex.I).sub
      ((continuous_row_intervalIntegrable (a := fun s => (((θ - s) / Real.pi : ℝ) : ℂ))
        (by fun_prop) g h0 hT).const_mul Complex.I)).congr fun s _ => by
      simp only [sawtoothKernel]; push_cast; ring
  have hcorr : IntervalIntegrable (fun s => correctedKernel W θ s * g s) volume 0 (2 * Real.pi) :=
    (((hs.add hoi).sub hsaw).congr fun s _ => by
      have he := sawtoothKernel_add_correctedKernel (W := W) θ s
      calc _ = (Complex.I * (Real.sign (θ - s) : ℂ) * volterraKernel W θ s +
            ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ) * g s -
            sawtoothKernel θ s * g s := by ring
        _ = correctedKernel W θ s * g s := by rw [← he]; ring)
  rw [periodicP_eq_doubleTrace_add_correctedVolterraAction, correctedVolterraAction, hv, ho,
    ← intervalIntegral.integral_add hs hoi, add_assoc, ← intervalIntegral.integral_add hsaw hcorr]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  have he := sawtoothKernel_add_correctedKernel (W := W) θ s
  change Complex.I * ((Real.sign (θ - s) : ℂ) * (volterraKernel W θ s * g s)) +
      ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ * g s = _
  calc _ = (Complex.I * (Real.sign (θ - s) : ℂ) * volterraKernel W θ s +
        ⟪basisVec 0, W θ (cutBE W (ContinuousLinearMap.adjoint (W s) (basisVec 0)))⟫_ℂ) * g s := by ring
    _ = sawtoothKernel θ s * g s + correctedKernel W θ s * g s := by rw [← he]; ring

/-! ### Part 4: Trace reparametrization, Herglotz observation & finite-rank chart helpers -/

private theorem isC1TraceReparam_ae_comp {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) {p : ℝ → Prop}
    (hp : ∀ᵐ s ∂μB, p s) : ∀ᵐ θ ∂μB, p (τ θ) := by
  classical
  let q : ℝ → ℝ := fun s => if p s then 0 else 1
  have hqzero : q =ᵐ[μB] 0 := by filter_upwards [hp] with s hs; simp [q, hs]
  have hq : IntegrableOn q (Ioc 0 (2 * π)) := (MeasureTheory.integrable_zero ℝ ℝ μB).congr hqzero.symm
  have himage : τ '' Icc (0 : ℝ) (2 * π) = Icc (0 : ℝ) (2 * π) := by
    simpa only [hτ.zero, hτ.endpoint] using
      hτ.continuous.continuousOn.image_Icc_of_monotoneOn two_pi_pos.le (hτ.monotone.monotoneOn _)
  have hq' : IntegrableOn q (Icc 0 (2 * π)) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (f := q) (by finiteness)).mpr hq
  have hj : IntegrableOn (fun θ => deriv τ θ • q (τ θ)) (Icc 0 (2 * π)) :=
    (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn measurableSet_Icc
      (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt)
      (hτ.monotone.monotoneOn (Icc 0 (2 * π))) q).mp (by simpa only [himage] using hq')
  have hj' : IntegrableOn (fun θ => deriv τ θ * q (τ θ)) (Ioc 0 (2 * π)) := by
    simpa only [smul_eq_mul] using
      (integrableOn_Icc_iff_integrableOn_Ioc (f := fun θ => deriv τ θ • q (τ θ)) (by finiteness)).mp hj
  have hchange := integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Icc
    (fun θ _ => (hτ.contDiff.differentiable_one θ).hasDerivAt.hasDerivWithinAt)
    (hτ.monotone.monotoneOn (Icc 0 (2 * π))) q
  have hz : (∫ θ in Ioc 0 (2 * π), deriv τ θ * q (τ θ)) = 0 := by
    rw [show (∫ θ in Ioc 0 (2 * π), deriv τ θ * q (τ θ)) = ∫ s in Ioc 0 (2 * π), q s by
      simpa only [himage, integral_Icc_eq_integral_Ioc, smul_eq_mul] using hchange.symm,
      integral_congr_ae hqzero]
    simp only [Pi.zero_apply, integral_zero]
  have hnonneg : 0 ≤ᵐ[μB] (fun θ => deriv τ θ * q (τ θ)) := Eventually.of_forall fun θ =>
    mul_nonneg hτ.monotone.deriv_nonneg (by simp only [q]; split_ifs <;> norm_num)
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnonneg hj').mp hz,
    ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hτ.lower_ae] with θ hzero hlower
  by_contra hbad
  exact (hτ.lower_pos.trans_le hlower).ne' (by simpa only [q, if_neg hbad, mul_one, Pi.zero_apply] using hzero)

private def localConformalHerglotzCoordinateLoad (F : ℂ → ℂ) {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) : BoundaryL2 :=
  (memLp_herglotzConormal ha k hΓLip).toLp (herglotzConormal k a (physicalCircleTrace F))

private theorem localConformalHerglotzBoundaryLoad_eq_coordinateLoad
    (F : ℂ → ℂ) {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))
    {L : NNReal} (hΓLip : LipschitzWith L (physicalCircleTrace F))
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha k) =
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
        (boundaryFourier (localConformalHerglotzCoordinateLoad F hΓLip ha k)) := by
  unfold localConformalBoundaryLoad; congr 2
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hΓ : physicalCircleTrace F = γ ∘ τ := funext hcoord
  have hc : herglotzConormal k a (γ ∘ τ) =ᵐ[μB]
      (fun θ => deriv τ θ • herglotzConormal k a γ (τ θ)) := by
    filter_upwards [isC1TraceReparam_ae_comp hτ
      (ae_restrict_of_ae (hKγ.ae_differentiableAt (μ := volume)))] with θ hγdiff
    have hd := hγdiff.hasDerivAt.scomp θ (hτ.contDiff.differentiable_one θ).hasDerivAt
    rw [herglotzConormal_eq ha.intervalIntegrable, hd.deriv, herglotzConormal_eq ha.intervalIntegrable]
    simp only [Function.comp_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]; ring
  rw [← hΓ] at hc
  apply Lp.ext
  filter_upwards [traceReparamConormalL2_ae hτ (herglotzConormalL2 hγ ha k),
    isC1TraceReparam_ae_comp hτ (herglotzConormalL2_ae hγ ha k), hc,
    (memLp_herglotzConormal ha k hΓLip).coeFn_toLp] with θ ht hr hc' hg
  rw [ht, hr, show (localConformalHerglotzCoordinateLoad F hΓLip ha k : ℝ → ℂ) θ = _ from hg]
  exact hc'.symm

private def regularHerglotzObservationVector {γ : ℝ → ℂ} (E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2) {a : ℝ → ℂ} (ha : IsDirDensity a) : Ell2 :=
  (Real.sqrt 2 : ℂ) •
      (herglotzVec ha (Real.sqrt E) (γ 0) +
        ContinuousLinearMap.adjoint (W (2 * π)) (herglotzVec ha (Real.sqrt E) (γ 0))) +
    cutBE W (observationAdj W (herglotzConormal (Real.sqrt E) a γ))

private theorem periodicP_herglotz_eq_regularObservation {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    periodicP W (fun s => herglotzWave (Real.sqrt E) a (γ s))
        (herglotzConormal (Real.sqrt E) a γ) θ =
      observation W (regularHerglotzObservationVector (γ := γ) E W ha) θ := by
  rw [periodicP, periodicA_herglotz_eq_observation hK hclosed hW ha hθ]
  simp only [regularHerglotzObservationVector, cutBE, observation, map_add, inner_add_right]

private theorem regularHerglotzObservationVector_cutProj
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    cutProj (cutC (W (2 * π)) (basisVec 0))
        (regularHerglotzObservationVector (γ := γ) E W ha) =
      regularHerglotzObservationVector (γ := γ) E W ha := by
  rw [cutProj_eq_starProjection, Submodule.starProjection_eq_self_iff,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  obtain ⟨hgm, _, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  have hn : (fun s => herglotzWave (Real.sqrt E) a (γ s)) (2 * π) =
      (fun s => herglotzWave (Real.sqrt E) a (γ s)) 0 := congrArg (herglotzWave (Real.sqrt E) a) hclosed
  have hp := periodicP_periodic (n := fun s => herglotzWave (Real.sqrt E) a (γ s)) hK hW hc hn hgm hgB
  rw [periodicP_herglotz_eq_regularObservation hK hclosed hW ha ⟨two_pi_pos.le, le_rfl⟩,
    periodicP_herglotz_eq_regularObservation hK hclosed hW ha ⟨le_rfl, two_pi_pos.le⟩] at hp
  rw [← observation_jump hW]; exact sub_eq_zero.mpr hp

private theorem halfSmoothing_adjoint_projObsDual
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (z : Ell2) :
    sobolevSmoothing (1 / 2) (by norm_num)
      ((√(2 * π) : ℂ) • ContinuousLinearMap.adjoint (projObsDual W) z) =
        boundaryFourier (projectedObservationBoundary hK hW z) := by
  rw [projObsDual_eq hK hW, rowSynth, ContinuousLinearMap.adjoint_adjoint]
  apply lp.ext; funext n
  have hw : ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Real.sqrt (sobWeight n) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, Real.sqrt_eq_rpow, ← Real.rpow_add (sobWeight_pos n)]; norm_num
  simp only [sobolevSmoothing, diagOp_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    rowAnalysis_apply, normProjObsRow, inner_smul_left, Complex.conj_ofReal,
    boundaryFourier_projectedObservation]
  change ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    ((√(2 * π) : ℂ) * ((Real.sqrt (sobWeight n) : ℂ) * ⟪projObsCoeffVec W n, z⟫_ℂ)) = _
  calc _ = (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (Real.sqrt (sobWeight n) : ℂ)) *
          ((√(2 * π) : ℂ) * ⟪projObsCoeffVec W n, z⟫_ℂ) := by ring
    _ = _ := by rw [hw, one_mul]

private theorem regular_halfSmoothing_injective :
    Function.Injective (sobolevSmoothing (1 / 2) (by norm_num) : L2Z →L[ℂ] L2Z) := fun f g h =>
  lp.ext <| funext fun n => by
    have hn := congrArg (fun v : L2Z => v n) h
    simp only [sobolevSmoothing, diagOp_apply] at hn
    exact mul_left_cancel₀ (by exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) _).ne') hn

private def localConformalHerglotzBoundaryLin {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (k : ℝ) : dirDensities →ₗ[ℂ] L2Z :=
  let hLin : dirDensities →ₗ[ℂ] BoundaryL2 :=
    { toFun := fun a => herglotzConormalL2 hγ a.property k
      map_add' := fun a b => Lp.ext <| by
        filter_upwards [herglotzConormalL2_ae hγ (a + b).property k,
          herglotzConormalL2_ae hγ a.property k, herglotzConormalL2_ae hγ b.property k,
          Lp.coeFn_add (herglotzConormalL2 hγ a.property k) (herglotzConormalL2 hγ b.property k)]
          with θ hab ha hb hs
        rw [hab, hs]; simp only [Pi.add_apply, ha, hb]
        exact congrFun (herglotzConormal_add_density a.property b.property k γ) θ
      map_smul' := fun c' a => Lp.ext <| by
        filter_upwards [herglotzConormalL2_ae hγ (c' • a).property k,
          herglotzConormalL2_ae hγ a.property k,
          Lp.coeFn_smul c' (herglotzConormalL2 hγ a.property k)] with θ hca ha hs
        simp only [RingHom.id_apply]; rw [hca, hs]; simp only [Pi.smul_apply, ha, smul_eq_mul]
        exact congrFun (herglotzConormal_smul_density a.property c' k γ) θ }
  let rLin : BoundaryL2 →ₗ[ℂ] BoundaryL2 :=
    { toFun := traceReparamConormalL2 hτ
      map_add' := fun g h => Lp.ext <| by
        filter_upwards [traceReparamConormalL2_ae hτ (g + h), traceReparamConormalL2_ae hτ g,
          traceReparamConormalL2_ae hτ h,
          Lp.coeFn_add (traceReparamConormalL2 hτ g) (traceReparamConormalL2 hτ h),
          isC1TraceReparam_ae_comp hτ (Lp.coeFn_add g h)] with θ hab hg hh hs hc
        rw [hab, hs]; simp only [Pi.add_apply, hg, hh, hc, smul_add]
      map_smul' := fun a g => Lp.ext <| by
        filter_upwards [traceReparamConormalL2_ae hτ (a • g), traceReparamConormalL2_ae hτ g,
          Lp.coeFn_smul a (traceReparamConormalL2 hτ g),
          isC1TraceReparam_ae_comp hτ (Lp.coeFn_smul a g)] with θ hag hg hs hc
        simp only [RingHom.id_apply]; rw [hag, hs]; simp only [Pi.smul_apply, hg, hc]
        exact smul_comm (deriv τ θ) a (g (τ θ)) }
  ((sobolevSmoothing (1 / 2 : ℝ) (by norm_num)).toLinearMap.comp
    (boundaryFourier.toLinearMap.comp rLin)).comp hLin

private def originalNeumannResonanceH1Basis {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    OrthonormalBasis (Fin (originalNeumannMultiplicity Ω E)) ℂ (h1ResonantSpace Ω E) :=
  letI := finiteDimensional_h1ResonantSpace hb hL E
  (stdOrthonormalBasis ℂ (h1ResonantSpace Ω E)).reindex <| finCongr <| by
    rw [originalNeumannMultiplicity, ← h1ResonantSpace_multiplicity_eq hb hL hE]
    exact (ENat.toNat_coe _).symm

private theorem finiteFourierChart_regular_compression_sub_four_compact {d : ℕ}
    (u : Fin d → H₁) (v : Fin d → L2Z) (P : L2Z →L[ℂ] L2Z)
    (hP : IsCompactOperator (P - (4 : ℂ) • posProj)) :
    IsCompactOperator (adjoint (finiteFourierChart u v) ∘L P ∘L finiteFourierChart u v -
      (4 : ℂ) • ContinuousLinearMap.id ℂ H₁) := by
  have hrk {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
      [NormedAddCommGroup Y] [NormedSpace ℂ Y] (y : Y) (x : X) :
      IsCompactOperator (InnerProductSpace.rankOne ℂ y x) :=
    (isCompactOperator_of_finiteDimensional_range (ContinuousLinearMap.toSpanSingleton ℂ y)).comp_clm
      (innerSL ℂ x)
  have hsum {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
      [NormedAddCommGroup Y] [NormedSpace ℂ Y] (s : Finset (Fin d)) (T : Fin d → X →L[ℂ] Y)
      (hT : ∀ i ∈ s, IsCompactOperator (T i)) : IsCompactOperator (∑ i ∈ s, T i : X →L[ℂ] Y) := by
    induction s using Finset.induction_on with
    | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : X →L[ℂ] Y))
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hT i (Finset.mem_insert_self _ _)).add (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))
  have hsub : IsCompactOperator (finiteFourierChart u v - Submodule.subtypeL H₁) := by
    simp only [finiteFourierChart, add_sub_cancel_left]
    exact hsum Finset.univ _ fun i _ => hrk (v i) (u i)
  have hadj : IsCompactOperator (adjoint (finiteFourierChart u v) - adjoint (Submodule.subtypeL H₁)) := by
    simp only [finiteFourierChart, map_add, map_sum, InnerProductSpace.adjoint_rankOne, add_sub_cancel_left]
    exact hsum Finset.univ _ fun i _ => hrk (u i) (v i)
  have hcomp_id : adjoint (Submodule.subtypeL H₁) ∘L posProj ∘L Submodule.subtypeL H₁ =
      ContinuousLinearMap.id ℂ H₁ := ContinuousLinearMap.ext fun z => by
    simp only [Submodule.adjoint_subtypeL, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, ContinuousLinearMap.id_apply]
    rw [← nonpositive_orthogonal_starProjection, Submodule.starProjection_mem_subspace_eq_self]
    exact Submodule.orthogonalProjection_mem_subspace_eq_self z
  have hpos : IsCompactOperator (adjoint (finiteFourierChart u v) ∘L posProj ∘L
      finiteFourierChart u v - ContinuousLinearMap.id ℂ H₁) := by
    rw [show adjoint (finiteFourierChart u v) ∘L posProj ∘L finiteFourierChart u v -
        ContinuousLinearMap.id ℂ H₁ =
        adjoint (finiteFourierChart u v) ∘L posProj ∘L (finiteFourierChart u v - Submodule.subtypeL H₁) +
          (adjoint (finiteFourierChart u v) - adjoint (Submodule.subtypeL H₁)) ∘L
            posProj ∘L Submodule.subtypeL H₁ by
      simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, hcomp_id]; abel]
    exact ((hsub.clm_comp posProj).clm_comp (adjoint (finiteFourierChart u v))).add
      ((hadj.comp_clm posProj).comp_clm (Submodule.subtypeL H₁))
  rw [show adjoint (finiteFourierChart u v) ∘L P ∘L finiteFourierChart u v -
      (4 : ℂ) • ContinuousLinearMap.id ℂ H₁ =
      adjoint (finiteFourierChart u v) ∘L (P - (4 : ℂ) • posProj) ∘L finiteFourierChart u v +
        (4 : ℂ) • (adjoint (finiteFourierChart u v) ∘L posProj ∘L finiteFourierChart u v -
          ContinuousLinearMap.id ℂ H₁) by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_sub]; abel]
  exact ((hP.comp_clm (finiteFourierChart u v)).clm_comp (adjoint (finiteFourierChart u v))).add
    (hpos.smul (4 : ℂ))

private theorem chart_reduced_boundary_bound_on_energy_set {H Y : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K₀ : Submodule ℂ H) [K₀.HasOrthogonalProjection]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    {m : ℕ} (J : ℝ → K₀ →L[ℂ] H) (R : K₀ᗮ →L[ℂ] H) (E₀ : ℝ) (U : Set ℝ)
    (hunit : ∀ E ∈ U, IsUnit (J E ∘L K₀.orthogonalProjection + R ∘L K₀ᗮ.orthogonalProjection))
    (P Preg : ℝ → H →L[ℂ] H) (S : ℝ → H →L[ℂ] Y) (w : Fin m → H)
    (hsa : ∀ E ∈ U, IsSelfAdjoint (P E))
    (hnullP : ∀ E ∈ U, P E ∘L J E = 0) (hnullS : ∀ E ∈ U, S E ∘L J E = 0)
    (hpole : ∀ E ∈ U, P E = ((-2 / (E - E₀) : ℝ) : ℂ) • ∑ j, rankOne ℂ (w j) (w j) + Preg E)
    (hPreg : ContinuousAt Preg E₀) (hS : ContinuousAt S E₀)
    (α : ℝ) (hα : 0 < α) (C : K₀ᗮ →L[ℂ] K₀ᗮ) (hC : IsCompactOperator C)
    (hreg : adjoint R ∘L Preg E₀ ∘L R = (α : ℂ) • ContinuousLinearMap.id ℂ K₀ᗮ + C)
    (hinj : ∀ z : K₀ᗮ, (∀ j, ⟪adjoint R (w j), z⟫_ℂ = 0) → S E₀ (R z) = 0 → z = 0) :
    ∃ A₀ > 0, ∃ V ∈ 𝓝 E₀, ∀ E ∈ V, E ∈ U →
      ∃ ℓ : H →ₗ[ℂ] (Fin m → ℂ), ∀ y, ℓ y = 0 → -(A₀ * ‖S E y‖ ^ 2) ≤ (⟪y, P E y⟫_ℂ).re := by
  set η : Fin m → K₀ᗮ := fun j => adjoint R (w j)
  set Z : Submodule ℂ K₀ᗮ := (Submodule.span ℂ (Set.range η))ᗮ
  have hmemZ (z : K₀ᗮ) : z ∈ Z ↔ ∀ j, ⟪η j, z⟫_ℂ = 0 :=
    ⟨fun hz j => (Submodule.mem_orthogonal _ _).1 hz _ (Submodule.subset_span ⟨j, rfl⟩),
     fun h => (Submodule.mem_orthogonal _ _).2 fun u hu => by
      induction hu using Submodule.span_induction with
      | mem _ hx => obtain ⟨j, rfl⟩ := hx; exact h j
      | zero => simp
      | add _ _ _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul _ _ _ hx => rw [inner_smul_left, hx, mul_zero]⟩
  obtain ⟨A₀, hA₀, hev⟩ := reduced_lower_bound_subspace Z α hα C hC
    (fun E => adjoint R ∘L Preg E ∘L R) (fun E => S E ∘L R) E₀
    (continuousAt_const.clm_comp (hPreg.clm_comp continuousAt_const))
    (hS.clm_comp continuousAt_const) hreg (fun z hz h0 => hinj z ((hmemZ z).1 hz) h0)
  refine ⟨A₀, hA₀, _, hev, fun E hE hEU => ?_⟩
  obtain ⟨u, hu⟩ := hunit E hEU
  set zc : H →L[ℂ] K₀ᗮ := K₀ᗮ.orthogonalProjection ∘L (↑u⁻¹ : H →L[ℂ] H)
  refine ⟨LinearMap.pi fun j => (((innerSL ℂ (η j)) ∘L zc : H →L[ℂ] ℂ) : H →ₗ[ℂ] ℂ), fun y hy => ?_⟩
  set x := (↑u⁻¹ : H →L[ℂ] H) y with hx
  set a := K₀.orthogonalProjection x
  set z := K₀ᗮ.orthogonalProjection x
  have hzj : ∀ j, ⟪η j, z⟫_ℂ = 0 := congrFun hy
  have hyx : y = J E a + R z := by
    have h1 : (u : H →L[ℂ] H) x = y := by
      rw [hx, ← ContinuousLinearMap.mul_apply, Units.mul_inv, ContinuousLinearMap.one_apply]
    rw [← h1, hu]; rfl
  have hSy : S E y = S E (R z) := by
    rw [hyx, map_add, show S E (J E a) = 0 by simpa using congrArg (· a) (hnullS E hEU), zero_add]
  have hPJa : P E (J E a) = 0 := by simpa using congrArg (· a) (hnullP E hEU)
  have hPy : ⟪y, P E y⟫_ℂ = ⟪R z, P E (R z)⟫_ℂ := by
    rw [hyx, map_add, hPJa, zero_add, inner_add_left,
      show ⟪J E a, P E (R z)⟫_ℂ = 0 by rw [← (hsa E hEU).adjoint_eq, adjoint_inner_right, hPJa, inner_zero_left],
      zero_add]
  have hpz : ⟪R z, P E (R z)⟫_ℂ = ⟪z, (adjoint R ∘L Preg E ∘L R) z⟫_ℂ := by
    rw [hpole E hEU, inner_pole_add_eq_of_orthogonal w _ _ _ (fun j => by rw [← adjoint_inner_left]; exact hzj j),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, adjoint_inner_right]
  rw [hPy, hpz, hSy]
  exact hE z ((hmemZ z).2 hzj)

/-! ### Part 5: Unified conformal Vekua forward nullity, Herglotz identity & transfer bound -/

section SuppliedCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "ΓF" => physicalCircleTrace F
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "JF" => localConformalHardyPrimitive hR F hFs
local notation "VF" => localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "UR" => localConformalVekuaTraceRow hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "YF" => localConformalVekuaTransportVector hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NF" => normalizedConormal hβF haF hgF

private def localConformalVekuaForwardLoad (E : ℂ) (b : L2Z)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) : BoundaryL2 :=
  boundaryFourier.symm (sobVec (1 / 2 : ℝ) (NF E b : ℤ → ℂ)
    (normalizedConormal_preserves_half_regular hβF haF hgF E b hbhalf))

private theorem localConformalVekuaForwardLoad_normalized (E : ℂ) (b : L2Z)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ)) :
    sobolevSmoothing (1 / 2 : ℝ) (by norm_num)
      (boundaryFourier (localConformalVekuaForwardLoad hR F hFs E b hbhalf)) = NF E b := by
  rw [localConformalVekuaForwardLoad, boundaryFourier.apply_symm_apply]
  exact lp.ext <| funext fun n => congrFun (fromL2_sobVec (1 / 2 : ℝ) _ _) n

private theorem localConformalVekuaForward_transport_eq
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {L : NNReal} (hΓLip : LipschitzWith L ΓF)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    YF E b θ = W θ (YF E b 0) +
      physicalDrivenVector W (localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf : ℝ → ℂ) θ := by
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) :=
    isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  have hΓ : ContDiff ℝ 1 ΓF :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  let g := localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf
  have hy := localConformalVekuaTransportVector_continuousOn hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E b hbn hb1
  refine driven_eq_transport_add_physicalDrivenVector_boundaryL2 hΓLip hΓ hW g hy (fun t ht => ?_) hθ
  let G : BoundaryL2 := boundaryContinuousMultiplier (localConformalVelocityCircle F)
    (TF (VF (F 1) (E : ℂ) (JF b)))
  let L0 : BoundaryL2 := (2 * (-(E : ℂ) / 4)) • G - Complex.I • g
  have hL0coeff (n : ℤ) : fourierCoeffOn Real.two_pi_pos (L0 : ℝ → ℂ) n =
      (Complex.I * (n : ℂ)) * fourierCoeffOn Real.two_pi_pos (UR (E : ℂ) b 0) n := by
    have ht0 : (TF (VF (F 1) (E : ℂ) b) : ℝ → ℂ) =ᵐ[μB] UR (E : ℂ) b 0 := by
      unfold localConformalVekuaTraceRow
      simpa only [pow_zero, ContinuousLinearMap.one_apply] using
        localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL hhol hinj hC hK
          e he hsource hes (E : ℂ) b hbn hb1
    have hNC := localConformalVekua_normalizedConormal_fourier hR F hFs hb hL hhol hinj hC hK
      e he hsource hes (E : ℂ) b hbn hb1 n
    have hload := congrArg (fun v : L2Z => v n)
      (localConformalVekuaForwardLoad_normalized hR F hFs (E : ℂ) b hbhalf)
    change ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * boundaryFourier g n = NF (E : ℂ) b n at hload
    simp only [localConformalVekuaGradientA_apply, map_smul, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul] at hNC
    have hw : (((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (sobWeight_pos n) _).ne'
    have hn := mul_left_cancel₀ hw (hNC.symm.trans hload.symm)
    apply mul_left_cancel₀ (by exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne' : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0)
    calc _ = boundaryFourier L0 n := (boundaryFourier_apply L0 n).symm
      _ = (Complex.I * (n : ℂ)) * boundaryFourier (TF (VF (F 1) (E : ℂ) b)) n := by
        simp only [L0, map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply,
          lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        rw [← hn]; dsimp only [G]; ring_nf; simp [Complex.I_sq]
      _ = _ := by rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos ht0]; ring
  have hAE : (L0 : ℝ → ℂ) =ᵐ[μB]
      fun s => 2 * (-(E : ℂ) / 4) * deriv ΓF s * UR (E : ℂ) b 1 s - Complex.I * g s := by
    have ht1 := localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL hhol
      hinj hC hK e he hsource hes (E : ℂ) (JF b)
      (localConformalHardyPrimitive_nonpositive hR F hFs hhol b hbn)
      (by simpa only [pow_one] using localConformalHardyPrimitive_pow_raw_H1 hR F hFs b hb1 1)
    filter_upwards [Lp.coeFn_sub ((2 * (-(E : ℂ) / 4)) • G) (Complex.I • g),
      Lp.coeFn_smul (2 * (-(E : ℂ) / 4)) G, Lp.coeFn_smul Complex.I g,
      boundaryContinuousMultiplier_ae (localConformalVelocityCircle F) (TF (VF (F 1) (E : ℂ) (JF b))),
      ht1] with s hsub hs htg hG htrace
    rw [hsub]; simp only [Pi.sub_apply]; rw [hs, htg]
    simp only [Pi.smul_apply, smul_eq_mul, G, g, hG, htrace,
      localConformalVelocityCircle_apply hR F hFs, localConformalVekuaTraceRow, pow_one]; ring
  have hzero_int : UR (E : ℂ) b 0 t = UR (E : ℂ) b 0 0 + ∫ s in (0 : ℝ)..t,
      2 * (-(E : ℂ) / 4) * deriv ΓF s * UR (E : ℂ) b 1 s - Complex.I * g s := by
    rw [eq_add_integral_of_L2_periodic_fourier_derivative
      (localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol hinj hC hK
        e he hsource hes (E : ℂ) b hbn hb1 0)
      (localConformalVekuaTraceRow_periodic hR F hFs hb hL hhol hinj hC hK
        e he hsource hes (E : ℂ) b 0) L0 hL0coeff ht]
    congr 1; apply intervalIntegral.integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp hAE] with s hs hmem
    rw [uIoc_of_le ht.1] at hmem
    exact hs ⟨hmem.1, hmem.2.trans ht.2⟩
  let y := YF E b
  let p := localConformalVekuaPositiveTransportVector hR F hFs hb hL hhol hinj hC hK e he hsource hes E b
  let z : ℝ → ℂ := fun s => UR (E : ℂ) b 0 s / (Real.sqrt 2 : ℂ)
  let Cg := fun s => transportCoeff ΓF E s (y s)
  let a : ℝ → ℂ := fun s =>
    (2 * (-(E : ℂ) / 4) * deriv ΓF s * UR (E : ℂ) b 1 s - Complex.I * g s) / (Real.sqrt 2 : ℂ)
  have hCoeff : Continuous (transportCoeff ΓF E) := by
    have hd := hΓ.continuous_deriv_one; have hc := Complex.continuous_conj.comp hd
    unfold transportCoeff; fun_prop
  have hCg : ContinuousOn Cg (Icc 0 (2 * Real.pi)) := hCoeff.continuousOn.clm_apply hy
  have hC0 : ContinuousOn (fun s => (Cg s : ℕ → ℂ) 0) (Icc 0 (2 * Real.pi)) := by
    convert (innerSL ℂ (basisVec 0)).continuous.continuousOn.comp hCg (fun _ _ => Set.mem_univ _) using 1
    funext s; simp only [Function.comp_apply, innerSL_apply_apply, inner_basisVec]
  have hz : Continuous z :=
    (localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol hinj hC hK
      e he hsource hes (E : ℂ) b hbn hb1 0).div_const _
  have hsplit (s : ℝ) (hs : s ∈ Icc 0 (2 * Real.pi)) : y s = z s • basisVec 0 + p s :=
    localConformalVekuaTransportVector_zero_add_positive hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn hb1 hs
  have hp : ContinuousOn p (Icc 0 (2 * Real.pi)) :=
    (hy.sub (hz.continuousOn.smul (continuousOn_const : ContinuousOn (fun _ : ℝ => basisVec 0) _))).congr
      fun s hs => by change p s = y s - z s • basisVec 0; rw [hsplit s hs]; abel
  have hsub : Icc 0 t ⊆ Icc 0 (2 * Real.pi) := Icc_subset_Icc le_rfl ht.2
  have hpi : IntervalIntegrable (fun s => Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0) volume 0 t :=
    ((hCg.sub (hC0.smul continuousOn_const)).mono (by simpa only [uIcc_of_le ht.1] using hsub)).intervalIntegrable
  have hip := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hp.mono hsub)
    (fun s hs => (localConformalVekuaPositiveTransportVector_hasDerivAt hR F hFs hb hL
      hhol hinj hC hK e he hsource hes E b hbn hb1 ⟨hs.1, hs.2.trans_le ht.2⟩).congr_deriv
      (localConformalVekuaPositiveTransportDerivative_tsum_eq hR F hFs hb hL
        hhol hinj hC hK e he hsource hes E hE b hbn hb1 ⟨hs.1.le, hs.2.le.trans ht.2⟩)) hpi
  have hzp : z t = z 0 + ∫ s in (0 : ℝ)..t, a s := by
    simpa only [z, a, g, add_div, intervalIntegral.integral_div] using
      congrArg (fun v : ℂ => v / (Real.sqrt 2 : ℂ)) hzero_int
  have hac : Continuous (fun s => 2 * (-(E : ℂ) / 4) * deriv ΓF s * UR (E : ℂ) b 1 s) :=
    (continuous_const.mul hΓ.continuous_deriv_one).mul
      (localConformalVekuaTraceRow_continuous hR F hFs hb hL hhol hinj hC hK e he hsource hes (E : ℂ) b hbn hb1 1)
  have hgi : IntervalIntegrable (g : ℝ → ℂ) volume 0 t :=
    (intervalIntegrable_boundaryL2 g).mono_set' (by
      simp only [uIoc_of_le ht.1, uIoc_of_le Real.two_pi_pos.le]; exact Ioc_subset_Ioc le_rfl ht.2)
  have hai : IntervalIntegrable a volume 0 t :=
    ((hac.intervalIntegrable 0 t).sub (hgi.const_mul Complex.I)).div_const _
  have hai' : IntervalIntegrable (fun s => a s • basisVec 0) volume 0 t :=
    ⟨hai.1.smul_const _, hai.2.smul_const _⟩
  calc y t = z t • basisVec 0 + p t := hsplit t ht
    _ = (z 0 • basisVec 0 + p 0) + ((∫ s in (0 : ℝ)..t, a s) • basisVec 0 +
          ∫ s in (0 : ℝ)..t, Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0) := by
      rw [hzp, sub_eq_iff_eq_add.mp hip.symm, add_smul]; abel
    _ = y 0 + ∫ s in (0 : ℝ)..t, (a s • basisVec 0 + (Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0)) := by
      rw [← hsplit 0 ⟨le_rfl, Real.two_pi_pos.le⟩, ← intervalIntegral.integral_smul_const,
        ← intervalIntegral.integral_add hai' hpi]
    _ = _ := by
      congr 1; apply intervalIntegral.integral_congr; intro s hs
      rw [uIcc_of_le ht.1] at hs
      have hsc : s ∈ Icc 0 (2 * Real.pi) := ⟨hs.1, hs.2.trans ht.2⟩
      have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
      have hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hzero : (2 * (-(E : ℂ) / 4) * deriv ΓF s * UR (E : ℂ) b 1 s) /
          (Real.sqrt 2 : ℂ) = (Cg s : ℕ → ℂ) 0 := by
        rw [show (Cg s : ℕ → ℂ) 0 = _ from transportCoeff_coord_zero _ _ _ _,
          localConformalVekuaTransportVector_coord hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn hb1 hsc 1]
        simp only [localConformalVekuaTransportCoordinate, if_false, Nat.one_ne_zero, pow_one]
        change _ = physicalDrivenQ E * _
        rw [← physicalDrivenQ_sq hE]
        field_simp [hs0]
        linear_combination -(physicalDrivenQ E ^ 2 * deriv ΓF s * UR (E : ℂ) b 1 s) * hs2
      have haeq : a s = (Cg s : ℕ → ℂ) 0 - (Complex.I / (Real.sqrt 2 : ℂ)) * g s := by
        dsimp only [a]; rw [sub_div, hzero]; ring
      change a s • basisVec 0 + (Cg s - ((Cg s : ℕ → ℂ) 0) • basisVec 0) =
        Cg s + (-(Complex.I / (Real.sqrt 2 : ℂ)) * g s) • basisVec 0
      rw [haeq, sub_smul]; simp only [neg_mul, neg_smul]; abel

include hb hL hhol hinj hC hK e he hsource hes in
private theorem localConformalVekuaForward_observationAdj_eq_cut
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {L : NNReal} (hΓLip : LipschitzWith L ΓF)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W) :
    observationAdj W (localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf : ℝ → ℂ) =
      (Complex.I * hardyFourierTrace (normalizedHardyAverage b) 0) •
        cutC (W (2 * Real.pi)) (basisVec 0) := by
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) :=
    isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let y := YF E b
  let g := localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf
  let h0 := hardyFourierTrace (normalizedHardyAverage b) 0
  have hinit : y 0 = (h0 / (Real.sqrt 2 : ℂ)) • basisVec 0 :=
    localConformalVekuaTransportVector_origin hR F hFs hb hL hhol hinj hC hK e he hsource hes E b hbn hb1
  have hper : y (2 * Real.pi) = y 0 := by
    simpa only [zero_add] using localConformalVekuaTransportVector_periodic hR F hFs hb hL hhol hinj hC hK e he hsource hes E b 0
  have hT : (2 * Real.pi) ∈ Icc 0 (2 * Real.pi) := ⟨Real.two_pi_pos.le, le_rfl⟩
  have hform := localConformalVekuaForward_transport_eq hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE b hbn hbhalf hΓLip hW hT
  change y (2 * Real.pi) = W (2 * Real.pi) (y 0) +
    (-(Complex.I / (Real.sqrt 2 : ℂ))) • W (2 * Real.pi) (observationAdj W (g : ℝ → ℂ)) at hform
  rw [hper] at hform
  have hu : ContinuousLinearMap.adjoint (W (2 * Real.pi)) * W (2 * Real.pi) = 1 := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using (Unitary.mem_iff.mp (transport_mem_unitary hΓLip hW hT)).1
  have hadj := congrArg (ContinuousLinearMap.adjoint (W (2 * Real.pi))) hform
  rw [map_add, map_smul, ← ContinuousLinearMap.mul_apply, hu, ContinuousLinearMap.one_apply,
    ← ContinuousLinearMap.mul_apply, hu, ContinuousLinearMap.one_apply] at hadj
  have hsub : ContinuousLinearMap.adjoint (W (2 * Real.pi)) (y 0) - y 0 =
      (-(Complex.I / (Real.sqrt 2 : ℂ))) • observationAdj W (g : ℝ → ℂ) := by rw [hadj]; abel
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hO : observationAdj W (g : ℝ → ℂ) = ((Real.sqrt 2 : ℂ) * Complex.I) •
      (ContinuousLinearMap.adjoint (W (2 * Real.pi)) (y 0) - y 0) := by
    rw [hsub, smul_smul, show (Real.sqrt 2 : ℂ) * Complex.I * -(Complex.I / (Real.sqrt 2 : ℂ)) = 1 by
      field_simp [hs0]; simp [Complex.I_sq], one_smul]
  rw [hO, hinit, map_smul, ← smul_sub, smul_smul,
    show ((Real.sqrt 2 : ℂ) * Complex.I) * (h0 / (Real.sqrt 2 : ℂ)) = Complex.I * h0 by field_simp [hs0]]
  rfl

private theorem localConformalVekuaForward_periodicP_eq_zero
    (E : ℝ) (hE : 0 ≤ E) (b : L2Z) (hbn : IsNonpositiveFourierSupport b)
    (hbhalf : IsSobolevSeq (1 / 2 : ℝ) (b : ℤ → ℂ))
    {L : NNReal} (hΓLip : LipschitzWith L ΓF)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    periodicP W (UR (E : ℂ) b 0)
      (localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf : ℝ → ℂ) θ = 0 := by
  have hb1 : IsSobolevSeq 1 (fromL2 (1 / 2 : ℝ) b) :=
    isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf
  let g := localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf
  let h0 := hardyFourierTrace (normalizedHardyAverage b) 0
  have htr : UR (E : ℂ) b 0 θ = h0 * observation W (basisVec 0) θ - Complex.I * volterraOp W (g : ℝ → ℂ) θ := by
    have hinner := congrArg (fun v : Ell2 => ⟪basisVec 0, v⟫_ℂ)
      (localConformalVekuaForward_transport_eq hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E hE b hbn hbhalf hΓLip hW hθ)
    simp only [inner_add_right] at hinner
    have hleft : ⟪basisVec 0, YF E b θ⟫_ℂ = UR (E : ℂ) b 0 θ / (Real.sqrt 2 : ℂ) := by
      simpa only [inner_basisVec, localConformalVekuaTransportCoordinate, if_true] using
        localConformalVekuaTransportVector_coord hR F hFs hb hL hhol hinj hC hK
          e he hsource hes E b hbn hb1 hθ 0
    have hinit : ⟪basisVec 0, W θ (YF E b 0)⟫_ℂ =
        (h0 / (Real.sqrt 2 : ℂ)) * observation W (basisVec 0) θ := by
      change _ = _ * ⟪basisVec 0, W θ (basisVec 0)⟫_ℂ
      rw [localConformalVekuaTransportVector_origin hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E b hbn hb1, map_smul, inner_smul_right]
    have hi : IntervalIntegrable (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) volume 0 θ :=
      intervalIntegrable_iff.mpr (MeasureTheory.IntegrableOn.mono_set
        (integrable_boundary_observation_load hΓLip hW g)
        (by rw [uIoc_of_le hθ.1]; exact Ioc_subset_Ioc le_rfl hθ.2))
    have hcomm := ((innerSL ℂ (basisVec 0)).comp (W θ)).intervalIntegral_comp_comm hi
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] at hcomm
    have hforced : ⟪basisVec 0, physicalDrivenVector W (g : ℝ → ℂ) θ⟫_ℂ =
        -(Complex.I / (Real.sqrt 2 : ℂ)) * volterraOp W (g : ℝ → ℂ) θ := by
      rw [physicalDrivenVector, inner_smul_right, ← hcomm, volterraOp]
      congr 1; exact intervalIntegral.integral_congr fun _ _ => by
        simp only [map_smul, inner_smul_right, volterraKernel]; ring
    rw [hleft, hinit, hforced] at hinner
    have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    exact (div_left_inj' hs0).mp (by rw [hinner]; ring)
  have hsum := volterraOp_add_adj_boundaryL2 hΓLip hW g hθ
  have hO := localConformalVekuaForward_observationAdj_eq_cut hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E hE b hbn hbhalf hΓLip hW
  change observationAdj W (g : ℝ → ℂ) = (Complex.I * h0) • cutC (W (2 * Real.pi)) (basisVec 0) at hO
  have hS : cutS (W (2 * Real.pi)) (basisVec 0) =
      (2 : ℂ) • basisVec 0 + cutC (W (2 * Real.pi)) (basisVec 0) := by
    simp only [cutS, cutC]; rw [two_smul]; abel
  have hA : periodicA W (UR (E : ℂ) b 0) (g : ℝ → ℂ) θ =
      h0 * observation W (cutS (W (2 * Real.pi)) (basisVec 0)) θ := by
    rw [hO] at hsum; rw [periodicA, htr, hS]
    simp only [observation, map_add, map_smul, inner_add_right, inner_smul_right] at hsum ⊢
    linear_combination (-Complex.I) * hsum - Complex.I_sq *
      (h0 * ⟪basisVec 0, W θ (cutC (W (2 * Real.pi)) (basisVec 0))⟫_ℂ)
  rw [periodicP, hA, hO, map_smul,
    (cutB_transport (transport_mem_unitary hΓLip hW ⟨Real.two_pi_pos.le, le_rfl⟩) (basisVec 0) hc).2,
    smul_smul]
  simp only [observation, map_smul, inner_smul_right]
  linear_combination Complex.I_sq * (h0 * ⟪basisVec 0, W θ (cutS (W (2 * Real.pi)) (basisVec 0))⟫_ℂ)

private theorem localConformal_halfSmoothing_halfTrace (u : NeumannH1 ΩF) :
    sobolevSmoothing (1 / 2) (by norm_num) (QF u) = boundaryFourier (TF u) := by
  apply lp.ext; funext n
  simp only [sobolevSmoothing, diagOp_apply, localConformalDiskHalfTrace_apply]
  have hw : sobWeight n ^ (-(1 / 2 : ℝ)) * Real.sqrt (sobWeight n) = 1 := by
    rw [Real.sqrt_eq_rpow, mul_comm, sobWeight_rpow_mul_neg]
  change ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    ((Real.sqrt (sobWeight n) : ℂ) * boundaryFourier (TF u) n) = _
  rw [← mul_assoc, ← Complex.ofReal_mul, hw, Complex.ofReal_one, one_mul]

private def localConformalRegularPeriodicOperator (E₀ E : ℝ)
    {γ₀ : ℝ → ℂ} {L : NNReal} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hL₀ : LipschitzWith L γ₀) (hW : IsTransport γ₀ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  (2 : ℂ) • ((TF).comp ((h1RegularResolvent ΩF E₀ E).comp
    ((ContinuousLinearMap.adjoint QF).comp
      ((sobolevSmoothing (1 / 2) (by norm_num)).comp
        boundaryFourier.toLinearIsometry.toContinuousLinearMap)))) +
    sawtoothBoundaryOperator + regularCorrectedBoundaryOperator hL₀ hW hc

private theorem localConformalRegularPeriodicOperator_fourier (E₀ E : ℝ)
    {γ₀ : ℝ → ℂ} {L : NNReal} {Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2}
    (hL₀ : LipschitzWith L γ₀) (hW : IsTransport γ₀ E (Ws E))
    (hc : cutC (Ws E (2 * π)) (basisVec 0) ≠ 0)
    (hbase : Summable fun p => ‖correctedRemainderMatrix (Ws E) 0 0 p‖ ^ 2)
    (f : BoundaryL2) :
    boundaryFourier (localConformalRegularPeriodicOperator hR F hFs hL E₀ E hL₀ hW hc f) =
      sobolevSmoothing (1 / 2) (by norm_num)
        (normalizedPeriodicRegularFamily QF E₀ Ws E
          (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier f))) := by
  let S : L2Z →L[ℂ] L2Z := sobolevSmoothing (1 / 2) (by norm_num)
  let b : L2Z := S (boundaryFourier f)
  let u : NeumannH1 ΩF := h1RegularResolvent ΩF E₀ E (ContinuousLinearMap.adjoint QF b)
  have hr : Summable fun p => ‖kernelIntegralMatrix (r := correctedKernel (Ws E)) p‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun p => ?_) hbase
    have hweight := one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow (one_le_sobWeight p.1) (by norm_num : (0 : ℝ) ≤ 1 / 2))
      (Real.one_le_rpow (one_le_sobWeight p.2) (by norm_num : (0 : ℝ) ≤ 1 / 2))
    have heq : correctedRemainderMatrix (Ws E) 0 0 p =
        (((sobWeight p.1) ^ (1 / 2 : ℝ) * (sobWeight p.2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          kernelIntegralMatrix (r := correctedKernel (Ws E)) p := by
      simp only [correctedRemainderMatrix, kernelIntegralMatrix, sobWeight,
        mul_zero, add_zero, sub_zero, Complex.ofReal_mul]; push_cast; ring
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
  have hN : S (normalizedNeumannRegular QF E₀ E b) = boundaryFourier (TF u) :=
    localConformal_halfSmoothing_halfTrace hR F hFs hL u
  have hS : boundaryFourier (sawtoothBoundaryOperator f) =
      S (principalNormalized b) - (2 : ℂ) • S (normalizedInverseAbsOperator b) := by
    change boundaryFourier (boundaryFourier.symm (regularRawInverseDerivative (boundaryFourier f))) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    simp only [regularRawInverseDerivative, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, map_sub, map_smul]; rfl
  have hKern : boundaryFourier (regularCorrectedBoundaryOperator hL₀ hW hc f) =
      hsMatrixOp (kernelIntegralMatrix (r := correctedKernel (Ws E))) hr (boundaryFourier f) := by
    change (fourierBasis (T := 2 * π)).repr (boundaryCircleUnitary (boundaryCircleUnitary.symm
      (correctedKernelL2Op hL₀ hW hc (boundaryCircleUnitary f)))) = _
    rw [LinearIsometryEquiv.apply_symm_apply, correctedKernelL2Op_fourier_action hL₀ hW hc hr]; rfl
  have hHS : S (hsMatrixOp (correctedRemainderMatrix (Ws E) 0 0) hbase b) =
      hsMatrixOp (kernelIntegralMatrix (r := correctedKernel (Ws E))) hr (boundaryFourier f) :=
    correctedRemainderOp_half_smoothing (Ws E) hbase hr (boundaryFourier f)
  change boundaryFourier ((2 : ℂ) • TF u + sawtoothBoundaryOperator f +
    regularCorrectedBoundaryOperator hL₀ hW hc f) =
    S (normalizedPeriodicRegularFamily QF E₀ Ws E b)
  rw [map_add, map_add, map_smul, hS, hKern]
  simp only [normalizedPeriodicRegularFamily, correctedRemainderOperator_eq _ _ _ hbase,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    map_add, map_smul, map_sub, smul_sub, hN, hHS]
  abel

private theorem localConformalRegularPeriodicOperator_ae_periodicP (E₀ E : ℝ)
    {γ₀ : ℝ → ℂ} {L : NNReal} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hL₀ : LipschitzWith L γ₀) (hW : IsTransport γ₀ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)
    (g t : BoundaryL2)
    (ht : TF (h1RegularResolvent ΩF E₀ E (ContinuousLinearMap.adjoint QF
      (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g)))) = t) :
    (localConformalRegularPeriodicOperator hR F hFs hL E₀ E hL₀ hW hc g : ℝ → ℂ) =ᵐ[μB]
      periodicP W (t : ℝ → ℂ) (g : ℝ → ℂ) := by
  have hfI := (Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  let k : BoundaryL2 := (memLp_regularCorrectedAction hL₀ hW hfI).toLp _
  have hop_eq : localConformalRegularPeriodicOperator hR F hFs hL E₀ E hL₀ hW hc g =
      (2 : ℂ) • t + sawtoothBoundaryAction g + k := by
    change (2 : ℂ) • TF (h1RegularResolvent ΩF E₀ E (ContinuousLinearMap.adjoint QF
      (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g)))) +
      sawtoothBoundaryOperator g + regularCorrectedBoundaryOperator hL₀ hW hc g = _
    rw [ht, sawtoothBoundaryOperator_eq_action, regularCorrectedBoundaryOperator_eq_integral_L2 hL₀ hW hc g]
  rw [hop_eq]
  filter_upwards [Lp.coeFn_add ((2 : ℂ) • t + sawtoothBoundaryAction g) k,
    Lp.coeFn_add ((2 : ℂ) • t) (sawtoothBoundaryAction g), Lp.coeFn_smul (2 : ℂ) t,
    MemLp.coeFn_toLp (memLp_sawtoothAction hfI),
    MemLp.coeFn_toLp (memLp_regularCorrectedAction hL₀ hW hfI),
    ae_restrict_mem measurableSet_Ioc] with θ ha hb' hc' hs hk hθ
  simp only [ha, hb', hc', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  dsimp only [sawtoothBoundaryAction, k]
  rw [hs, hk]
  exact (periodicP_eq_kernel_integrals_boundaryL2 hL₀ hW _ g (Ioc_subset_Icc_self hθ)).symm

include hR hFs in
private theorem exists_physicalCircleTrace_deriv_lipschitz :
    ∃ B : NNReal, ∀ x ∈ Icc 0 (2 * Real.pi), ∀ y ∈ Icc 0 (2 * Real.pi),
      ‖deriv ΓF x - deriv ΓF y‖ ≤ B * |x - y| := by
  have hΓ2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) ΓF :=
    (contDiff_physicalCircleTrace_four_of_neighborhood hR F
      (hFs.of_le (WithTop.coe_le_coe.mpr le_top))).of_le (by norm_num)
  obtain ⟨B, hB⟩ := hΓ2.deriv'.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_Icc 0 (2 * Real.pi)) isCompact_Icc
  exact ⟨B, fun x hx y hy => by simpa [dist_eq_norm, Real.dist_eq] using hB.dist_le_mul x hx y hy⟩

include hR hFs in
private theorem localConformal_correctedRemainderMatrix_summable
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) :
    Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2 := by
  obtain ⟨B, hB⟩ := exists_physicalCircleTrace_deriv_lipschitz hR F hFs
  exact summable_correctedRemainderMatrix hΓLip hB hW hc
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

include hb hhol hinj hC hK e he hsource hes hγ hτ hcoord in
private theorem localConformalPeriodicBoundaryNull_comp_subtype
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0) :
    (normalizedPeriodicBoundaryFamily QF Ws E).comp
      ((NF (E : ℂ)).comp (H₀).subtypeL) = 0 := by
  apply ContinuousLinearMap.ext; intro b₀
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, Submodule.subtypeL_apply]
  refine clm_eq_zero_of_nonpositive_stdBasis
    ((normalizedPeriodicBoundaryFamily QF Ws E).comp (NF (E : ℂ)))
    (fun n hn => ?_) (b₀ : L2Z) b₀.property
  simp only [ContinuousLinearMap.comp_apply]
  let b := stdBasisZ n
  have hbn : IsNonpositiveFourierSupport b := fun k hk => by
    simp [b, stdBasisZ_apply, lp.single_apply, show k ≠ n by omega]
  have hbhalf := stdBasis_isSobolevSeq_half n
  have hunit := h1HelmholtzForm_isUnit hb hL hE hnr
  let g : BoundaryL2 := localConformalVekuaForwardLoad hR F hFs (E : ℂ) b hbhalf
  have hload := localConformalVekuaForwardLoad_normalized hR F hFs (E : ℂ) b hbhalf
  have hbase := localConformal_correctedRemainderMatrix_summable hR F hFs hΓLip hW hc
  have hVekua_eq : VF (F 1) (E : ℂ) b = normalizedNeumannPoisson QF E (NF (E : ℂ) b) :=
    h1HelmholtzForm_injective hb hL hE hnr <|
      ((isNormalizedNeumannSolution_iff QF E (NF (E : ℂ) b) _).mp fun w =>
        localConformalVekuaH1_normalizedConormal_weak_form hR F hFs hb hL hhol hinj hC hK
          e he hsource hes hγ hτ hcoord (E : ℂ) b hbn w).trans
        ((isNormalizedNeumannSolution_iff QF E (NF (E : ℂ) b) _).mp
          (normalizedNeumannPoisson_isSolution QF hunit _)).symm
  have htr_eq : TF (h1RegularResolvent ΩF E E (ContinuousLinearMap.adjoint QF
      (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g)))) = TF (VF (F 1) (E : ℂ) b) := by
    rw [hload]; apply boundaryFourier.injective
    rw [← localConformal_halfSmoothing_halfTrace hR F hFs hL,
      ← localConformal_halfSmoothing_halfTrace hR F hFs hL]
    change sobolevSmoothing (1 / 2) (by norm_num) (normalizedNeumannRegular QF E E (NF (E : ℂ) b)) = _
    rw [← normalizedNeumannBoundary_eq_regular_at_nonresonant_reference QF hb hL hE hunit]
    change sobolevSmoothing (1 / 2) (by norm_num) (QF (normalizedNeumannPoisson QF E (NF (E : ℂ) b))) = _
    rw [← hVekua_eq]
  have hop := localConformalRegularPeriodicOperator_ae_periodicP hR F hFs hL E E hΓLip hW hc
    g (TF (VF (F 1) (E : ℂ) b)) htr_eq
  have htrace := localConformalVekua_coordinate_trace_reconstruction_ae hR F hFs hb hL
    hhol hinj hC hK e he hsource hes (E : ℂ) b hbn
    (isSobolevSeq_one_fromL2_half_of_half_regular b hbhalf)
  have hz : localConformalRegularPeriodicOperator hR F hFs hL E E hΓLip hW hc g = 0 := Lp.ext <| by
    filter_upwards [hop, htrace, Lp.coeFn_zero ℂ 2 μB, ae_restrict_mem measurableSet_Ioc]
      with θ hp ht hzero hθ
    rw [hzero]
    have hnull := localConformalVekuaForward_periodicP_eq_zero hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E hE b hbn hbhalf hΓLip hW hc (Ioc_subset_Icc_self hθ)
    exact hp.trans (by
      simpa only [periodicP, periodicA, ht, g, localConformalVekuaTraceRow, pow_zero,
        ContinuousLinearMap.one_apply, Pi.zero_apply] using hnull)
  have hfour := localConformalRegularPeriodicOperator_fourier hR F hFs hL E E hΓLip hW hc hbase g
  rw [hload] at hfour
  apply regular_halfSmoothing_injective
  rw [show normalizedPeriodicBoundaryFamily QF Ws E = normalizedPeriodicRegularFamily QF E Ws E by
      simp only [normalizedPeriodicBoundaryFamily, normalizedPeriodicRegularFamily,
        normalizedNeumannBoundary_eq_regular_at_nonresonant_reference QF hb hL hE hunit],
    ← hfour, hz, map_zero, map_zero]

include hb hhol hinj hC hγ hτ hcoord in
private theorem normalizedPeriodicBoundaryFamily_herglotz_eq
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hunit : IsUnit (h1HelmholtzForm ΩF E))
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    normalizedPeriodicBoundaryFamily QF Ws E
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) =
      (Real.sqrt (2 * Real.pi) : ℂ) • ContinuousLinearMap.adjoint (projObsDual (Ws E))
        (regularHerglotzObservationVector (γ := ΓF) E (Ws E) ha) := by
  let g : BoundaryL2 := localConformalHerglotzCoordinateLoad F hΓLip ha (Real.sqrt E)
  let load : L2Z := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))
  have hload : sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier g) = load :=
    (localConformalHerglotzBoundaryLoad_eq_coordinateLoad F hγ hτ hcoord hΓLip ha (Real.sqrt E)).symm
  have hbase := localConformal_correctedRemainderMatrix_summable hR F hFs hΓLip hW hc
  have hres_eq : h1RegularResolvent ΩF E E (ContinuousLinearMap.adjoint QF load) =
      herglotzWaveH1 hb ha (Real.sqrt E) := by
    have hsol := (isNormalizedNeumannSolution_iff QF E _ _).mp
      (localConformalHerglotz_isNormalizedNeumannSolution hR F hFs hb hL hhol hinj
        hC hγ hτ hcoord hE ha)
    rw [← hsol, h1RegularResolvent_form_at_reference hb hL hE,
      Submodule.starProjection_orthogonal_val,
      h1Resonant_starProjection_eq_zero_of_form_isUnit hunit, sub_zero]
  have hop := localConformalRegularPeriodicOperator_ae_periodicP hR F hFs hL E E hΓLip hW hc
    g (TF (herglotzWaveH1 hb ha (Real.sqrt E))) (by rw [hload, hres_eq])
  have htrace : (TF (herglotzWaveH1 hb ha (Real.sqrt E)) : ℝ → ℂ) =ᵐ[μB]
      (fun θ => herglotzWave (Real.sqrt E) a (ΓF θ)) := by
    obtain ⟨f, hfu, hfγ⟩ := exists_smoothTraceTest_herglotz hb hL hγ ha (Real.sqrt E)
    rw [← hfu]
    filter_upwards [localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC f,
      ae_restrict_mem measurableSet_Ioc] with θ ht hθ
    rw [ht, hcoord, hfγ _ (hτ.mapsTo (Ioc_subset_Icc_self hθ))]
    simpa only [physicalCircleTrace, hcoord] using (herglotzWave_eq (Real.sqrt E) a (γ (τ θ))).symm
  have hgf : (g : ℝ → ℂ) =ᵐ[μB] herglotzConormal (Real.sqrt E) a ΓF :=
    (memLp_herglotzConormal ha (Real.sqrt E) hΓLip).coeFn_toLp
  have hclosed : ΓF (2 * π) = ΓF 0 := by simpa only [zero_add] using physicalCircleTrace_periodic F 0
  let zΓ := regularHerglotzObservationVector (γ := ΓF) E (Ws E) ha
  have hzΓ := regularHerglotzObservationVector_cutProj hΓLip hclosed hW hc ha
  have hop_eq : localConformalRegularPeriodicOperator hR F hFs hL E E hΓLip hW hc g =
      projectedObservationBoundary hΓLip hW zΓ := Lp.ext <| by
    filter_upwards [hop, htrace, projectedObservationBoundary_coe hΓLip hW zΓ,
      ae_restrict_mem measurableSet_Ioc] with θ hp htr ho hθ
    have hθc := Ioc_subset_Icc_self hθ
    have hv1 : volterraOp (Ws E) (g : ℝ → ℂ) θ =
        volterraOp (Ws E) (herglotzConormal (Real.sqrt E) a ΓF) θ := by
      rw [volterraOp, volterraOp, intervalIntegral.integral_of_le hθc.1, intervalIntegral.integral_of_le hθc.1]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right hθc.2) hgf] with s hs
      rw [hs]
    have hv2 : volterraOpAdj (Ws E) (g : ℝ → ℂ) θ =
        volterraOpAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF) θ := by
      rw [volterraOpAdj, volterraOpAdj, intervalIntegral.integral_of_le hθc.2, intervalIntegral.integral_of_le hθc.2]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_left hθc.1) hgf] with s hs
      rw [hs]
    have hob : observationAdj (Ws E) (g : ℝ → ℂ) =
        observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF) := by
      rw [observationAdj, observationAdj, intervalIntegral.integral_of_le two_pi_pos.le,
        intervalIntegral.integral_of_le two_pi_pos.le]
      refine integral_congr_ae ?_; filter_upwards [hgf] with s hs; rw [hs]
    rw [hp, ho, ← observation_cutProj_eq, hzΓ,
      ← periodicP_herglotz_eq_regularObservation hΓLip hclosed hW ha hθc]
    simp only [periodicP, periodicA, htr, hv1, hv2, hob]
  have hfour := localConformalRegularPeriodicOperator_fourier hR F hFs hL E E hΓLip hW hc hbase g
  rw [hload, hop_eq, ← halfSmoothing_adjoint_projObsDual hΓLip hW zΓ] at hfour
  apply regular_halfSmoothing_injective
  rw [show normalizedPeriodicBoundaryFamily QF Ws E = normalizedPeriodicRegularFamily QF E Ws E by
      simp only [normalizedPeriodicBoundaryFamily, normalizedPeriodicRegularFamily,
        normalizedNeumannBoundary_eq_regular_at_nonresonant_reference QF hb hL hE hunit],
    ← hfour]

include hR hFs hb hL hhol hinj hC hK e he hsource hes hγ hτ hcoord in
private theorem exists_localConformal_reduced_bound
    {L : NNReal} (hΓLip : LipschitzWith L ΓF)
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) (hWs : ∀ E, IsTransport ΓF E (Ws E))
    {E₀ : ℝ} (hE₀ : 0 < E₀)
    (hcut : cutC (Ws E₀ (2 * Real.pi)) (basisVec 0) ≠ 0) :
    ∃ A₀ δ₀ : ℝ, 0 < A₀ ∧ 0 < δ₀ ∧ ∀ E, 0 < E → |E - E₀| < δ₀ →
      (∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) →
      ∃ ℓ : L2Z →ₗ[ℂ] (Fin (originalNeumannMultiplicity ΩF E₀) → ℂ),
        ∀ y : L2Z, ℓ y = 0 →
          -(A₀ * ‖projObsDual (Ws E) y‖ ^ 2) ≤
            (⟪y, normalizedPeriodicBoundaryFamily QF Ws E y⟫_ℂ).re := by
  obtain ⟨d, u, v, hinjS, Vchart, hVchart, hchart⟩ :=
    exists_localConformal_fixed_fourier_complement_projectedObservation_injective
      hR F hFs hb hL hhol hinj hC hK e he hsource hes hΓLip hE₀ (hWs E₀) hcut
  let T : H₀ᗮ →L[ℂ] L2Z := finiteFourierChart u v
  let J : ℝ → H₀ →L[ℂ] L2Z := fun E => (NF (E : ℂ)).comp (H₀).subtypeL
  let P : ℝ → L2Z →L[ℂ] L2Z := normalizedPeriodicBoundaryFamily QF Ws
  let Preg : ℝ → L2Z →L[ℂ] L2Z := normalizedPeriodicRegularFamily QF E₀ Ws
  let S : ℝ → L2Z →L[ℂ] Ell2 := fun E => projObsDual (Ws E)
  let w : Fin (originalNeumannMultiplicity ΩF E₀) → L2Z :=
    fun j => (Real.sqrt (E₀ + 1) : ℂ) • QF (originalNeumannResonanceH1Basis hb hL hE₀.le j)
  obtain ⟨Vcomp, hVcomp, hcomp, _⟩ := h1ComplementForm_isUnit_near hb hL hE₀.le
  have hcutCont : ContinuousAt (fun E => cutC (Ws E (2 * Real.pi)) (basisVec 0)) E₀ :=
    (((continuous_eval_const (basisVec 0)).tendsto _).comp
      (((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := Ell2) (F := Ell2)).continuous.tendsto _).comp
        (tendsto_transport_energy hΓLip hWs E₀ ⟨Real.two_pi_pos.le, le_rfl⟩))).sub tendsto_const_nhds
  let Vbase : Set ℝ := Vchart ∩ Vcomp ∩ {E | cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0}
  have hVbase : Vbase ∈ 𝓝 E₀ := inter_mem (inter_mem hVchart hVcomp) (hcutCont.eventually_ne hcut)
  let U : Set ℝ := {E | E ∈ Vbase ∧ 0 < E ∧ ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E}
  have hbase (E : ℝ) (hcE : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0) :
      Summable fun p => ‖correctedRemainderMatrix (Ws E) 0 0 p‖ ^ 2 :=
    localConformal_correctedRemainderMatrix_summable hR F hFs hΓLip (hWs E) hcE
  have hpole : ∀ E ∈ U, P E = ((-2 / (E - E₀) : ℝ) : ℂ) •
      ∑ j, InnerProductSpace.rankOne ℂ (w j) (w j) + Preg E := fun E hEU => by
    change normalizedPeriodicBoundaryFamily QF Ws E = _
    rw [normalizedPeriodicBoundaryFamily_eq_pole_add_regular QF hb hL Ws hE₀.le
      (h1HelmholtzForm_isUnit hb hL hEU.2.1.le hEU.2.2) (hcomp E hEU.1.1.2),
      normalizedNeumannResidue_eq_sum_rankOne QF hE₀.le (originalNeumannResonanceH1Basis hb hL hE₀.le)]
  obtain ⟨B', hB'⟩ := exists_physicalCircleTrace_deriv_lipschitz hR F hFs
  have hu₀ := h1ComplementForm_isUnit hb hL hE₀.le
  have hPreg : ContinuousAt Preg E₀ :=
    continuousAt_normalizedPeriodicRegularFamily QF hu₀ hΓLip hB' hWs hcut
  have hbase₀ := hbase E₀ hcut
  let P₀ := Preg E₀
  have hP₀_comp : IsCompactOperator (P₀ - (4 : ℂ) • posProj) := by
    have hdiff : IsCompactOperator (normalizedNeumannRegular QF E₀ E₀ - normalizedInverseAbsOperator) := by
      rw [show normalizedNeumannRegular QF E₀ E₀ - normalizedInverseAbsOperator =
        (normalizedNeumannRegular QF E₀ E₀ - 1) - (normalizedInverseAbsOperator - 1) by abel]
      exact (isCompactOperator_localConformal_normalizedNeumannRegular_sub_one
        hR F hFs hb hL hhol hinj hC e he hsource hes hE₀.le hu₀).sub
        isCompactOperator_normalizedInverseAbsOperator_sub_one
    rw [show P₀ - (4 : ℂ) • posProj =
      (2 : ℂ) • (normalizedNeumannRegular QF E₀ E₀ - normalizedInverseAbsOperator) +
        (principalNormalized - (4 : ℂ) • posProj) +
          hsMatrixOp (correctedRemainderMatrix (Ws E₀) 0 0) hbase₀ by
      dsimp only [P₀, Preg, normalizedPeriodicRegularFamily]
      rw [correctedRemainderOperator_eq _ _ _ hbase₀]; abel]
    exact ((hdiff.smul (2 : ℂ)).add principal_normalized_sub_four_posProj_compact).add
      (isCompactOperator_hsMatrixOp _ hbase₀)
  let D := adjoint T ∘L P₀ ∘L T - (4 : ℂ) • ContinuousLinearMap.id ℂ H₁
  have hD : IsCompactOperator D := finiteFourierChart_regular_compression_sub_four_compact u v P₀ hP₀_comp
  have hnullS : ∀ E ∈ U, S E ∘L J E = 0 := fun E hEU => ContinuousLinearMap.ext fun b₀ => by
    simp only [S, J, ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, Submodule.subtypeL_apply]
    refine clm_eq_zero_of_nonpositive_stdBasis ((projObsDual (Ws E)).comp (NF (E : ℂ)))
      (fun n hn => ?_) (b₀ : L2Z) b₀.property
    simp only [ContinuousLinearMap.comp_apply]
    have hstd_np : IsNonpositiveFourierSupport (stdBasisZ n) := fun k hk => by
      simp [stdBasisZ_apply, lp.single_apply, show k ≠ n by omega]
    have h := projObsDual_boundary_normalized hΓLip (hWs E)
      (localConformalVekuaForwardLoad hR F hFs (E : ℂ) (stdBasisZ n) (stdBasis_isSobolevSeq_half n))
    rw [localConformalVekuaForwardLoad_normalized, map_smul,
      localConformalVekuaForward_observationAdj_eq_cut hR F hFs hb hL hhol hinj hC hK
        e he hsource hes E hEU.2.1.le (stdBasisZ n) hstd_np (stdBasis_isSobolevSeq_half n) hΓLip (hWs E),
      map_smul, cutProj_eq_starProjection,
      Submodule.starProjection_orthogonal_apply_eq_zero (Submodule.mem_span_singleton_self _),
      smul_zero] at h
    exact (smul_eq_zero.mp h).resolve_left (by exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne')
  obtain ⟨A₀, hA₀, V, hV, hred⟩ := chart_reduced_boundary_bound_on_energy_set H₀ J T E₀ U
    (fun E hEU => hchart E hEU.1.1.1) P Preg S w
    (fun E hEU => normalizedPeriodicBoundaryFamily_isSelfAdjoint QF Ws hΓLip (hWs E) (hbase E hEU.1.2))
    (fun E hEU => localConformalPeriodicBoundaryNull_comp_subtype hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγ hτ hcoord Ws hEU.2.1.le hEU.2.2 hΓLip (hWs E) hEU.1.2)
    hnullS hpole hPreg (tendsto_projObsDual_energy hΓLip hWs E₀ hcut) 4 (by norm_num) D hD
    (by dsimp only [D, P₀]; push_cast; abel) (fun z _ hz => hinjS (by simpa using hz))
  obtain ⟨δ₀, hδ₀, hδsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hV hVbase)
  refine ⟨A₀, δ₀, hA₀, hδ₀, fun E hE hnear hnr => ?_⟩
  obtain ⟨hEV, hEbase⟩ := hδsub (mem_ball.mpr (by simpa only [Real.dist_eq] using hnear))
  exact hred E hEV ⟨hEbase, hE, hnr⟩

include hR hFs hb hL hhol hinj hC hK e he hsource hes hγ hτ hcoord in
theorem exists_localConformal_herglotz_bound
    {L : NNReal} (hΓLip : LipschitzWith L ΓF)
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) (hWs : ∀ E, IsTransport ΓF E (Ws E))
    {E₀ : ℝ} (hE₀ : 0 < E₀)
    (hcut : cutC (Ws E₀ (2 * Real.pi)) (basisVec 0) ≠ 0) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) →
      ∀ Wγ : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E Wγ →
        ∃ Lf : (ℝ → ℂ) →ₗ[ℂ] (Fin (originalNeumannMultiplicity ΩF E₀) → ℂ),
          ∀ a, IsDirDensity a → Lf a = 0 →
            -(A * ‖observationAdj Wγ (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
              herglotzForm Wγ γ E a := by
  obtain ⟨A₀, δ₀, hA₀, hδ₀, hnormalized⟩ := exists_localConformal_reduced_bound
    hR F hFs hb hL hhol hinj hC hK e he hsource hes hγ hτ hcoord hΓLip Ws hWs hE₀ hcut
  have hBcut : ∀ᶠ E in 𝓝 E₀, ‖cutBE (Ws E)‖ ≤ ‖cutBE (Ws E₀)‖ + 1 :=
    ((tendsto_cutBE_energy hΓLip hWs E₀ hcut).norm.eventually
      (gt_mem_nhds (by linarith : ‖cutBE (Ws E₀)‖ < ‖cutBE (Ws E₀)‖ + 1))).mono fun _ h => h.le
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp
    ((eventually_cutC_ne hΓLip hWs E₀ hcut).and hBcut)
  set B := ‖cutBE (Ws E₀)‖ + 1
  refine ⟨A₀ / (2 * Real.pi) + B, min δ₀ ρ, add_pos (div_pos hA₀ Real.two_pi_pos) (by positivity),
    lt_min hδ₀ hρ, fun E hE hnear hnr Wγ hWγ => ?_⟩
  obtain ⟨hcE, hBE⟩ := hρsub (mem_ball.mpr (by
    simpa only [Real.dist_eq] using hnear.trans_le (min_le_right _ _)))
  obtain ⟨ℓ, hℓ⟩ := hnormalized E hE (hnear.trans_le (min_le_left _ _)) hnr
  obtain ⟨Lf, hLf⟩ := LinearMap.exists_extend (ℓ.comp (localConformalHerglotzBoundaryLin hγ hτ (Real.sqrt E)))
  refine ⟨Lf, fun a ha hLa => ?_⟩
  have hb0 : ℓ (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) = 0 :=
    (congrArg (fun M => M ⟨a, ha⟩) hLf).symm.trans hLa
  have hbd := hℓ _ hb0
  have hobs : (Real.sqrt (2 * Real.pi) : ℂ) • projObsDual (Ws E)
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) =
      cutProj (cutC (Ws E (2 * Real.pi)) (basisVec 0))
        (observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)) := by
    rw [localConformalHerglotzBoundaryLoad_eq_coordinateLoad F hγ hτ hcoord hΓLip ha, ← map_smul]
    have h := projObsDual_boundary_normalized hΓLip (hWs E)
      (localConformalHerglotzCoordinateLoad F hΓLip ha (Real.sqrt E))
    have hae : observationAdj (Ws E) (localConformalHerglotzCoordinateLoad F hΓLip ha (Real.sqrt E)) =
        observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF) := by
      rw [observationAdj, observationAdj, intervalIntegral.integral_of_le Real.two_pi_pos.le,
        intervalIntegral.integral_of_le Real.two_pi_pos.le]
      refine integral_congr_ae ?_
      filter_upwards [(memLp_herglotzConormal ha (Real.sqrt E) hΓLip).coeFn_toLp] with θ hθ
      exact congrArg (fun v : ℂ => v • _) hθ
    rwa [hae] at h
  have hn' : ‖projObsDual (Ws E)
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))‖ ^ 2 =
      ‖cutProj (cutC (Ws E (2 * Real.pi)) (basisVec 0))
        (observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF))‖ ^ 2 / (2 * Real.pi) := by
    refine (eq_div_iff Real.two_pi_pos.ne').mpr ?_
    have hn := congrArg (fun v : Ell2 => ‖v‖ ^ 2) hobs
    rw [norm_smul, Complex.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt Real.two_pi_pos.le] at hn
    linarith
  have hunitE := h1HelmholtzForm_isUnit hb hL hE.le hnr
  have hclosedΓ : ΓF (2 * Real.pi) = ΓF 0 := by simpa only [zero_add] using physicalCircleTrace_periodic F 0
  have hinner : ⟪localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)),
      normalizedPeriodicBoundaryFamily QF Ws E
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))⟫_ℂ =
      l2Inner (herglotzConormal (Real.sqrt E) a ΓF)
        (periodicP (Ws E) (fun θ => herglotzWave (Real.sqrt E) a (ΓF θ))
          (herglotzConormal (Real.sqrt E) a ΓF)) := by
    rw [normalizedPeriodicBoundaryFamily_herglotz_eq hR F hFs hb hL hhol hinj hC
        hγ hτ hcoord Ws hE.le hunitE hΓLip (hWs E) hcE ha,
      inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
      ← Complex.conj_ofReal (Real.sqrt (2 * Real.pi)), ← inner_smul_left, hobs,
      inner_cutProj_left, regularHerglotzObservationVector_cutProj hΓLip hclosedΓ (hWs E) hcE ha]
    obtain ⟨hgm, _, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hΓLip
    rw [inner_observationAdj (hWs E).1 hgm hgB, l2Inner]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le Real.two_pi_pos.le] at hθ
    change conj _ * observation (Ws E) _ θ = conj _ * periodicP (Ws E) _ _ θ
    rw [periodicP_herglotz_eq_regularObservation hΓLip hclosedΓ (hWs E) ha hθ]
  rw [hn', hinner] at hbd
  have hΓform := herglotzForm_lower_of_periodicP_lower hΓLip hclosedΓ (hWs E) ha
    (div_nonneg hA₀.le Real.two_pi_pos.le) (by convert hbd using 1; ring)
  have hΓbd : -((A₀ / (2 * Real.pi) + B) *
      ‖observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)‖ ^ 2) ≤
      herglotzForm (Ws E) ΓF E a := by
    nlinarith [mul_le_mul_of_nonneg_right hBE
      (sq_nonneg ‖observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)‖)]
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨Kτ, hKτ⟩ := hτ.lipschitz
  have hΓeq : ΓF = γ ∘ τ := funext hcoord
  have hclosedγ : γ (2 * Real.pi) = γ 0 := by simpa only [zero_add] using hγ.periodic 0
  have hWcomp : IsTransport (γ ∘ τ) E (Ws E) := hΓeq ▸ hWs E
  have hU := monodromy_comp hKγ hτ.monotone hKτ hτ.zero hτ.endpoint hWγ hWcomp
  have hclosed_comp : (γ ∘ τ) (2 * Real.pi) = (γ ∘ τ) 0 := by
    change γ (τ (2 * Real.pi)) = γ (τ 0); rw [hτ.endpoint, hτ.zero, hclosedγ]
  have hobs_eq : observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF) =
      observationAdj Wγ (herglotzConormal (Real.sqrt E) a γ) := by
    rw [hΓeq, (herglotzForm_eq (hKγ.comp hKτ) hclosed_comp hWcomp ha).1,
      (herglotzForm_eq hKγ hclosedγ hWγ ha).1]
    change ((Real.sqrt 2 : ℂ) * Complex.I) • (monodromy (Ws E) - 1)
        (herglotzVec ha (Real.sqrt E) ((γ ∘ τ) 0)) =
      ((Real.sqrt 2 : ℂ) * Complex.I) • (monodromy Wγ - 1)
        (herglotzVec ha (Real.sqrt E) (γ 0))
    simp only [Function.comp_apply, hτ.zero, hU]
  have hform_eq : herglotzForm (Ws E) ΓF E a = herglotzForm Wγ γ E a := by
    rw [hΓeq, herglotzForm_eq_im (hKγ.comp hKτ) hclosed_comp hWcomp ha,
      herglotzForm_eq_im hKγ hclosedγ hWγ ha]
    simp only [Function.comp_apply, hτ.zero, hU]
  rwa [hobs_eq, hform_eq] at hΓbd

end SuppliedCoordinates

end PolyaNeumann
end
