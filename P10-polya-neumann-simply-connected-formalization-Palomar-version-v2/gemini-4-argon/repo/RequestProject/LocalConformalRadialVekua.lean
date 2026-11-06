module

public import RequestProject.PhysicalDrivenKernelConormal
public import RequestProject.NeumannHerglotzBoundary
public import RequestProject.HerglotzReduction
public import RequestProject.LocalConformalBoundaryGeometry
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The actual full zero-mode Vekua vector is the centered radial wave

The input sqrt(2pi) times the zero Fourier basis vector represents the
ordinary Hardy constant one. Its genuine primitive iterates are identified
with compact smooth restrictions of conj(z-p)^j/j!, using actual CR trace
uniqueness. The genuine H1 series then has the same L2 limit as the actual
centered Herglotz wave. The center is the boundary origin p=F(1).

This radial construction does not turn arbitrary normalized H^(-1/2)
conormal data into L2 boundary data.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped Topology ComplexConjugate InnerProductSpace ContDiff


variable {E : ℝ} {Ω : Set ℂ} {L : NNReal}

/-- Normalized half-trace input for the actual ordinary Hardy constant one. -/
def radialVekuaInput : L2Z := (Real.sqrt (2 * Real.pi) : ℂ) • stdBasisZ 0

theorem radialVekuaInput_apply n :
    radialVekuaInput n = if n = 0 then (Real.sqrt (2 * Real.pi) : ℂ) else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [radialVekuaInput, stdBasisZ_apply]
  · simp [radialVekuaInput, stdBasisZ_apply, hn]

theorem radialVekuaInput_nonpositive : IsNonpositiveFourierSupport radialVekuaInput := by
  intro n hn
  rw [radialVekuaInput_apply, if_neg (ne_of_gt hn)]

theorem normalizedHardyAverage_radialVekuaInput n :
    normalizedHardyAverage radialVekuaInput n = if n = 0 then 1 else 0 := by
  have hc : Real.sqrt (2 * Real.pi) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne'
  by_cases hn : n = 0
  · subst n
    simp [normalizedHardyAverage, fromL2, radialVekuaInput_apply, sobWeight]
    field_simp [(by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'), (by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne')]
  · simp [normalizedHardyAverage, fromL2, radialVekuaInput_apply, hn]

theorem radialVekuaInput_raw_H1 : IsSobolevSeq 1 (fromL2 (1 / 2) radialVekuaInput) := by
  classical
  unfold IsSobolevSeq
  refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
  simp [fromL2, radialVekuaInput_apply, show n ≠ 0 by simpa using hn]

theorem hardyFourierTrace_radialVekuaInput (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage radialVekuaInput) θ = 1 := by
  classical
  simp only [hardyFourierTrace, normalizedHardyAverage_radialVekuaInput]
  simp

private def radialPrimitivePolynomial (p : ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  conj (z - p) ^ j / (j.factorial : ℂ)

private theorem radialPrimitivePolynomial_contDiff p j :
    ContDiff ℝ ∞ (radialPrimitivePolynomial p j) :=
  ((Complex.conjCLE.contDiff.comp (contDiff_id.sub contDiff_const)).pow j).div_const _

private theorem radialPrimitivePolynomial_fderiv p j z v :
    fderiv ℝ (radialPrimitivePolynomial p j) z v =
      (j : ℂ) * conj (z - p) ^ (j - 1) * conj v / (j.factorial : ℂ) := by
  have hc := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := z - p)).comp z ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const p)
  change fderiv ℝ (fun y => conj (y - p) ^ j / j.factorial) z v = _
  simpa [radialPrimitivePolynomial, div_eq_mul_inv, Complex.conjCLE_apply, mul_comm, mul_left_comm, mul_assoc]
    using congrArg (fun A : ℂ →L[ℝ] ℂ => A v) ((hc.pow j).mul_const j.factorial⁻¹).fderiv

private theorem exists_radialPrimitiveTest  (hb : Bornology.IsBounded Ω)
    p j : ∃ f : smoothTraceTests,
      ∀ z ∈ closure Ω, (f : ℂ → ℂ) =ᶠ[𝓝 z] radialPrimitivePolynomial p j := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_compact_extension hb.isCompact_closure
    isOpen_univ (subset_univ _) (radialPrimitivePolynomial_contDiff p j).contDiffOn
  exact ⟨⟨f, hf⟩, heq⟩

private def radialPrimitiveTest  (hb : Bornology.IsBounded Ω)
    (p : ℂ) (j : ℕ) : smoothTraceTests :=
  Classical.choose (exists_radialPrimitiveTest hb p j)

private theorem radialPrimitiveTest_near  (hb : Bornology.IsBounded Ω)
    p j  (hz : z ∈ closure Ω) :
    (radialPrimitiveTest hb p j : ℂ → ℂ) =ᶠ[𝓝 z] radialPrimitivePolynomial p j :=
  Classical.choose_spec (exists_radialPrimitiveTest hb p j) z hz

private theorem radialPrimitiveTest_value_ae  (hb : Bornology.IsBounded Ω)
    (hΩ : IsOpen Ω) p j :
    (h1Value Ω (smoothTraceH1 Ω (radialPrimitiveTest hb p j)) : ℂ → ℂ)
      =ᵐ[volume.restrict Ω] radialPrimitivePolynomial p j := by
  rw [h1Value_smoothTraceH1]
  filter_upwards [(smoothTraceTests_memLp Ω (radialPrimitiveTest hb p j)).coeFn_toLp,
    ae_restrict_mem hΩ.measurableSet] with z hz hmem
  exact hz.trans (radialPrimitiveTest_near hb p j (subset_closure hmem)).self_of_nhds

private theorem radialPrimitiveTest_cauchyRiemann 
    (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) p j :
    h1Gradient Ω 0 (smoothTraceH1 Ω (radialPrimitiveTest hb p j)) =
      Complex.I • h1Gradient Ω 1 (smoothTraceH1 Ω (radialPrimitiveTest hb p j)) := by
  apply Lp.ext
  rw [h1Gradient_smoothTraceH1, h1Gradient_smoothTraceH1]
  filter_upwards [(smoothTraceTests_memLp_deriv Ω (radialPrimitiveTest hb p j) 0).coeFn_toLp,
    (smoothTraceTests_memLp_deriv Ω (radialPrimitiveTest hb p j) 1).coeFn_toLp,
    Lp.coeFn_smul Complex.I
      ((smoothTraceTests_memLp_deriv Ω (radialPrimitiveTest hb p j) 1).toLp _),
    ae_restrict_mem hΩ.measurableSet] with z hx hy hs hz
  calc
    _ = fderiv ℝ (radialPrimitiveTest hb p j) z (coordDir 0) := hx
    _ = Complex.I * fderiv ℝ (radialPrimitiveTest hb p j) z (coordDir 1) := by
      rw [(radialPrimitiveTest_near hb p j (subset_closure hz)).fderiv_eq]
      simp only [radialPrimitivePolynomial_fderiv,
        show coordDir 0 = 1 from rfl,
        show coordDir 1 = Complex.I from rfl, map_one, Complex.conj_I, mul_one]
      simp only [div_eq_mul_inv]
      calc
        _ = Complex.I * (-Complex.I) *
            (↑j * (starRingEnd ℂ) (z - p) ^ (j - 1) * (↑j.factorial)⁻¹) := by
          rw [show Complex.I * (-Complex.I) = 1 by
            rw [mul_neg, Complex.I_mul_I, neg_neg], one_mul]
        _ = _ := by ring
    _ = Complex.I * ((((smoothTraceTests_memLp_deriv Ω
        (radialPrimitiveTest hb p j) 1).toLp _ : L2 Ω) : ℂ → ℂ) z) := by rw [hy]
    _ = _ := by simpa using hs.symm

private theorem radial_volterra_primitive_polynomial
     (hγ : ContDiff ℝ 1 γ) j θ :
    volterraPrimitiveIterate (fun s => conj (deriv γ s)) (fun _ => 1) j θ =
      conj (γ θ - γ 0) ^ j / (j.factorial : ℂ) := by
  induction j generalizing θ with
  | zero => simp [volterraPrimitiveIterate]
  | succ j ih =>
    have hd s : HasDerivAt
        (fun t => conj (γ t - γ 0) ^ (j + 1) / ((j + 1).factorial))
        (conj (deriv γ s) * (conj (γ s - γ 0) ^ j / j.factorial)) s := by
      convert ((show HasDerivAt (fun t => conj (γ t - γ 0)) (conj (deriv γ s)) s by
        simpa using
          ((hγ.differentiable_one s).hasDerivAt.sub_const (γ 0)).star).pow (j + 1)).div_const ((j + 1).factorial) using 1
      simp [Nat.factorial_succ]
      field_simp [(by exact_mod_cast j.factorial_ne_zero), (by exact_mod_cast Nat.succ_ne_zero j)]
    change (∫ s in 0..θ, conj (deriv γ s) *
      volterraPrimitiveIterate (fun t => conj (deriv γ t)) (fun _ => 1) j s) = _
    rw [show (fun s => conj (deriv γ s) *
        volterraPrimitiveIterate (fun t => conj (deriv γ t)) (fun _ => 1) j s) =
        (fun s => conj (deriv γ s) * (conj (γ s - γ 0) ^ j / j.factorial)) by
          funext s; rw [ih s]]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (((Complex.continuous_conj.comp hγ.continuous_deriv_one).mul (((Complex.continuous_conj.comp (hγ.continuous.sub continuous_const)).pow j).div_const _)).intervalIntegrable _ _)]
    simp

private theorem radial_Lp_series_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (u : ℕ → Lp ℂ 2 μ) v
    (f : ℕ → α → ℂ) g (hs : HasSum u v)
    (hf : ∀ j, (u j : α → ℂ) =ᵐ[μ] f j)
    (hfm : ∀ j, AEStronglyMeasurable (f j) μ)
    (hpt : ∀ x, HasSum (fun j => f j x) (g x)) : (v : α → ℂ) =ᵐ[μ] g := by
  classical
  have heq s : (∑ j ∈ s, u j : Lp ℂ 2 μ)
      =ᵐ[μ] fun x => ∑ j ∈ s, f j x := by
    induction s using Finset.induction_on with
    | empty => simpa [Pi.zero_def] using Lp.coeFn_zero ℂ 2 μ
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (u a) (∑ j ∈ s, u j), hf a, ih] with x hsum hfa his
      simp only [Pi.add_apply] at hsum
      rw [hsum, hfa, his]
  have hlim :=
    tendstoInMeasure_of_tendsto_ae
      (fun N => by
        rw [← (show (∑ j ∈ Finset.range N, f j) = (fun x => ∑ j ∈ Finset.range N, f j x) by
          funext x
          simp)]
        exact Finset.aestronglyMeasurable_sum (Finset.range N) fun j _ => hfm j)
      (Eventually.of_forall fun x => (hpt x).tendsto_sum_nat)
  exact tendstoInMeasure_ae_unique ((tendstoInMeasure_of_tendsto_Lp hs.tendsto_sum_nat).congr (fun N => heq _) EventuallyEq.rfl) hlim

/-- Genuine centered radial Herglotz density, with ordinary value one at p. -/
def radialVekuaDensity (k : ℝ) (p : ℂ) : ℝ → ℂ :=
  centeredPolyDensity k p {0} (fun _ => 1)

theorem isDirDensity_radialVekuaDensity k p :
    IsDirDensity (radialVekuaDensity k p) :=
  isDirDensity_centeredPolyDensity k p {0} (fun _ => 1)

/-- Actual centered radial density with the indicated ordinary amplitude. -/
def radialVekuaScaledDensity (k : ℝ) (p a : ℂ) : ℝ → ℂ :=
  centeredPolyDensity k p {0} (fun _ => a)

theorem isDirDensity_radialVekuaScaledDensity k p a :
    IsDirDensity (radialVekuaScaledDensity k p a) :=
  isDirDensity_centeredPolyDensity k p {0} (fun _ => a)

theorem radialVekuaScaledDensity_eq_smul k p a :
    radialVekuaScaledDensity k p a = a • radialVekuaDensity k p := by
  funext φ
  simp [radialVekuaScaledDensity, radialVekuaDensity, centeredPolyDensity, polyDensity]
  ; ring

theorem radialVekuaScaledDensity_one k p :
    radialVekuaScaledDensity k p 1 = radialVekuaDensity k p := rfl

private theorem radial_boundaryFourier_ae  (v : BoundaryL2)
    (hv : v =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] f) n :
    boundaryFourier v n = (Real.sqrt (2 * Real.pi) : ℂ) *
      fourierCoeffOn Real.two_pi_pos f n := by
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hv]

private theorem radial_herglotzWaveH1_smul 
    (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) {a : ℝ → ℂ}
    (ha : IsDirDensity a) (c : ℂ) (k : ℝ) :
    herglotzWaveH1 hb (ha.const_smul c) k = c • herglotzWaveH1 hb ha k := by
  apply h1Value_injective hΩ
  rw [map_smul, h1Value_herglotzWaveH1, h1Value_herglotzWaveH1]
  apply Lp.ext
  filter_upwards [(herglotzCoeff_memLp_domain hb (ha.const_smul c) k 0).coeFn_toLp,
    (herglotzCoeff_memLp_domain hb ha k 0).coeFn_toLp,
    Lp.coeFn_smul c ((herglotzCoeff_memLp_domain hb ha k 0).toLp _)] with z hc hcoeff hs
  calc
    _ = _ := hc
    _ = _ := herglotzCoeff_smul_density a c k 0 z
    _ = c * ((herglotzCoeff_memLp_domain hb ha k 0).toLp _ : L2 Ω) z := by
      rw [hcoeff]
    _ = c • (((herglotzCoeff_memLp_domain hb ha k 0).toLp _ : L2 Ω) z) := by
      rfl
     _ = _ := by
       simpa using hs.symm

private theorem exists_radialWaveTest  (hb : Bornology.IsBounded Ω)
    (hΩ : IsOpen Ω) {a : ℝ → ℂ} (ha : IsDirDensity a) k :
    ∃ f : smoothTraceTests, smoothTraceH1 Ω f = herglotzWaveH1 hb ha k ∧
      ∀ z ∈ closure Ω, f z = herglotzCoeff k a 0 z := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_compact_extension hb.isCompact_closure
    isOpen_univ (subset_univ _) (contDiff_herglotzCoeff_infty ha.intervalIntegrable k 0).contDiffOn
  let ff : smoothTraceTests := ⟨f, hf⟩
  have hval : ∀ z ∈ closure Ω, ff z = herglotzCoeff k a 0 z :=
    fun z hz => (heq z hz).self_of_nhds
  refine ⟨ff, ?_, hval⟩
  apply h1Value_injective hΩ
  rw [h1Value_smoothTraceH1, h1Value_herglotzWaveH1]
  apply MemLp.toLp_congr
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
  exact hval z (subset_closure hz)

private theorem exists_radialCoeffTest  (hb : Bornology.IsBounded Ω)
     (ha : IsDirDensity a) k m :
    ∃ f : smoothTraceTests, ∀ z ∈ closure Ω, f z = herglotzCoeff k a m z := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_compact_extension hb.isCompact_closure
    isOpen_univ (subset_univ _) (contDiff_herglotzCoeff_infty ha.intervalIntegrable k m).contDiffOn
  exact ⟨⟨f, hf⟩, fun z hz => (heq z hz).self_of_nhds⟩

private theorem radial_herglotzWirtingerD_ae 
    (hb : Bornology.IsBounded Ω) {a : ℝ → ℂ} (ha : IsDirDensity a) k :
    (h1WirtingerD Ω (herglotzWaveH1 hb ha k) : ℂ → ℂ)
      =ᵐ[volume.restrict Ω] fun z => -(Complex.I * k / 2) * herglotzCoeff k a 1 z := by
  let x := (herglotzCoeff_memLp_deriv_domain hb ha k 0 0).toLp
    (fun z => fderiv ℝ (herglotzCoeff k a 0) z (coordDir 0))
  let y := (herglotzCoeff_memLp_deriv_domain hb ha k 0 1).toLp
    (fun z => fderiv ℝ (herglotzCoeff k a 0) z (coordDir 1))
  rw [h1WirtingerD_apply, h1Gradient_herglotzWaveH1, h1Gradient_herglotzWaveH1]
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (x - Complex.I • y),
    Lp.coeFn_sub x (Complex.I • y), Lp.coeFn_smul Complex.I y,
    (herglotzCoeff_memLp_deriv_domain hb ha k 0 0).coeFn_toLp,
    (herglotzCoeff_memLp_deriv_domain hb ha k 0 1).coeFn_toLp] with z hs hsub hi hx hy
  rw [hs]
  simp only [Pi.smul_apply]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hi]
  simp
  rw [hx, hy]
  simp [fderiv_herglotzCoeff_apply ha.intervalIntegrable, show coordDir 0 = 1 from rfl, show coordDir 1 = Complex.I from rfl]
  ring_nf
  rw [show Complex.I ^ 3 = -Complex.I by
    rw [show Complex.I ^ 3 = Complex.I ^ 2 * Complex.I by ring, Complex.I_sq]
    ring]
  ring

private theorem radialVekuaDensity_wave k p z :
    herglotzWave k (radialVekuaDensity k p) z =
      herglotzWave k (monoDensity 0) (z - p) := by
  rw [herglotzWave_eq, herglotzWave_eq]
  unfold radialVekuaDensity centeredPolyDensity
  rw [show polyDensity k {0} (fun _ => 1) = monoDensity 0 by
    funext φ
    simp [polyDensity]]
  unfold herglotzCoeff
  congr 2
  funext φ
  dsimp
  rw [show monoDensity 0 φ * planeWave k (-p) φ * planeWave k z φ = monoDensity 0 φ * planeWave k (z - p) φ by
    rw [mul_assoc, mul_comm (planeWave k (-p) φ) (planeWave k z φ)]
    rw [← planeWave_add k z (-p) φ]
    rw [sub_eq_add_neg]]

private theorem radial_affine_value_ae  hb
    p u f
    (hf : h1Value Ω u =ᵐ[volume.restrict Ω] f) j :
    (h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) u) : ℂ → ℂ)
      =ᵐ[volume.restrict Ω] fun z => (z - p) ^ j * f z := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, h1Value_neumannH1AffineMultiplier]
    filter_upwards [neumannAffineL2Multiplier_ae p (neumannH1AffineBound_spec hb p)
      (h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) u)), ih] with z hm hi
    rw [hm, hi, pow_succ']
    ring

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hb : Bornology.IsBounded (F '' ball 0 1))
    (hL : IsLipschitzDomain (F '' ball 0 1))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1))
    (hC : ∀ z ∈ ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ↑e = F)
    (hsource : closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)

local notation "ΩF" => F '' ball 0 1
local notation "UF" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "JF" => localConformalHardyPrimitive hR F hFs
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "VF" => localConformalVekuaH1AtBoundaryOrigin hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "ΓF" => physicalCircleTrace F
local notation "hΓF" => contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
local notation "AF" => localConformalVekuaGradientA hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "NCF" => normalizedConormal (localConformalVelocityCircle_isWL1_half hR F hFs) (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs) (localConformalCenteredCircle_isWL1_half hR F hFs)

include hhol in
private theorem radial_primitive_trace j θ :
    hardyFourierTrace (normalizedHardyAverage ((JF ^ j) radialVekuaInput)) θ =
      radialPrimitivePolynomial (F 1) j (ΓF θ) := by
  rw [localConformalHardyPrimitive_pow_volterra_of_H1 hR F hFs hhol
    radialVekuaInput radialVekuaInput_nonpositive
    (isSobolevSeq_smul _ radialVekuaInput_raw_H1), funext hardyFourierTrace_radialVekuaInput, radial_volterra_primitive_polynomial hΓF]
  simp only [radialPrimitivePolynomial, physicalCircleTrace, circleMap_zero]
  norm_num

/-- The completed physical Hardy primitive iterates are the actual
antiholomorphic polynomials, proved using genuine CR trace uniqueness. -/
local notation "Φ1" => localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC

private theorem localConformalHardy_radial_primitive_eq j :
    UF ((JF ^ j) radialVekuaInput) =
      smoothTraceH1 ΩF (radialPrimitiveTest hb (F 1) j) := by
  apply localConformalH1Pullback_injective hR F hFs hb hL hhol hinj hC hK
  apply neumannH1_eq_of_antiholomorphic_same_trace unitDisk_bounded
    isLipschitzDomain_unitDisk unitCircle_isBoundaryParam
  · rw [localConformalH1Pullback_hardyExtension]
    exact diskHardyExtension_cauchyRiemann _
  · exact (localConformalH1Pullback_antiholomorphic_iff hR F hFs hb hL hhol hinj hC _).mpr
      (radialPrimitiveTest_cauchyRiemann hb hL.1.1 (F 1) j)
  · change TF (UF ((JF ^ j) radialVekuaInput)) =
      TF (smoothTraceH1 ΩF (radialPrimitiveTest hb (F 1) j))
    apply Lp.ext
    have hu := localConformalHardy_affine_primitive_trace_ae hR F hFs hb hL
      hhol hinj hC hK e he hsource hes radialVekuaInput
      radialVekuaInput_nonpositive radialVekuaInput_raw_H1 0 j
    simp only [pow_zero, ContinuousLinearMap.one_apply, one_mul] at hu
    filter_upwards [hu, Φ1 (radialPrimitiveTest hb (F 1) j)] with θ hu ht
    rw [hu, ht, radial_primitive_trace hR F hFs hhol j θ]
    exact ((radialPrimitiveTest_near hb (F 1) j (by
      rw [← localConformal_closedDisk_image_eq_closure hR F hFs]
      exact mem_image_of_mem F (sphere_subset_closedBall
        (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ)))).self_of_nhds).symm

/-- Actual L2 values of every completed primitive iterate retain the
factorial, full constant mode, and the physical boundary center. -/
theorem localConformalHardy_radial_primitive_value_ae j :
    (h1Value ΩF (UF ((JF ^ j) radialVekuaInput)) : ℂ → ℂ)
      =ᵐ[volume.restrict ΩF] fun z => conj (z - F 1) ^ j / (j.factorial : ℂ) := by
  rw [localConformalHardy_radial_primitive_eq hR F hFs hb hL hhol hinj hC hK e he hsource hes]
  exact radialPrimitiveTest_value_ae hb hL.1.1 (F 1) j

/-- The actual physical H1 Vekua vector for the full zero Fourier mode
equals the actual centered radial Herglotz H1 vector. This equality comes
from the true completed H1 series and pointwise entire-wave series. -/
local notation "Φ0" => Real.sqrt E

theorem localConformalVekuaH1_radial_eq_herglotz  (hE : 0 < E) :
    VF (E : ℂ) radialVekuaInput =
      herglotzWaveH1 hb (isDirDensity_radialVekuaDensity (Φ0) (F 1))
        (Φ0) := by
  haveI : IsFiniteMeasure (volume.restrict ΩF) :=
    isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  let term : ℕ → L2 ΩF := fun j => physicalVekuaCoeff E j •
    h1Value ΩF ((neumannH1AffineMultiplier hb (F 1) ^ j)
      (UF ((JF ^ j) radialVekuaInput)))
  have hs : HasSum term (h1Value ΩF (VF E radialVekuaInput)) := by
    simpa only [term, map_smul, localConformalVekuaH1AtBoundaryOrigin] using
      (h1Value ΩF).hasSum (localConformalVekuaH1_hasSum hR F hFs hb hL hhol hinj hC hK
        e he hsource hes (F 1) E radialVekuaInput)
  have ht j : term j =ᵐ[volume.restrict ΩF]
      fun z => physicalVekuaCoeff E j * (z - F 1) ^ j *
        radialPrimitivePolynomial (F 1) j z := by
    have hm := radial_affine_value_ae hb (F 1) (UF ((JF ^ j) radialVekuaInput))
      (radialPrimitivePolynomial (F 1) j) (localConformalHardy_radial_primitive_value_ae hR F hFs hb hL hhol hinj hC hK e he hsource hes j) j
    filter_upwards [Lp.coeFn_smul (physicalVekuaCoeff E j)
      (h1Value ΩF ((neumannH1AffineMultiplier hb (F 1) ^ j)
        (UF ((JF ^ j) radialVekuaInput)))), hm] with z hs hm
    change (physicalVekuaCoeff E j •
      h1Value ΩF ((neumannH1AffineMultiplier hb (F 1) ^ j)
        (UF ((JF ^ j) radialVekuaInput)))) z = _
    simp only [Pi.smul_apply, smul_eq_mul, hs, hm]
    ring
  apply h1Value_injective hL.1.1
  apply Lp.ext
  rw [h1Value_herglotzWaveH1]
  filter_upwards [radial_Lp_series_ae term (h1Value ΩF (VF E radialVekuaInput)) (fun j z => physicalVekuaCoeff E j * (z - F 1) ^ j * radialPrimitivePolynomial (F 1) j z) (herglotzWave (Φ0) (radialVekuaDensity (Φ0) (F 1))) hs ht (fun j => ((continuous_const.mul ((continuous_id.sub continuous_const).pow j)).mul (radialPrimitivePolynomial_contDiff (F 1) j).continuous).aestronglyMeasurable) (fun z => (by
    have hs := hasSum_vekuaMonoTerm ((Real.sqrt_pos.mpr hE).ne') 0 (z - (F 1))
    rw [Real.sq_sqrt hE.le] at hs
    simp at hs
    rw [radialVekuaDensity_wave]
    convert hs using 1
    funext j
    simp [physicalVekuaCoeff, radialPrimitivePolynomial, vekuaMonoTerm, div_eq_mul_inv]
    ring)), (herglotzCoeff_memLp_domain hb
    (isDirDensity_radialVekuaDensity (Φ0) (F 1)) (Φ0) 0).coeFn_toLp]
    with z hv hh
  exact hv.trans ((herglotzWave_eq _ _ z).trans hh.symm)

/-- The actual scaled radial density has its exact initial jet, including
the full zero component and the sqrt(2) convention of the jet space. -/
theorem localConformalRadial_scaled_herglotzVec_at_boundary_origin E a :
    herglotzVec (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (F 1) a)
      (Real.sqrt E) (F 1) = (a / (Real.sqrt 2 : ℂ)) • basisVec 0 := by
  simpa [radialVekuaScaledDensity, antiPoly] using
    herglotzVec_centeredPolyDensity (Real.sqrt E) (F 1) {0} (fun _ => a)

/-- Arbitrary scalar multiples preserve the actual radial realization,
so the projected observation correction is a true zero-mode Vekua vector. -/
local notation "Φ2" => localConformalVekuaH1_radial_eq_herglotz hR F hFs hb hL hhol hinj hC hK e he hsource hes

theorem localConformalVekuaH1_radial_smul_eq  (hE : 0 < E) (a : ℂ) :
    VF (E : ℂ) (a • radialVekuaInput) = a •
      herglotzWaveH1 hb (isDirDensity_radialVekuaDensity (Φ0) (F 1))
        (Φ0) := by
  rw [map_smul, Φ2 hE]

/-- Equality with the actual amplitude-a Herglotz H1 vector, rather than
merely equality of formal coefficients. -/
theorem localConformalVekuaH1_radial_smul_eq_herglotz  (hE : 0 < E) (a : ℂ) :
    VF (E : ℂ) (a • radialVekuaInput) =
      herglotzWaveH1 hb (isDirDensity_radialVekuaScaledDensity (Φ0) (F 1) a)
        (Φ0) := by
  rw [localConformalVekuaH1_radial_smul_eq hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hE]
  simpa [radialVekuaScaledDensity_eq_smul] using
    (radial_herglotzWaveH1_smul hb hL.1.1
      (isDirDensity_radialVekuaDensity (Φ0) (F 1)) a (Φ0)).symm

/-- The actual coordinate trace of the radial completed vector equals the
ordinary centered Herglotz wave. No constant-speed property of Gamma is
used: Gamma is the true conformal circle trace. -/
theorem localConformalVekuaH1_radial_coordinate_trace_ae 
    (hE : 0 < E) a :
    (TF (VF (E : ℂ) (a • radialVekuaInput)) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        fun θ => herglotzWave (Φ0)
          (radialVekuaScaledDensity (Φ0) (F 1) a) (ΓF θ) := by
  rw [localConformalVekuaH1_radial_smul_eq_herglotz hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hE]
  obtain ⟨f, hfu, hf⟩ := exists_radialWaveTest hb hL.1.1
    (isDirDensity_radialVekuaScaledDensity (Φ0) (F 1) a) (Φ0)
  rw [← hfu]
  filter_upwards [Φ1 f] with θ ht
  rw [ht, herglotzWave_eq]
  apply hf
  rw [← localConformal_closedDisk_image_eq_closure hR F hFs]
  exact mem_image_of_mem F (sphere_subset_closedBall
    (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))

/-- The true derivative companion A of the radial Vekua series has the
actual smooth coefficient-one trace. This follows from the genuine
Wirtinger derivative in L2 and value injectivity in the real H1 graph. -/
theorem localConformalRadial_gradientA_coordinate_trace_ae  (hE : 0 < E) :
    (TF (AF (F 1) (E : ℂ) radialVekuaInput) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        fun θ => -(Complex.I * (Φ0 : ℂ) / 2) *
          herglotzCoeff (Φ0) (radialVekuaDensity (Φ0) (F 1)) 1 (ΓF θ) := by
  let ρ := radialVekuaDensity (Φ0) (F 1)
  let c := -(Complex.I * Φ0 / 2)
  obtain ⟨f, hf⟩ := exists_radialCoeffTest hb
    (isDirDensity_radialVekuaDensity (Φ0) (F 1)) (Φ0) 1
  have hA : AF (F 1) E radialVekuaInput = c • smoothTraceH1 ΩF f := by
    apply h1Value_injective hL.1.1
    rw [map_smul, h1Value_smoothTraceH1]
    apply Lp.ext
    filter_upwards [(show h1Value ΩF (AF (F 1) E radialVekuaInput) =ᵐ[volume.restrict ΩF] fun z => c * herglotzCoeff (Φ0) ρ 1 z by
      have hD : h1Value ΩF (AF (F 1) E radialVekuaInput) =
          h1WirtingerD ΩF (VF E radialVekuaInput) := by
        rw [localConformalVekuaGradientA_apply, map_smul]
        exact (localConformalVekuaH1_wirtingerD hR F hFs hb hL hhol hinj hC hK
          e he hsource hes (F 1) E radialVekuaInput).symm
      rw [hD, Φ2 hE]
      exact radial_herglotzWirtingerD_ae hb
        (isDirDensity_radialVekuaDensity (Φ0) (F 1)) (Φ0)), Lp.coeFn_smul c ((smoothTraceTests_memLp ΩF f).toLp _),
      (smoothTraceTests_memLp ΩF f).coeFn_toLp,
      ae_restrict_mem hL.1.1.measurableSet] with z ha hs hfv hz
    simp [ha, hs, hfv, hf z (subset_closure hz), ρ]
  rw [hA, map_smul]
  filter_upwards [Lp.coeFn_smul c (TF (smoothTraceH1 ΩF f)),
    Φ1 f] with θ hs ht
  simp only [Pi.smul_apply, smul_eq_mul, hs, ht]
  exact congrArg (fun z => c * z) (hf _ (by
    rw [← localConformal_closedDisk_image_eq_closure hR F hFs]
    exact mem_image_of_mem F (sphere_subset_closedBall
      (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))))

/-- The actual radial conormal belongs to genuine parameter L2 even for
the variable-speed conformal circle trace. This is a property of this
constructed smooth wave, not a gain for arbitrary normalized loads. -/
local notation "Φ3" => LipschitzWith L ΓF

theorem localConformalRadial_conormal_memLp 
    (hΓLip : Φ3) E a :
    MemLp (herglotzConormal (Real.sqrt E)
      (radialVekuaScaledDensity (Real.sqrt E) (F 1) a) ΓF) 2
      (volume.restrict (Ioc 0 (2 * Real.pi))) :=
  memLp_herglotzConormal
    (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (F 1) a) (Real.sqrt E) hΓLip

/-- The true radial conormal has precisely the missing cut direction in
the original observation adjoint: amplitude one gives i times cutC. -/
theorem localConformalRadial_observationAdj_conormal 
    (hΓLip : Φ3) 
     (hW : IsTransport ΓF E W) a :
    observationAdj W (herglotzConormal (Φ0)
      (radialVekuaScaledDensity (Real.sqrt E) (F 1) a) ΓF) =
        (Complex.I * a) • cutC (W (2 * Real.pi)) (basisVec 0) := by
  have hclosed : ΓF (2 * Real.pi) = ΓF 0 := by
    simpa using physicalCircleTrace_periodic F 0
  rw [(herglotzForm_eq hΓLip hclosed hW
    (isDirDensity_radialVekuaScaledDensity (Φ0) (F 1) a)).1,
    show ΓF 0 = F 1 by
      simp [physicalCircleTrace, circleMap_zero], localConformalRadial_scaled_herglotzVec_at_boundary_origin,
    map_smul, smul_smul]
  change (((Real.sqrt 2) * Complex.I) * (a / (Real.sqrt 2))) •
      cutC (W (2 * Real.pi)) (basisVec 0) = _
  congr 1
  field_simp [(by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')]
  -- `field_simp` closes the scalar identity after clearing the nonzero square root.

/-- The genuine variable-speed coordinate conormal as an ordinary L2
class. Its measure is dtheta and its velocity is the actual Gamma'. -/
def localConformalRadialCoordinateLoad 
    (hΓLip : Φ3) (E : ℝ) (a : ℂ) : BoundaryL2 :=
  (localConformalRadial_conormal_memLp F hΓLip E a).toLp
    (herglotzConormal (Real.sqrt E) (radialVekuaScaledDensity (Real.sqrt E) (F 1) a) ΓF)

theorem localConformalRadialCoordinateLoad_ae 
    (hΓLip : Φ3) E a :
    (localConformalRadialCoordinateLoad F hΓLip E a : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))]
        herglotzConormal (Real.sqrt E)
          (radialVekuaScaledDensity (Real.sqrt E) (F 1) a) ΓF :=
  (localConformalRadial_conormal_memLp F hΓLip E a).coeFn_toLp

theorem localConformalRadialCoordinateLoad_smul 
    (hΓLip : Φ3) E a :
    localConformalRadialCoordinateLoad F hΓLip E a =
      a • localConformalRadialCoordinateLoad F hΓLip E 1 := by
  apply Lp.ext
  filter_upwards [localConformalRadialCoordinateLoad_ae F hΓLip E a,
    localConformalRadialCoordinateLoad_ae F hΓLip E 1,
    Lp.coeFn_smul a (localConformalRadialCoordinateLoad F hΓLip E 1)] with θ ha h1 hs
  simp only [Pi.smul_apply, smul_eq_mul, ha, hs, h1,
    radialVekuaScaledDensity_eq_smul,
    herglotzConormal_smul_density
      (isDirDensity_radialVekuaDensity (Real.sqrt E) (F 1))]
  simp only [one_mul]

/-- The actual ordinary L2 representative retains exactly the original
observation adjoint, including the boundary-origin cut direction. -/
theorem localConformalRadialCoordinateLoad_observationAdj 
    (hΓLip : Φ3) 
     (hW : IsTransport ΓF E W) a :
    observationAdj W (localConformalRadialCoordinateLoad F hΓLip E a : ℝ → ℂ) =
      (Complex.I * a) • cutC (W (2 * Real.pi)) (basisVec 0) := by
  rw [← localConformalRadial_observationAdj_conormal F hΓLip hW a, observationAdj, observationAdj,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  apply integral_congr_ae
  filter_upwards [localConformalRadialCoordinateLoad_ae F hΓLip E a] with θ hθ
  rw [hθ]

include hb hL hhol hinj hC hK e he hsource hes in
private theorem radial_normalizedConormal_eq_coordinateLoad_one 
    (hΓLip : Φ3)  (hE : 0 < E) :
    NCF (E : ℂ) radialVekuaInput =
      sobolevSmoothing (1 / 2) (by norm_num)
        (boundaryFourier (localConformalRadialCoordinateLoad F hΓLip E 1)) := by
  let ρ := radialVekuaDensity (Φ0) (F 1)
  let c := -(Complex.I * Φ0 / 2)
  let f : ℝ → ℂ := fun θ => herglotzCoeff (Φ0) ρ 0 (ΓF θ)
  let df : ℝ → ℂ := fun θ => c *
    (deriv ΓF θ * herglotzCoeff (Φ0) ρ 1 (ΓF θ) +
      conj (deriv ΓF θ) * herglotzCoeff (Φ0) ρ (-1) (ΓF θ))
  let A := (boundaryContinuousMultiplier (localConformalVelocityCircle F)) (TF (AF (F 1) E radialVekuaInput))
  let r := localConformalRadialCoordinateLoad F hΓLip E 1
  let d := (2 : ℂ) • A - Complex.I • r
  have hd : (d : ℝ → ℂ) =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] df := by
    filter_upwards [Lp.coeFn_sub ((2 : ℂ) • A) (Complex.I • r),
      Lp.coeFn_smul (2 : ℂ) A, Lp.coeFn_smul Complex.I r, (show A =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] fun θ => deriv ΓF θ * (c * herglotzCoeff (Φ0) ρ 1 (ΓF θ)) by
        filter_upwards [boundaryContinuousMultiplier_ae (localConformalVelocityCircle F)
            (TF (AF (F 1) E radialVekuaInput)),
          localConformalRadial_gradientA_coordinate_trace_ae hR F hFs hb hL hhol hinj hC hK
            e he hsource hes hE] with θ hm ha
        rw [hm, ha, localConformalVelocityCircle_apply hR F hFs]),
      localConformalRadialCoordinateLoad_ae F hΓLip E 1] with θ hs h2 hi ha hr
    simp only [d, r, hs, h2, hi, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha, hr,
      radialVekuaScaledDensity_one, herglotzConormal_eq
        (isDirDensity_radialVekuaDensity (Φ0) (F 1)).intervalIntegrable, df, c, ρ]
    ring_nf
  have hdf θ : HasDerivAt f (df θ) θ := by
    simpa only [f, df, c, ρ, Function.comp_def,
      fderiv_herglotzCoeff_apply
        (isDirDensity_radialVekuaDensity (Φ0) (F 1)).intervalIntegrable,
      zero_add, zero_sub] using (differentiable_herglotzCoeff (isDirDensity_radialVekuaDensity (Φ0) (F 1)).intervalIntegrable (Φ0) 0 (ΓF θ)).hasFDerivAt.comp_hasDerivAt θ ((hΓF).differentiable_one θ).hasDerivAt
  have hcoeff (n : ℤ) : boundaryFourier d n =
      Complex.I * (n : ℂ) * boundaryFourier (TF (VF E radialVekuaInput)) n := by
    rw [radial_boundaryFourier_ae d hd n,
      radial_boundaryFourier_ae _ (by
        simpa only [one_smul, radialVekuaScaledDensity_one, herglotzWave_eq, f, ρ] using
          localConformalVekuaH1_radial_coordinate_trace_ae hR F hFs hb hL hhol hinj hC hK
            e he hsource hes hE 1) n, fourierCoeffOn_deriv hdf (by
              exact continuous_const.mul
                (((hΓF).continuous_deriv_one.mul
                  ((continuous_herglotzCoeff
                    (isDirDensity_radialVekuaDensity (Φ0) (F 1)).intervalIntegrable
                      (Φ0) 1).comp (hΓF).continuous)).add
                  ((Complex.continuous_conj.comp (hΓF).continuous_deriv_one).mul
                    ((continuous_herglotzCoeff
                      (isDirDensity_radialVekuaDensity (Φ0) (F 1)).intervalIntegrable
                        (Φ0) (-1)).comp (hΓF).continuous)))) (by
              dsimp only [f]
              rw [show ΓF (2 * Real.pi) = ΓF 0 by
                simpa only [zero_add] using physicalCircleTrace_periodic F 0]) n]
    ring
  apply lp.ext
  funext n
  have hn := hcoeff n
  simp only [d, map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hn
  have hi := congrArg (fun z => Complex.I * z) hn
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_one_mul] at hi
  rw [localConformalVekua_normalizedConormal_fourier hR F hFs hb hL hhol hinj hC hK
    e he hsource hes E radialVekuaInput radialVekuaInput_nonpositive
      radialVekuaInput_raw_H1 n]
  simp only [sobolevSmoothing, diagOp_apply]
  change (sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) *
      (-(n : ℂ) * boundaryFourier (TF (VF E radialVekuaInput)) n -
        2 * Complex.I * boundaryFourier A n) = _
  linear_combination -(sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) * hi

include hb hL hhol hinj hC hK e he hsource hes in
/-- The genuine normalized conormal of every scalar full zero mode is
exactly the half-smoothed unitary Fourier transform of its actual L2
radial conormal, including the zero mode and variable circle speed. -/
theorem localConformalRadial_normalizedConormal_eq_coordinateLoad 
    (hΓLip : Φ3)  (hE : 0 < E) a :
    NCF (E : ℂ) (a • radialVekuaInput) =
      sobolevSmoothing (1 / 2) (by norm_num)
        (boundaryFourier (localConformalRadialCoordinateLoad F hΓLip E a)) := by
  rw [map_smul, radial_normalizedConormal_eq_coordinateLoad_one hR F hFs hb hL hhol hinj
    hC hK e he hsource hes hΓLip hE, localConformalRadialCoordinateLoad_smul (F := F) hΓLip E a]
  simp

end PhysicalCoordinates

end PolyaNeumann

end
