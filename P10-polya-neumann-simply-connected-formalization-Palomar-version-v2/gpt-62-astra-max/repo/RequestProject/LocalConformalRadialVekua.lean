module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.PhysicalDrivenKernelConormal
public import RequestProject.NeumannHerglotzBoundary
public import RequestProject.HerglotzReduction
public import RequestProject.LocalConformalBoundaryGeometry
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import RequestProject.PlanarNotation

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

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Filter Metric
open scoped Topology ComplexConjugate InnerProductSpace

/-- Normalized half-trace input for the actual ordinary Hardy constant one. -/
def radialVekuaInput : L2Z := fourierScale • stdBasisZ 0

theorem radialVekuaInput_apply (n : ℤ) :
    radialVekuaInput n = if n = 0 then fourierScale else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [radialVekuaInput, stdBasisZ_apply, lp.single_apply]
  · simp [radialVekuaInput, stdBasisZ_apply, lp.single_apply, hn]

section

variable (p : ℂ) (j : ℕ) (z : ℂ)

theorem radialVekuaInput_nonpositive : IsNonpositiveFourierSupport radialVekuaInput := by
  intro n hn
  rw [radialVekuaInput_apply, if_neg (ne_of_gt hn)]

theorem normalizedHardyAverage_radialVekuaInput (n : ℤ) :
    normalizedHardyAverage radialVekuaInput n = if n = 0 then 1 else 0 := by
  
  by_cases hn : n = 0
  · subst n
    simp only [normalizedHardyAverage, fromL2, radialVekuaInput_apply,
      sobWeight, Int.cast_zero, abs_zero]
    norm_num
    have h2 : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
      simp
    
    field_simp [h2, (by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne')]
  · simp [normalizedHardyAverage, fromL2, radialVekuaInput_apply, hn]

theorem radialVekuaInput_raw_H1 : IsSobolevSeq 1 (fromL2 halfOrder radialVekuaInput) := by
  classical
  
  refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
  have hn0 : n ≠ 0 := by simpa only [Finset.mem_singleton] using hn
  simp [fromL2, radialVekuaInput_apply, hn0]

theorem hardyFourierTrace_radialVekuaInput (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage radialVekuaInput) θ = 1 := by
  classical
  simp [hardyFourierTrace, normalizedHardyAverage_radialVekuaInput]

include j p z in
private def radialPrimitivePolynomial : ℂ :=
  conj (z - p) ^ j / (j.factorial : ℂ)

private theorem radialPrimitivePolynomial_contDiff :
    ContDiff ℝ ∞ (radialPrimitivePolynomial p j) :=
  ((Complex.conjCLE.contDiff.comp (contDiff_id.sub contDiff_const)).pow j).div_const _

private theorem radialPrimitivePolynomial_fderiv (v : ℂ) :
    fderiv ℝ (radialPrimitivePolynomial p j) z v =
      ((j : ℂ) * conj (z - p) ^ (j - 1) * conj v) / (j.factorial : ℂ) := by
  have hsub := (hasFDerivAt_id (𝕜 := ℝ) z).sub_const p
  have hc := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := z - p)).comp z hsub
  have h := congrArg (fun A : ℂ →L[ℝ] ℂ => A v)
    ((hc.pow j).mul_const j.factorial⁻¹).fderiv
  change fderiv ℝ (fun y : ℂ => conj (y - p) ^ j / (j.factorial : ℂ)) z v = _
  simpa [radialPrimitivePolynomial, div_eq_mul_inv, id_eq, nsmul_eq_mul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using h

end

private theorem exists_radialPrimitiveTest {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (j : ℕ) : ∃ f : smoothTraceTests,
      ∀ z ∈ closure Ω, (f : ℂ → ℂ) =ᶠ[𝓝 z] radialPrimitivePolynomial p j := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_compact_extension hb.isCompact_closure
    isOpen_univ (subset_univ _) (radialPrimitivePolynomial_contDiff p j).contDiffOn
  exact ⟨⟨f, hf⟩, heq⟩

private def radialPrimitiveTest {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (j : ℕ) : smoothTraceTests :=
  Classical.choose (exists_radialPrimitiveTest hb p j)

private theorem radialPrimitiveTest_near {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (j : ℕ) {z : ℂ} (hz : z ∈ closure Ω) :
    (radialPrimitiveTest hb p j : ℂ → ℂ) =ᶠ[𝓝 z] radialPrimitivePolynomial p j :=
  Classical.choose_spec (exists_radialPrimitiveTest hb p j) z hz

private theorem radialPrimitiveTest_value_ae {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hΩ : IsOpen Ω) (p : ℂ) (j : ℕ) :
    (h1Value Ω (smoothTraceH1 Ω (radialPrimitiveTest hb p j)) : ℂ → ℂ)
      =ᵐ[volume.restrict Ω] radialPrimitivePolynomial p j := by
  rw [h1Value_smoothTraceH1]
  filter_upwards [(smoothTraceTests_memLp Ω (radialPrimitiveTest hb p j)).coeFn_toLp,
    ae_restrict_mem hΩ.measurableSet] with z hz hmem
  exact hz.trans (radialPrimitiveTest_near hb p j (subset_closure hmem)).self_of_nhds

private theorem radialPrimitiveTest_cauchyRiemann {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) (p : ℂ) (j : ℕ) :
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
    _ = _ := hx
    _ = Complex.I * fderiv ℝ (radialPrimitiveTest hb p j) z (coordDir 1) := by
      rw [((radialPrimitiveTest_near hb p j (subset_closure hz)).fderiv_eq)]
      simp only [radialPrimitivePolynomial_fderiv,
        show coordDir 0 = (1 : ℂ) from rfl,
        show coordDir 1 = Complex.I from rfl, map_one, Complex.conj_I, mul_one]
      
      simp only [div_eq_mul_inv]
      calc
        _ = (Complex.I * (-Complex.I)) *
            (↑j * (starRingEnd ℂ) (z - p) ^ (j - 1) * (↑j.factorial)⁻¹) := by
          simp
        _ = _ := by ring
    _ = Complex.I * ((((smoothTraceTests_memLp_deriv Ω
        (radialPrimitiveTest hb p j) 1).toLp _) : ℂ → ℂ) z) := by rw [hy]
    _ = _ := hs.symm

private theorem radial_volterra_primitive_polynomial
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (j : ℕ) (θ : ℝ) :
    volterraPrimitiveIterate (fun s => conj (deriv γ s)) (fun _ => 1) j θ =
      conj (γ θ - γ 0) ^ j / (j.factorial : ℂ) := by
  induction j generalizing θ with
  | zero => simp [volterraPrimitiveIterate]
  | succ j ih =>
    have hd (s : ℝ) : HasDerivAt
        (fun t => conj (γ t - γ 0) ^ (j + 1) / (j + 1).factorial)
        (conj (deriv γ s) * (conj (γ s - γ 0) ^ j / j.factorial)) s := by
      have hz : HasDerivAt (fun t => conj (γ t - γ 0)) (conj (deriv γ s)) s := by
        simpa only [Complex.star_def] using
          ((hγ.differentiable_one s).hasDerivAt.sub_const (γ 0)).star
      convert (hz.pow (j + 1)).div_const (j + 1).factorial using 1
      
      
      simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
      field_simp [(by exact_mod_cast j.factorial_ne_zero), (by exact_mod_cast Nat.succ_ne_zero j)]
    
    change (∫ s in (0 : ℝ)..θ, conj (deriv γ s) *
      volterraPrimitiveIterate (fun t => conj (deriv γ t)) (fun _ => 1) j s) = _
    rw [show (fun s => conj (deriv γ s) *
        volterraPrimitiveIterate (fun t => conj (deriv γ t)) (fun _ => 1) j s) =
        (fun s => conj (deriv γ s) * (conj (γ s - γ 0) ^ j / j.factorial)) by
          simp [*]]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      (((Complex.continuous_conj.comp hγ.continuous_deriv_one).mul
        (((Complex.continuous_conj.comp (hγ.continuous.sub continuous_const)).pow j).div_const _)).intervalIntegrable _ _)]
    simp

private theorem radial_Lp_series_ae {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (u : ℕ → Lp ℂ 2 μ) (v : Lp ℂ 2 μ)
    (f : ℕ → α → ℂ) (g : α → ℂ) (hs : HasSum u v)
    (hf : ∀ j, (u j : α → ℂ) =ᵐ[μ] f j)
    (hfm : ∀ j, AEStronglyMeasurable (f j) μ)
    (hpt : ∀ x, HasSum (fun j => f j x) (g x)) : (v : α → ℂ) =ᵐ[μ] g := by
  classical
  have heq (s : Finset ℕ) : ((∑ j ∈ s, u j : Lp ℂ 2 μ) : α → ℂ)
      =ᵐ[μ] fun x => ∑ j ∈ s, f j x := by
    induction s using Finset.induction_on with
    | empty => exact (Lp.coeFn_zero ℂ 2 μ)
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (u a) (∑ j ∈ s, u j), hf a, ih] with x hsum hfa his
      simp only [Pi.add_apply] at hsum
      rw [hsum, hfa, his]
  
  
  exact tendstoInMeasure_ae_unique ((tendstoInMeasure_of_tendsto_Lp hs.tendsto_sum_nat).congr (fun N => heq _) EventuallyEq.rfl) (tendstoInMeasure_of_tendsto_ae
    (fun N => by
      fun_prop)
    (Eventually.of_forall fun x => (hpt x).tendsto_sum_nat))

section

variable (k : ℝ) (p a : ℂ)
include k p

/-- Genuine centered radial Herglotz density, with ordinary value one at p. -/
def radialVekuaDensity : ℝ → ℂ :=
  centeredPolyDensity k p {0} (fun _ => 1)

theorem isDirDensity_radialVekuaDensity :
    IsDirDensity (radialVekuaDensity k p) :=
  isDirDensity_centeredPolyDensity k p {0} (fun _ => 1)

include a in
/-- Actual centered radial density with the indicated ordinary amplitude. -/
def radialVekuaScaledDensity : ℝ → ℂ :=
  centeredPolyDensity k p {0} (fun _ => a)

theorem isDirDensity_radialVekuaScaledDensity :
    IsDirDensity (radialVekuaScaledDensity k p a) :=
  isDirDensity_centeredPolyDensity k p {0} (fun _ => a)

end

section

variable (k : ℝ) (p : ℂ)

theorem radialVekuaScaledDensity_eq_smul (a : ℂ) :
    radialVekuaScaledDensity k p a = a • radialVekuaDensity k p := by
  funext φ
  simp [radialVekuaScaledDensity, radialVekuaDensity, centeredPolyDensity, polyDensity]
  ; ring

theorem radialVekuaScaledDensity_one :
    radialVekuaScaledDensity k p 1 = radialVekuaDensity k p := rfl

private theorem radial_herglotzWaveH1_smul {Ω : Set ℂ}
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
    _ = c * ((((herglotzCoeff_memLp_domain hb ha k 0).toLp _) : ℂ → ℂ) z) := by
      rw [hcoeff]
    _ = (c • ((((herglotzCoeff_memLp_domain hb ha k 0).toLp _) : ℂ → ℂ) z)) := by
      rfl
     _ = _ := hs.symm

private theorem exists_radialWaveTest {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hΩ : IsOpen Ω) {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    ∃ f : smoothTraceTests, smoothTraceH1 Ω f = herglotzWaveH1 hb ha k ∧
      ∀ z ∈ closure Ω, f z = herglotzCoeff k a 0 z := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_compact_extension hb.isCompact_closure
    isOpen_univ (subset_univ _) (contDiff_herglotzCoeff_infty ha.intervalIntegrable k 0).contDiffOn
  
  have hval  :=
    fun z hz => (heq z hz).self_of_nhds
  refine ⟨(⟨f, hf⟩), ?_, hval⟩
  apply h1Value_injective hΩ
  rw [h1Value_smoothTraceH1, h1Value_herglotzWaveH1]
  apply MemLp.toLp_congr
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
  exact hval z (subset_closure hz)

private theorem exists_radialCoeffTest {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) (m : ℤ) :
    ∃ f : smoothTraceTests, ∀ z ∈ closure Ω, f z = herglotzCoeff k a m z := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_compact_extension hb.isCompact_closure
    isOpen_univ (subset_univ _) (contDiff_herglotzCoeff_infty ha.intervalIntegrable k m).contDiffOn
  exact ⟨⟨f, hf⟩, fun z hz => (heq z hz).self_of_nhds⟩

private theorem radial_herglotzWirtingerD_ae {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) {a : ℝ → ℂ} (ha : IsDirDensity a) (k : ℝ) :
    (h1WirtingerD Ω (herglotzWaveH1 hb ha k) : ℂ → ℂ)
      =ᵐ[volume.restrict Ω] fun z => -(Complex.I * k / 2) * herglotzCoeff k a 1 z := by
  let x  := (herglotzCoeff_memLp_deriv_domain hb ha k 0 0).toLp
    (fun z => fderiv ℝ (herglotzCoeff k a 0) z (coordDir 0))
  let y  := (herglotzCoeff_memLp_deriv_domain hb ha k 0 1).toLp
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
  simp only [Pi.smul_apply]
  rw [hx, hy]
  simp only [smul_eq_mul,
    fderiv_herglotzCoeff_apply ha.intervalIntegrable,
    show coordDir 0 = (1 : ℂ) from rfl,
    show coordDir 1 = Complex.I from rfl,
    zero_add, zero_sub, map_one, Complex.conj_I,
    one_mul]
  ring_nf
  simp <;> ring

private theorem radialVekuaDensity_wave (z : ℂ) :
    herglotzWave k (radialVekuaDensity k p) z =
      herglotzWave k (monoDensity 0) (z - p) := by
  have hpoly : polyDensity k {0} (fun _ => (1 : ℂ)) = monoDensity 0 := by
    funext φ
    simp [polyDensity]
  rw [herglotzWave_eq, herglotzWave_eq]
  unfold radialVekuaDensity centeredPolyDensity
  rw [hpoly]
  unfold herglotzCoeff
  congr 2
  funext φ
  dsimp
  have hprod : monoDensity 0 φ * planeWave k (-p) φ * planeWave k z φ =
      monoDensity 0 φ * planeWave k (z - p) φ := by
    rw [mul_assoc]
    rw [mul_comm (planeWave k (-p) φ) (planeWave k z φ)]
    rw [← planeWave_add k z (-p) φ]
    rw [sub_eq_add_neg]
  rw [hprod]

end

private theorem radial_wave_hasSum {E : ℝ} (hE : 0 < E) (p z : ℂ) :
    HasSum (fun j : ℕ => physicalVekuaCoeff (E : ℂ) j * (z - p) ^ j *
      radialPrimitivePolynomial p j z)
      (herglotzWave (Real.sqrt E) (radialVekuaDensity (Real.sqrt E) p) z) := by
  have hk  := (Real.sqrt_pos.mpr hE).ne'
  have hs := hasSum_vekuaMonoTerm hk 0 (z - p)
  rw [Real.sq_sqrt hE.le] at hs
  simp at hs
  rw [radialVekuaDensity_wave]
  convert hs using 1
  funext j
  simp only [physicalVekuaCoeff, radialPrimitivePolynomial, vekuaMonoTerm,
    Nat.factorial_zero, Nat.cast_one, zero_add, mul_one, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem radial_affine_value_ae {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (u : NeumannH1 Ω) (f : ℂ → ℂ)
    (hf : (h1Value Ω u : ℂ → ℂ) =ᵐ[volume.restrict Ω] f) (j : ℕ) :
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

section

variable (Φ : DiskCoordinates) (j : ℕ) (F : ℂ → ℂ)

private theorem radial_primitive_trace (Φ : SmoothDiskMap)
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (j : ℕ) (θ : ℝ) :
    hardyFourierTrace (normalizedHardyAverage ((Φ.hardyPrimitive ^ j) radialVekuaInput)) θ =
      radialPrimitivePolynomial (Φ.map 1) j (Φ.boundary θ) := by
  rw [localConformalHardyPrimitive_pow_volterra_of_H1 Φ hhol
    radialVekuaInput radialVekuaInput_nonpositive
    (isSobolevSeq_smul _ radialVekuaInput_raw_H1)]
  have hf  :=
    funext hardyFourierTrace_radialVekuaInput
  rw [hf, radial_volterra_primitive_polynomial Φ.boundaryC1]
  simp [radialPrimitivePolynomial, physicalCircleTrace, circleMap_zero]

/-- The completed physical Hardy primitive iterates are the actual
antiholomorphic polynomials, proved using genuine CR trace uniqueness. -/
private theorem localConformalHardy_radial_primitive_eq :
    Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) radialVekuaInput) =
      smoothTraceH1 Φ.domain (radialPrimitiveTest Φ.bounded (Φ.map 1) j) := by
  apply localConformalH1Pullback_injective Φ
  apply neumannH1_eq_of_antiholomorphic_same_trace unitDisk_bounded
    isLipschitzDomain_unitDisk unitCircle_isBoundaryParam
  · rw [localConformalH1Pullback_hardyExtension]
    exact diskHardyExtension_cauchyRiemann _
  · exact (localConformalH1Pullback_antiholomorphic_iff Φ _).mpr
      (radialPrimitiveTest_cauchyRiemann Φ.bounded Φ.lipschitzDomain.1.1 (Φ.map 1) j)
  · change (Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) radialVekuaInput)) =
      (Φ.pulledBackTrace Φ.lipschitzDomain) (smoothTraceH1 Φ.domain (radialPrimitiveTest Φ.bounded (Φ.map 1) j))
    apply Lp.ext
    have hu := localConformalHardy_affine_primitive_trace_ae Φ radialVekuaInput
      radialVekuaInput_nonpositive radialVekuaInput_raw_H1 0 j
    simp only [pow_zero, ContinuousLinearMap.one_apply, one_mul] at hu
    filter_upwards [hu, localConformalDiskH1Trace_smooth_ae Φ (radialPrimitiveTest Φ.bounded (Φ.map 1) j)] with θ hu ht
    rw [hu, ht, radial_primitive_trace Φ Φ.holomorphic j θ]
    have hz : Φ.map (unitCirclePt θ) ∈ closure Φ.domain := by
      rw [← localConformal_closedDisk_image_eq_closure Φ]
      exact mem_image_of_mem Φ.map (sphere_subset_closedBall
        (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))
    exact ((radialPrimitiveTest_near Φ.bounded (Φ.map 1) j hz).self_of_nhds).symm

/-- Actual L2 values of every completed primitive iterate retain the
factorial, full constant mode, and the physical boundary center. -/
theorem localConformalHardy_radial_primitive_value_ae :
    (h1Value Φ.domain (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) radialVekuaInput)) : ℂ → ℂ)
      =ᵐ[volume.restrict Φ.domain] fun z => conj (z - Φ.map 1) ^ j / (j.factorial : ℂ) := by
  rw [localConformalHardy_radial_primitive_eq Φ]
  exact radialPrimitiveTest_value_ae Φ.bounded Φ.lipschitzDomain.1.1 (Φ.map 1) j

/-- The actual physical H1 Vekua vector for the full zero Fourier mode
equals the actual centered radial Herglotz H1 vector. This equality comes
from the true completed H1 series and pointwise entire-wave series. -/
theorem localConformalVekuaH1_radial_eq_herglotz {E : ℝ}
    (hE : 0 < E) :
    Φ.vekuaH1AtBoundaryOrigin (E : ℂ) radialVekuaInput =
      herglotzWaveH1 Φ.bounded (isDirDensity_radialVekuaDensity (Real.sqrt E) (Φ.map 1))
        (Real.sqrt E) := by
  haveI : IsFiniteMeasure (volume.restrict Φ.domain) :=
    isFiniteMeasure_restrict.mpr Φ.bounded.measure_lt_top.ne
  let term  := fun j => physicalVekuaCoeff (E : ℂ) j •
    h1Value Φ.domain ((neumannH1AffineMultiplier Φ.bounded (Φ.map 1) ^ j)
      (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) radialVekuaInput)))
  have hs := (h1Value Φ.domain).hasSum (localConformalVekuaH1_hasSum Φ (Φ.map 1) (E : ℂ) radialVekuaInput)
  have ht (j : ℕ) : (term j : ℂ → ℂ) =ᵐ[volume.restrict Φ.domain]
      fun z => physicalVekuaCoeff (E : ℂ) j * (z - Φ.map 1) ^ j *
        radialPrimitivePolynomial (Φ.map 1) j z := by
    have hu := localConformalHardy_radial_primitive_value_ae Φ j
    have hm := radial_affine_value_ae Φ.bounded (Φ.map 1) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) radialVekuaInput))
      (radialPrimitivePolynomial (Φ.map 1) j) hu j
    filter_upwards [Lp.coeFn_smul (physicalVekuaCoeff (E : ℂ) j)
      (h1Value Φ.domain ((neumannH1AffineMultiplier Φ.bounded (Φ.map 1) ^ j)
        (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) radialVekuaInput)))), hm] with z hs hm
    change (physicalVekuaCoeff (E : ℂ) j •
      h1Value Φ.domain ((neumannH1AffineMultiplier Φ.bounded (Φ.map 1) ^ j)
        (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) radialVekuaInput)))) z = _
    simp only [Pi.smul_apply, smul_eq_mul, hs, hm]
    ring
  have hval := radial_Lp_series_ae term (h1Value Φ.domain (Φ.vekuaH1AtBoundaryOrigin (E : ℂ) radialVekuaInput))
    (fun j z => physicalVekuaCoeff (E : ℂ) j * (z - Φ.map 1) ^ j *
      radialPrimitivePolynomial (Φ.map 1) j z)
    (herglotzWave (Real.sqrt E) (radialVekuaDensity (Real.sqrt E) (Φ.map 1))) hs ht
    (fun j => ((continuous_const.mul ((continuous_id.sub continuous_const).pow j)).mul
      (radialPrimitivePolynomial_contDiff (Φ.map 1) j).continuous).aestronglyMeasurable)
    (radial_wave_hasSum hE (Φ.map 1))
  apply h1Value_injective Φ.lipschitzDomain.1.1
  apply Lp.ext
  rw [h1Value_herglotzWaveH1]
  filter_upwards [hval, (herglotzCoeff_memLp_domain Φ.bounded
    (isDirDensity_radialVekuaDensity (Real.sqrt E) (Φ.map 1)) (Real.sqrt E) 0).coeFn_toLp]
    with z hv hh
  exact hv.trans ((herglotzWave_eq _ _ z).trans hh.symm)

/-- The actual scaled radial density has its exact initial jet, including
the full zero component and the sqrt(2) convention of the jet space. -/
theorem localConformalRadial_scaled_herglotzVec_at_boundary_origin (E : ℝ) (a : ℂ) :
    herglotzVec (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (F 1) a)
      (Real.sqrt E) (F 1) = (a / vacuumWeight) • basisVec 0 := by
  simpa only [radialVekuaScaledDensity, antiPoly, Finset.sum_singleton, pow_zero, mul_one] using
    herglotzVec_centeredPolyDensity (Real.sqrt E) (F 1) {0} (fun _ => a)

/-- Arbitrary scalar multiples preserve the actual radial realization,
so the projected observation correction is a true zero-mode Vekua vector. -/
theorem localConformalVekuaH1_radial_smul_eq {E : ℝ}
    (hE : 0 < E) (a : ℂ) :
    Φ.vekuaH1AtBoundaryOrigin (E : ℂ) (a • radialVekuaInput) = a •
      herglotzWaveH1 Φ.bounded (isDirDensity_radialVekuaDensity (Real.sqrt E) (Φ.map 1))
        (Real.sqrt E) := by
  rw [map_smul, localConformalVekuaH1_radial_eq_herglotz Φ hE]

/-- Equality with the actual amplitude-a Herglotz H1 vector, rather than
merely equality of formal coefficients. -/
theorem localConformalVekuaH1_radial_smul_eq_herglotz {E : ℝ}
    (hE : 0 < E) (a : ℂ) :
    Φ.vekuaH1AtBoundaryOrigin (E : ℂ) (a • radialVekuaInput) =
      herglotzWaveH1 Φ.bounded (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (Φ.map 1) a)
        (Real.sqrt E) := by
  rw [localConformalVekuaH1_radial_smul_eq Φ hE]
  simpa [radialVekuaScaledDensity_eq_smul] using (radial_herglotzWaveH1_smul Φ.bounded Φ.lipschitzDomain.1.1
      (isDirDensity_radialVekuaDensity (Real.sqrt E) (Φ.map 1)) a (Real.sqrt E)).symm

/-- The actual coordinate trace of the radial completed vector equals the
ordinary centered Herglotz wave. No constant-speed property of Gamma is
used: Gamma is the true conformal circle trace. -/
theorem localConformalVekuaH1_radial_coordinate_trace_ae {E : ℝ}
    (hE : 0 < E) (a : ℂ) :
    ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1AtBoundaryOrigin (E : ℂ) (a • radialVekuaInput)) : ℝ → ℂ)
      =ᵐ[angleMeasure]
        fun θ => herglotzWave (Real.sqrt E)
          (radialVekuaScaledDensity (Real.sqrt E) (Φ.map 1) a) (Φ.boundary θ) := by
  rw [localConformalVekuaH1_radial_smul_eq_herglotz Φ hE]
  obtain ⟨f, hfu, hf⟩ := exists_radialWaveTest Φ.bounded Φ.lipschitzDomain.1.1
    (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (Φ.map 1) a) (Real.sqrt E)
  rw [← hfu]
  filter_upwards [localConformalDiskH1Trace_smooth_ae Φ f] with θ ht
  rw [ht, herglotzWave_eq]
  apply hf
  rw [← localConformal_closedDisk_image_eq_closure Φ]
  exact mem_image_of_mem Φ.map (sphere_subset_closedBall
    (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))

/-- The true derivative companion A of the radial Vekua series has the
actual smooth coefficient-one trace. This follows from the genuine
Wirtinger derivative in L2 and value injectivity in the real H1 graph. -/
theorem localConformalRadial_gradientA_coordinate_trace_ae {E : ℝ}
    (hE : 0 < E) :
    ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaGradientA (Φ.map 1) (E : ℂ) radialVekuaInput) : ℝ → ℂ)
      =ᵐ[angleMeasure]
        fun θ => -(Complex.I * (Real.sqrt E : ℂ) / 2) *
          herglotzCoeff (Real.sqrt E) (radialVekuaDensity (Real.sqrt E) (Φ.map 1)) 1 (Φ.boundary θ) := by
  let ρ  := radialVekuaDensity (Real.sqrt E) (Φ.map 1)
  let c  := -(Complex.I * (Real.sqrt E : ℂ) / 2)
  obtain ⟨f, hf⟩ := exists_radialCoeffTest Φ.bounded
    (isDirDensity_radialVekuaDensity (Real.sqrt E) (Φ.map 1)) (Real.sqrt E) 1
  have hAvalue : (h1Value Φ.domain (Φ.vekuaGradientA (Φ.map 1) (E : ℂ) radialVekuaInput) : ℂ → ℂ)
      =ᵐ[volume.restrict Φ.domain] fun z => c * herglotzCoeff (Real.sqrt E) ρ 1 z := by
    have hD : h1Value Φ.domain (Φ.vekuaGradientA (Φ.map 1) (E : ℂ) radialVekuaInput) =
        h1WirtingerD Φ.domain (Φ.vekuaH1AtBoundaryOrigin (E : ℂ) radialVekuaInput) := by
      rw [localConformalVekuaGradientA_apply, map_smul]
      exact (localConformalVekuaH1_wirtingerD Φ (Φ.map 1) (E : ℂ) radialVekuaInput).symm
    rw [hD, localConformalVekuaH1_radial_eq_herglotz Φ hE]
    exact radial_herglotzWirtingerD_ae Φ.bounded
      (isDirDensity_radialVekuaDensity (Real.sqrt E) (Φ.map 1)) (Real.sqrt E)
  have hA : Φ.vekuaGradientA (Φ.map 1) (E : ℂ) radialVekuaInput = c • smoothTraceH1 Φ.domain f := by
    apply h1Value_injective Φ.lipschitzDomain.1.1
    rw [map_smul, h1Value_smoothTraceH1]
    apply Lp.ext
    filter_upwards [hAvalue, Lp.coeFn_smul c ((smoothTraceTests_memLp Φ.domain f).toLp _),
      (smoothTraceTests_memLp Φ.domain f).coeFn_toLp,
      ae_restrict_mem Φ.lipschitzDomain.1.1.measurableSet] with z ha hs hfv hz
    simp only [Pi.smul_apply, smul_eq_mul, ha, hs, hfv,
      hf z (subset_closure hz), ρ]
  rw [hA, map_smul]
  filter_upwards [Lp.coeFn_smul c ((Φ.pulledBackTrace Φ.lipschitzDomain) (smoothTraceH1 Φ.domain f)),
    localConformalDiskH1Trace_smooth_ae Φ f] with θ hs ht
  simp only [Pi.smul_apply, smul_eq_mul, hs, ht]
  have hz : Φ.map (unitCirclePt θ) ∈ closure Φ.domain := by
    rw [← localConformal_closedDisk_image_eq_closure Φ]
    exact mem_image_of_mem Φ.map (sphere_subset_closedBall
      (circleMap_mem_sphere (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ))
  solve_by_elim

/-- The actual radial conormal belongs to genuine parameter L2 even for
the variable-speed conformal circle trace. This is a property of this
constructed smooth wave, not a gain for arbitrary normalized loads. -/
theorem localConformalRadial_conormal_memLp {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F)) (E : ℝ) (a : ℂ) :
    MemLp (herglotzConormal (Real.sqrt E)
      (radialVekuaScaledDensity (Real.sqrt E) (F 1) a) (physicalCircleTrace F)) 2
      angleMeasure :=
  memLp_herglotzConormal
    (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (F 1) a) (Real.sqrt E) hΓLip

/-- The true radial conormal has precisely the missing cut direction in
the original observation adjoint: amplitude one gives i times cutC. -/
theorem localConformalRadial_observationAdj_conormal {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F)) {E : ℝ} {W : TransportPath}
    (hW : IsTransport (physicalCircleTrace F) E W) (a : ℂ) :
    observationAdj W (herglotzConormal (Real.sqrt E)
      (radialVekuaScaledDensity (Real.sqrt E) (F 1) a) (physicalCircleTrace F)) =
        (Complex.I * a) • cutVector W := by
  have hclosed : (physicalCircleTrace F) anglePeriod = (physicalCircleTrace F) 0 := by
    simpa only [zero_add] using physicalCircleTrace_periodic F 0
  have hbase : (physicalCircleTrace F) 0 = F 1 := by
    simp [physicalCircleTrace, circleMap_zero]
  rw [(herglotzForm_eq hΓLip hclosed hW
    (isDirDensity_radialVekuaScaledDensity (Real.sqrt E) (F 1) a)).1,
    hbase, localConformalRadial_scaled_herglotzVec_at_boundary_origin,
    map_smul, smul_smul]
  change ((vacuumWeight * Complex.I) * (a / vacuumWeight)) •
      cutVector W = _
  have h2 : vacuumWeight ≠ 0 := by
    simp
  field_simp [h2]
  -- `field_simp` closes the scalar identity after clearing the nonzero square root.

/-- The genuine variable-speed coordinate conormal as an ordinary L2
class. Its measure is dtheta and its velocity is the actual Gamma'. -/
def localConformalRadialCoordinateLoad {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F)) (E : ℝ) (a : ℂ) : BoundaryL2 :=
  (localConformalRadial_conormal_memLp F hΓLip E a).toLp
    (herglotzConormal (Real.sqrt E) (radialVekuaScaledDensity (Real.sqrt E) (F 1) a) (physicalCircleTrace F))

theorem localConformalRadialCoordinateLoad_ae {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F)) (E : ℝ) (a : ℂ) :
    (localConformalRadialCoordinateLoad F hΓLip E a : ℝ → ℂ)
      =ᵐ[angleMeasure]
        herglotzConormal (Real.sqrt E)
          (radialVekuaScaledDensity (Real.sqrt E) (F 1) a) (physicalCircleTrace F) :=
  (localConformalRadial_conormal_memLp F hΓLip E a).coeFn_toLp

theorem localConformalRadialCoordinateLoad_smul {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F)) (E : ℝ) (a : ℂ) :
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
  simp

/-- The actual ordinary L2 representative retains exactly the original
observation adjoint, including the boundary-origin cut direction. -/
theorem localConformalRadialCoordinateLoad_observationAdj {L : NNReal}
    (hΓLip : LipschitzWith L (physicalCircleTrace F)) {E : ℝ} {W : TransportPath}
    (hW : IsTransport (physicalCircleTrace F) E W) (a : ℂ) :
    observationAdj W (localConformalRadialCoordinateLoad F hΓLip E a : ℝ → ℂ) =
      (Complex.I * a) • cutVector W := by
  rw [← localConformalRadial_observationAdj_conormal F hΓLip hW a]
  rw [observationAdj, observationAdj,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  apply integral_congr_ae
  filter_upwards [localConformalRadialCoordinateLoad_ae F hΓLip E a] with θ hθ
  rw [hθ]

private theorem radial_normalizedConormal_eq_coordinateLoad_one {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {E : ℝ} (hE : 0 < E) :
    Φ.conormal (E : ℂ) radialVekuaInput =
      sobolevSmoothing halfOrder (by norm_num)
        (boundaryFourier (localConformalRadialCoordinateLoad Φ.map hΓLip E 1)) := by
  let ρ  := radialVekuaDensity (Real.sqrt E) (Φ.map 1)
  let c  := -(Complex.I * (Real.sqrt E : ℂ) / 2)
  let f  := fun θ => herglotzCoeff (Real.sqrt E) ρ 0 (Φ.boundary θ)
  let df  := fun θ => c *
    (deriv Φ.boundary θ * herglotzCoeff (Real.sqrt E) ρ 1 (Φ.boundary θ) +
      conj (deriv Φ.boundary θ) * herglotzCoeff (Real.sqrt E) ρ (-1) (Φ.boundary θ))
  let A  := (boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)) ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaGradientA (Φ.map 1) (E : ℂ) radialVekuaInput))
  let r  := localConformalRadialCoordinateLoad Φ.map hΓLip E 1
  let d  := (2 : ℂ) • A - Complex.I • r
  have hA : (A : ℝ → ℂ) =ᵐ[angleMeasure]
      fun θ => deriv Φ.boundary θ * (c * herglotzCoeff (Real.sqrt E) ρ 1 (Φ.boundary θ)) := by
    filter_upwards [boundaryContinuousMultiplier_ae (localConformalVelocityCircle Φ.map)
        ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaGradientA (Φ.map 1) (E : ℂ) radialVekuaInput)),
      localConformalRadial_gradientA_coordinate_trace_ae Φ hE] with θ hm ha
    rw [hm, ha, localConformalVelocityCircle_apply Φ]
  have hd : (d : ℝ → ℂ) =ᵐ[angleMeasure] df := by
    filter_upwards [Lp.coeFn_sub ((2 : ℂ) • A) (Complex.I • r),
      Lp.coeFn_smul (2 : ℂ) A, Lp.coeFn_smul Complex.I r, hA,
      localConformalRadialCoordinateLoad_ae Φ.map hΓLip E 1] with θ hs h2 hi ha hr
    simp only [d, r, hs, h2, hi, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha, hr,
      radialVekuaScaledDensity_one, herglotzConormal_eq
        (isDirDensity_radialVekuaDensity (Real.sqrt E) (Φ.map 1)).intervalIntegrable, df, c, ρ]
    ring_nf
  have ht : ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1AtBoundaryOrigin (E : ℂ) radialVekuaInput) : ℝ → ℂ)
      =ᵐ[angleMeasure] f := by
    simpa only [one_smul, radialVekuaScaledDensity_one, herglotzWave_eq, f, ρ] using
      localConformalVekuaH1_radial_coordinate_trace_ae Φ hE 1
  have hdf (θ : ℝ) : HasDerivAt f (df θ) θ := by
    have h := (differentiable_herglotzCoeff
      (isDirDensity_radialVekuaDensity (Real.sqrt E) (Φ.map 1)).intervalIntegrable
        (Real.sqrt E) 0 (Φ.boundary θ)).hasFDerivAt.comp_hasDerivAt θ
          (Φ.boundaryC1.differentiable_one θ).hasDerivAt
    simpa only [f, df, c, ρ, Function.comp_def,
      fderiv_herglotzCoeff_apply
        (isDirDensity_radialVekuaDensity (Real.sqrt E) (Φ.map 1)).intervalIntegrable,
      zero_add, zero_sub] using h
  have hdc : Continuous df := by
    exact continuous_const.mul
      ((Φ.boundaryC1.continuous_deriv_one.mul
        ((continuous_herglotzCoeff
          (isDirDensity_radialVekuaDensity (Real.sqrt E) (Φ.map 1)).intervalIntegrable
            (Real.sqrt E) 1).comp Φ.boundaryC1.continuous)).add
        ((Complex.continuous_conj.comp Φ.boundaryC1.continuous_deriv_one).mul
          ((continuous_herglotzCoeff
            (isDirDensity_radialVekuaDensity (Real.sqrt E) (Φ.map 1)).intervalIntegrable
              (Real.sqrt E) (-1)).comp Φ.boundaryC1.continuous)))
  have hp : f 0 = f anglePeriod := by
    have hclosed : Φ.boundary anglePeriod = Φ.boundary 0 := by
      simpa only [zero_add] using Φ.periodic_boundary 0
    simp [f, hclosed]
  have hcoeff (n : ℤ) : boundaryFourier d n =
      (Complex.I * (n : ℂ)) * boundaryFourier ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1AtBoundaryOrigin (E : ℂ) radialVekuaInput)) n := by
    rw [kernel_conormal_coeff_ae d hd n,
      kernel_conormal_coeff_ae _ ht n, fourierCoeffOn_deriv hdf hdc hp n]
    ring
  apply lp.ext
  funext n
  have hn := hcoeff n
  simp only [d, map_sub, map_smul, lp.coeFn_sub, Pi.sub_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hn
  have hi := congrArg (fun z : ℂ => Complex.I * z) hn
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_one_mul] at hi
  rw [localConformalVekua_normalizedConormal_fourier Φ (E : ℂ) radialVekuaInput radialVekuaInput_nonpositive
      radialVekuaInput_raw_H1 n]
  
  change ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) *
      (-(n : ℂ) * boundaryFourier ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaH1AtBoundaryOrigin (E : ℂ) radialVekuaInput)) n -
        2 * Complex.I * boundaryFourier A n) =
    ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) * boundaryFourier r n
  linear_combination -((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) * hi

/-- The genuine normalized conormal of every scalar full zero mode is
exactly the half-smoothed unitary Fourier transform of its actual L2
radial conormal, including the zero mode and variable circle speed. -/
theorem localConformalRadial_normalizedConormal_eq_coordinateLoad {L : NNReal}
    (hΓLip : LipschitzWith L Φ.boundary) {E : ℝ} (hE : 0 < E) (a : ℂ) :
    Φ.conormal (E : ℂ) (a • radialVekuaInput) =
      sobolevSmoothing halfOrder (by norm_num)
        (boundaryFourier (localConformalRadialCoordinateLoad Φ.map hΓLip E a)) := by
  rw [map_smul, radial_normalizedConormal_eq_coordinateLoad_one Φ hΓLip hE]
  have hload := localConformalRadialCoordinateLoad_smul (F := Φ.map) hΓLip E a
  rw [hload]
  simp only [map_smul]

end

end PhysicalCoordinates

end PolyaNeumann

end
