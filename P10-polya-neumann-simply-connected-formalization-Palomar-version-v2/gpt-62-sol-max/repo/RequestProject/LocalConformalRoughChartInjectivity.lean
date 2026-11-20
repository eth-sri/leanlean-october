module

public import RequestProject.ConformalDiskCoordinates

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import RequestProject.RoughVekuaTransport
public import RequestProject.HardyMoments
public import RequestProject.LocalConformalReducedCoercivity
public import RequestProject.LocalConformalFourierComplement
public import RequestProject.LocalConformalRoughGaugeRegularity

/-!
# Actual rough observation kernels in finite Fourier conormal charts

A genuine Hardy gauge differs from the negative imaginary multiple of
the rough periodic primitive by an actual H1 correction. The positive
primitive therefore has H1 Fourier coefficients. Finite Fourier chart
corrections then give half-order regularity of the full normalized load,
which permits the true L2 conormal realization and chart injectivity.

The final supplied-coordinate wrappers use the constructed rough driven
gauge; they do not assume regularity or Hardy support of the unknown
normalized load.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ComplexConjugate

local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
local notation "H₀" => nonpositiveFourierSubspace

private theorem rough_chart_posProj_eq_zero_of_nonpositive (b : L2Z)
    (hb : IsNonpositiveFourierSupport (b : ℤ → ℂ)) : posProj b = 0 := by
  apply lp.ext
  funext n
  by_cases hn : 0 < n
  · simp  [posProj, diagOp_apply, hb n hn, mul_zero,
      lp.coeFn_zero, Pi.zero_apply]
  · simp  [posProj, if_neg hn, zero_mul]

section

variable (y : L2Z) (H K : BoundaryL2) (hH : IsNonpositiveFourierSupport (boundaryFourier H : ℤ → ℂ)) (hK : IsSobolevSeq 1 (boundaryFourier K : ℤ → ℂ))
include y H K hH hK

/-- A true L2 Hardy split controls the positive rough primitive. This
This lemma concerns actual boundary vectors and uses no endpoint value. -/
theorem roughNormalizedPrimitive_pos_one_of_hardy_split
    
    (hsplit : H = -Complex.I • roughNormalizedPrimitive y + K) :
    IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ) := by
  let p := posProj (boundaryFourier (roughNormalizedPrimitive y))
  let k := posProj (boundaryFourier K)
  have hzero := rough_chart_posProj_eq_zero_of_nonpositive (boundaryFourier H) hH
  have hs := congrArg (fun B : BoundaryL2 => posProj (boundaryFourier B)) hsplit
  change posProj (boundaryFourier H) =
    posProj (boundaryFourier (-Complex.I • roughNormalizedPrimitive y + K)) at hs
  rw [hzero, map_add, map_smul, map_add, map_smul] at hs
  change (0 : L2Z) = -Complex.I • p + k at hs
  have hi := congrArg (fun B : L2Z => Complex.I • B) hs
  simp  [smul_zero, smul_add, smul_smul, mul_neg,
    Complex.I_mul_I, neg_neg, one_smul] at hi
  have hp : p = -Complex.I • k := by
    have h := eq_neg_of_add_eq_zero_left hi.symm
    simpa only [neg_smul] using h
  change p ∈ fourierSobolevSubmodule 1
  rw [hp]
  exact (fourierSobolevSubmodule 1).smul_mem _ (isSobolevSeq_posProj hK)

theorem roughNormalizedPrimitive_pos_one_of_hardy_split_ae
    
    (hsplit : (H : ℝ → ℂ) =ᵐ[μB]
      (fun θ => -Complex.I * roughNormalizedPrimitive y θ + K θ)) :
    IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ) := by
  apply roughNormalizedPrimitive_pos_one_of_hardy_split y H K hH hK
  apply Lp.ext
  filter_upwards [hsplit, Lp.coeFn_add (-Complex.I • roughNormalizedPrimitive y) K,
    Lp.coeFn_smul (-Complex.I) (roughNormalizedPrimitive y)] with θ hs ha hm
  simp_all

end

/-- Raw H1 correction coefficients give the actual unitary Fourier H1
vector; the ordinary-measure sqrt(2pi) normalization is retained. -/
theorem boundaryFourier_toLp_sobolev_one_of_coefficients
    {K : ℝ → ℂ} (hK : MemLp K 2 μB)
    (hK1 : IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos K)) :
    IsSobolevSeq 1 (boundaryFourier (hK.toLp K) : ℤ → ℂ) := by
  have heq : (boundaryFourier (hK.toLp K) : ℤ → ℂ) =
      (Real.sqrt (2 * Real.pi) : ℂ) • fourierCoeffOn Real.two_pi_pos K := by
    funext n
    rw [boundaryFourier_apply,
      fourierCoeffOn_congr_ae Real.two_pi_pos hK.coeFn_toLp]
    rfl
  rw [heq]
  exact isSobolevSeq_smul _ hK1

/-- Actual raw L2 gauges and corrections can be passed to the boundary
vector split without introducing pointwise periodicity of the gauge. -/
theorem roughNormalizedPrimitive_pos_one_of_raw_hardy_split
    (y : L2Z) (H K : ℝ → ℂ) (hH2 : MemLp H 2 μB) (hK2 : MemLp K 2 μB)
    (hH : IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H))
    (hK1 : IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos K))
    (hsplit : H =ᵐ[μB] fun θ => -Complex.I * roughNormalizedPrimitive y θ + K θ) :
    IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ) := by
  have hHB : IsNonpositiveFourierSupport (boundaryFourier (hH2.toLp H) : ℤ → ℂ) := by
    intro n hn
    rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hH2.coeFn_toLp,
      hH n hn, mul_zero]
  apply roughNormalizedPrimitive_pos_one_of_hardy_split_ae y (hH2.toLp H) (hK2.toLp K)
    hHB (boundaryFourier_toLp_sobolev_one_of_coefficients hK2 hK1)
  filter_upwards [hH2.coeFn_toLp, hK2.coeFn_toLp, hsplit] with θ hh hk hs
  simp_all

section PhysicalCoordinates

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

local notation "ΓF" => physicalCircleTrace F
local notation "hβF" => localConformalVelocityCircle_isWL1_half coords.one_lt_radius F coords.smooth
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 coords.one_lt_radius F coords.smooth
local notation "hgF" => localConformalCenteredCircle_isWL1_half coords.one_lt_radius F coords.smooth
local notation "NF" => normalizedConormal hβF haF hgF

/-- The genuine rough driven gauge is Hardy for every normalized
observation-kernel input. The moments come from the actual positive-row
ODE and factorial tails, and the Hardy conclusion uses the true L2
physical moment criterion. -/
theorem localConformal_roughGauge_exists_nonpositive_of_projObsDual_eq_zero
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (y : L2Z) (hy : projObsDual W y = 0) :
    ∃ α : ℂ,
      roughVekuaRegularCorrection ΓF E W (roughNormalizedPrimitive y) (roughNormalizedMean y)
        α (2 * Real.pi) = α • basisVec 0 ∧
      MemLp (physicalDrivenGauge ΓF E
        (roughVekuaDrivenVector ΓF E W (roughNormalizedPrimitive y) (roughNormalizedMean y) α) 0)
        2 μB ∧
      IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos
        (physicalDrivenGauge ΓF E
          (roughVekuaDrivenVector ΓF E W (roughNormalizedPrimitive y) (roughNormalizedMean y) α) 0)) := by
  have hΓ :=
    contDiff_physicalCircleTrace_of_neighborhood coords.one_lt_radius F (coords.smooth.of_le (by simp))
  obtain ⟨α, hα0, hαT⟩ :=
    roughVekuaRegularCorrection_exists_periodic_of_projObsDual_eq_zero hΓLip hΓ hW y hy
  have hH2 := roughVekuaGauge_zero_memLp hΓLip hΓ hW
    (roughNormalizedPrimitive y) (roughNormalizedMean y) α
  refine ⟨α, hαT, hH2, ?_⟩
  apply localConformal_physicalMoments_nonpositive coords _ (intervalIntegrable_boundary_of_memLp _ hH2)
  intro k
  have hm := roughVekuaGauge_physicalMoment_eq_zero hΓLip hΓ hW
    (roughNormalizedPrimitive y) (roughNormalizedMean y) α hE hαT 0 k
  simpa only [physicalDrivenMoment, physicalDrivenCentered, map_sub, mul_assoc] using hm

/-- Original normalized observation nullity gives the positive primitive
H1 regularity. Every gauge and Sobolev fact used here is constructed from
the true rough driven equation. -/
theorem localConformal_roughProjectedObservation_primitive_pos_one
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (y : L2Z) (hy : projObsDual W y = 0) :
    IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ) := by
  have hΓ :=
    contDiff_physicalCircleTrace_of_neighborhood coords.one_lt_radius F (coords.smooth.of_le (by simp))
  obtain ⟨α, hαT, hH2, hHn⟩ :=
    localConformal_roughGauge_exists_nonpositive_of_projObsDual_eq_zero
      coords hΓLip hE hW y hy
  have hK2 := roughVekuaGauge_regular_memLp hΓLip hΓ hW
    (roughNormalizedPrimitive y) (roughNormalizedMean y) α 0
  have hK1 := roughVekuaGauge_regular_isSobolevSeq_one hΓLip hΓ hW
    (roughNormalizedPrimitive y) (roughNormalizedMean y) α hαT
  apply roughNormalizedPrimitive_pos_one_of_raw_hardy_split y _ _ hH2 hK2 hHn hK1
  exact Eventually.of_forall (roughVekuaGauge_zero_split
    (roughNormalizedPrimitive y) (roughNormalizedMean y) α)

theorem localConformal_finiteFourierChart_projectedObservation_injective
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    {d : ℕ} (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (hunit : IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
      (finiteFourierChart u v) ∘L H₀ᗮ.orthogonalProjection)) :
    Function.Injective ((projObsDual W).comp (finiteFourierChart u v)) := by
  apply (injective_iff_map_eq_zero _).2
  intro z hz
  have hreg := localConformal_roughProjectedObservation_primitive_pos_one coords hΓLip hE hW _ hz
  exact localConformal_fixed_complement_half_regular_kernel_eq_zero coords hΓLip hE hW
    (finiteFourierChart u v) hunit z (finiteFourierChart_half_of_rough_primitive_pos_one u v hv z hreg).1 hz

/-- A genuine nonzero reference cut supplies an actual finite Fourier
complement with full normalized projected-observation injectivity. No
half-order hypothesis is added to its chart inputs. -/
theorem exists_localConformal_fixed_fourier_complement_projectedObservation_injective
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E₀ : ℝ} (hE₀ : 0 < E₀)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E₀ W)
    (hcut : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → L2Z),
      Function.Injective ((projObsDual W).comp (finiteFourierChart u v)) ∧
      ∃ U ∈ 𝓝 E₀,
        ∀ E ∈ U, IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
          (finiteFourierChart u v) ∘L H₀ᗮ.orthogonalProjection) := by
  have hinj : Function.Injective ((NF (E₀ : ℂ)).comp (H₀).subtypeL) := fun b d hbd =>
    Subtype.ext (localConformalVekuaConormal_injective_on_nonpositive_of_cutC_ne_zero coords E₀
      hE₀.le hW hcut b.property d.property hbd)
  obtain ⟨d, u, v, hv, hunit⟩ := normalizedConormal_fixed_fourier_complement hβF haF hgF hinj
  exact ⟨d, u, v, localConformal_finiteFourierChart_projectedObservation_injective
    coords hΓLip hE₀ hW u v hv hunit.self_of_nhds, _, hunit, fun _ h => h⟩

end PhysicalCoordinates

end PolyaNeumann

end
