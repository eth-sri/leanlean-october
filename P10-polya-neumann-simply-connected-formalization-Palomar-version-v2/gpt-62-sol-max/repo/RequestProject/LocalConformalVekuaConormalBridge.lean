module

public import RequestProject.CircleFourier
public import RequestProject.ConformalDiskCoordinates

public import RequestProject.LocalConformalVekuaConormal
public import RequestProject.LocalConformalVekuaTrace
public import RequestProject.DiskWeakModes

/-!
# Identification of the actual Vekua flux and the Fourier conormal remainder

The physical velocity multipliers are transported by the genuine arclength
Jacobian on dense smooth H¹ restrictions. Both sides are continuous trace
pairings, so the identity extends to actual H¹ vectors. The supplied H¹
inverse and actual harmonic disk tests separate the half-trace pairings.
Consequently the normalized physical flux is the half-smoothed unitary
Fourier transform of the actual coordinate flux. Its convergent trace
series is then exactly the existing conormal remainder operator.

The center is F(1); the averaged multiplier coefficients and ordinary
dθ Fourier normalization are retained. Existence of the supplied coordinates
is separate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology InnerProductSpace ComplexConjugate

/-- The actual continuous nonconjugate angular velocity of F on the circle. -/
def localConformalVelocityCircle (F : ℂ → ℂ) : C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨fun q => conj (localConformalPrimitiveCircle F q),
    Complex.continuous_conj.comp (localConformalPrimitiveCircle F).continuous⟩

section

variable {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
include R hR F hFs

theorem localConformalVelocityCircle_apply  (θ : ℝ) :
    localConformalVelocityCircle F (θ : AddCircle (2 * Real.pi)) =
      deriv (physicalCircleTrace F) θ := by
  change conj (localConformalPrimitiveCircle F (θ : AddCircle (2 * Real.pi))) = _
  rw [localConformalPrimitiveCircle_apply hR F hFs, Complex.conj_conj]

theorem localConformalVelocityCircle_coeff  :
    fourierCoeff (localConformalVelocityCircle F) =
      fourierCoeffOn Real.two_pi_pos (deriv (physicalCircleTrace F)) := by
  rw [fourierCoeff_eq_on_circle]
  congr 1
  exact funext (localConformalVelocityCircle_apply hR F hFs)

theorem localConformalVelocityCircle_isWL1_half  :
    IsWL1 (1 / 2 : ℝ) (fourierCoeff (localConformalVelocityCircle F)) := by
  rw [localConformalVelocityCircle_coeff hR F hFs]
  exact IsWL1.mono (by norm_num)
    (periodic_contDiff_four_fourier_weights
      (contDiff_physicalCircleTrace_four_of_neighborhood hR F
        (hFs.of_le (WithTop.coe_le_coe.mpr le_top)))
      (physicalCircleTrace_periodic F)).1

end

section

variable {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (conjugated : Bool)
include Ω γ hγ conjugated

private def bridge_physicalVelocity  : BoundaryL2 →L[ℂ] BoundaryL2 :=
  let B : NNReal := Classical.choose hγ.lipschitz
  let hB : LipschitzWith B γ := Classical.choose_spec hγ.lipschitz
  lpBoundedMultiplier
    (fun θ => if conjugated then conj (deriv γ θ) else deriv γ θ)
    (by cases conjugated
        · simpa using (measurable_deriv γ).aestronglyMeasurable.restrict
        · simpa using (Complex.continuous_conj.comp_aestronglyMeasurable
            (measurable_deriv γ).aestronglyMeasurable).restrict)
    (Eventually.of_forall fun θ => by
      cases conjugated <;> simpa using
        (norm_deriv_le_of_lipschitz hB : ‖deriv γ θ‖ ≤ B))

private theorem bridge_physicalVelocity_ae  (g : BoundaryL2) :
    (bridge_physicalVelocity hγ conjugated g : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))]
      fun θ => (if conjugated then conj (deriv γ θ) else deriv γ θ) * g θ :=
  lpBoundedMultiplier_ae _ _ _ g

end

section CoordinatePairing

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "TF" => coords.trace
local notation "TP" => h1BoundaryTrace coords.bounded coords.lipschitz hγ

include coords hγ hτ hcoord in
private theorem bridge_velocity_jacobian (conjugated : Bool) :
    (fun θ : ℝ => if conjugated then
        localConformalPrimitiveCircle F (θ : AddCircle (2 * Real.pi)) else
        localConformalVelocityCircle F (θ : AddCircle (2 * Real.pi))) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))]
      fun θ => deriv τ θ •
        (if conjugated then conj (deriv γ (τ θ)) else deriv γ (τ θ)) := by
  obtain ⟨B, hB⟩ := hγ.lipschitz
  obtain ⟨D, hD⟩ := hτ.lipschitz
  have hchain := (ae_deriv_comp hB hτ.monotone hD).filter_mono
    (ae_restrict_le : ae (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) ≤ ae volume)
  have he : γ ∘ τ = physicalCircleTrace F := funext fun θ => (hcoord θ).symm
  rw [he] at hchain
  filter_upwards [hchain] with θ hθ
  cases conjugated <;> simp only [Bool.false_eq_true, ↓reduceIte,
    localConformalPrimitiveCircle_apply coords.one_lt_radius F coords.smooth,
    localConformalVelocityCircle_apply coords.one_lt_radius F coords.smooth, hθ,
    Complex.real_smul, map_mul, Complex.conj_ofReal]

include hτ hcoord in
/-- The actual velocity multiplier is transported by the conormal Jacobian. -/
private theorem bridge_velocity_pairing (conjugated : Bool) (w u : NeumannH1 ΩF) :
    ⟪TP w, bridge_physicalVelocity hγ conjugated (TP u)⟫_ℂ =
      ⟪TF w, boundaryContinuousMultiplier
        (if conjugated then localConformalPrimitiveCircle F else
          localConformalVelocityCircle F) (TF u)⟫_ℂ := by
  let M := bridge_physicalVelocity hγ conjugated
  let A := if conjugated then localConformalPrimitiveCircle F else localConformalVelocityCircle F
  let N := boundaryContinuousMultiplier A
  change ⟪TP w, M (TP u)⟫_ℂ = ⟪TF w, N (TF u)⟫_ℂ
  refine (denseRange_smoothTraceH1Lin coords.bounded coords.lipschitz).induction_on
    (p := fun v => ⟪TP w, M (TP v)⟫_ℂ = ⟪TF w, N (TF v)⟫_ℂ) u
    (isClosed_eq (continuous_const.inner (M.comp TP).continuous)
      (continuous_const.inner (N.comp TF).continuous)) ?_
  intro f
  rw [smoothTraceH1Lin_apply]
  let v := smoothTraceH1 ΩF f
  have he : traceReparamConormalL2 hτ (M (TP v)) = N (TF v) := by
    apply Lp.ext
    filter_upwards [traceReparamConormalL2_ae hτ (M (TP v)),
      isC1TraceReparam_ae_comp hτ (bridge_physicalVelocity_ae hγ conjugated (TP v)),
      isC1TraceReparam_ae_comp hτ (h1BoundaryTrace_smooth_ae coords.bounded coords.lipschitz hγ f),
      boundaryContinuousMultiplier_ae A (TF v), localConformalDiskH1Trace_smooth_ae coords f,
      bridge_velocity_jacobian coords hγ hτ hcoord conjugated] with θ ht hm ht₁ hn ht₂ hj
    change (traceReparamConormalL2 hτ (M (TP v))) θ = (N (TF v)) θ
    rw [ht, hm, ht₁, hn, ht₂, hcoord]
    have hA : A (θ : AddCircle (2 * Real.pi)) = deriv τ θ •
        (if conjugated then conj (deriv γ (τ θ)) else deriv γ (τ θ)) := by
      cases conjugated <;> simpa [A] using hj
    rw [hA]
    simp only [Complex.real_smul]
    ring
  rw [← he, ← localConformalDiskH1Trace_eq_reparam coords hγ hτ hcoord]
  exact (h1ReparamBoundaryTrace_inner_conormalL2 coords.bounded coords.lipschitz hγ hτ w _).symm

end CoordinatePairing

section VekuaCoordinates

variable {R C : ℝ}
    (hR : 1 < R)
    (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (coords : ConformalDiskCoordinates F)

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "UF" => localConformalHardyH1Extension coords
local notation "JF" => localConformalHardyPrimitive coords.one_lt_radius F coords.smooth
local notation "MF" => neumannH1AffineMultiplier coords.bounded (F 1)
local notation "TF" => coords.trace
local notation "QF" => coords.halfTrace
local notation "AF" => localConformalVekuaGradientA coords
local notation "BF" => localConformalVekuaGradientB coords
local notation "βF" => fourierCoeff (localConformalVelocityCircle F)
local notation "aF" => localConformalHardyPrimitiveMultiplier F
local notation "gF" => fourierCoeff (localConformalCenteredCircle coords.one_lt_radius F coords.smooth)
local notation "hβF" => localConformalVelocityCircle_isWL1_half coords.one_lt_radius F coords.smooth
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 coords.one_lt_radius F coords.smooth
local notation "hgF" => localConformalCenteredCircle_isWL1_half coords.one_lt_radius F coords.smooth

section

variable {F}
include coords

/-- The genuine coordinate flux; its two inputs are the actual H¹ gradient
representatives. The variable circle speed is included in its velocities. -/
def localConformalVekuaCoordinateConormalRemainder (E : ℂ) : L2Z →L[ℂ] BoundaryL2 :=
  (-Complex.I) • ((boundaryContinuousMultiplier (localConformalVelocityCircle F)).comp
      ((TF).comp (AF (F 1) E))) +
    Complex.I • ((boundaryContinuousMultiplier (localConformalPrimitiveCircle F)).comp
      ((TF).comp (BF (F 1) E)))

end

local notation "CCF" => localConformalVekuaCoordinateConormalRemainder coords

section

variable {F}
include coords

/-- The actual conformal half trace separates L² coefficient vectors.
This uses genuine harmonic tests and the constructed H¹ inverse. -/
theorem localConformalDiskHalfTrace_separates (x y : L2Z)
    (hxy : ∀ w : NeumannH1 ΩF, ⟪QF w, x⟫_ℂ = ⟪QF w, y⟫_ℂ) : x = y := by
  apply lp.ext
  funext n
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · have h := hxy (localConformalH1Pushforward coords (diskHolomorphicH1Test m))
    change ⟪diskHalfTrace (coords.pullback _), x⟫_ℂ =
      ⟪diskHalfTrace (coords.pullback _), y⟫_ℂ at h
    rw [localConformalH1Pullback_pushforward, diskHalfTrace_holomorphicTest,
      inner_smul_left, inner_smul_left, inner_stdBasisZ, inner_stdBasisZ] at h
    exact mul_left_cancel₀ (by
      simp only [map_mul, Complex.conj_ofReal]
      exact mul_ne_zero
        (by exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos (m : ℤ))).ne')
        (by exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne')) h
  · have h := hxy (localConformalH1Pushforward coords (diskAntiholomorphicH1Test m))
    change ⟪diskHalfTrace (coords.pullback _), x⟫_ℂ =
      ⟪diskHalfTrace (coords.pullback _), y⟫_ℂ at h
    rw [localConformalH1Pullback_pushforward, diskHalfTrace_antiholomorphicTest,
      inner_smul_left, inner_smul_left, inner_stdBasisZ, inner_stdBasisZ] at h
    exact mul_left_cancel₀ (by
      simp only [map_mul, Complex.conj_ofReal]
      exact mul_ne_zero
        (by exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos (-(m : ℤ)))).ne')
        (by exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne')) h

end

variable {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

section

variable {F}
include coords

private theorem bridge_physicalFlux_split (E : ℂ) (b : L2Z) :
    localConformalVekuaConormalRemainder coords hγ (F 1) E b =
      (-Complex.I) • bridge_physicalVelocity hγ false
        (h1BoundaryTrace coords.bounded coords.lipschitz hγ (AF (F 1) E b)) +
        Complex.I • bridge_physicalVelocity hγ true
          (h1BoundaryTrace coords.bounded coords.lipschitz hγ (BF (F 1) E b)) := by
  apply Lp.ext
  filter_upwards [localConformalVekuaConormalRemainder_ae coords hγ (F 1) E b,
    Lp.coeFn_add
      ((-Complex.I) • bridge_physicalVelocity hγ false
        (h1BoundaryTrace coords.bounded coords.lipschitz hγ (AF (F 1) E b)))
      (Complex.I • bridge_physicalVelocity hγ true
        (h1BoundaryTrace coords.bounded coords.lipschitz hγ (BF (F 1) E b))),
    Lp.coeFn_smul (-Complex.I) (bridge_physicalVelocity hγ false
      (h1BoundaryTrace coords.bounded coords.lipschitz hγ (AF (F 1) E b))),
    Lp.coeFn_smul Complex.I (bridge_physicalVelocity hγ true
      (h1BoundaryTrace coords.bounded coords.lipschitz hγ (BF (F 1) E b))),
    bridge_physicalVelocity_ae hγ false (h1BoundaryTrace coords.bounded coords.lipschitz hγ (AF (F 1) E b)),
    bridge_physicalVelocity_ae hγ true (h1BoundaryTrace coords.bounded coords.lipschitz hγ (BF (F 1) E b))]
    with θ hc ha hA hB hv hvc
  rw [hc, ha]
  simp only [Pi.add_apply, hA, hB, Pi.smul_apply, hv, hvc,
    Bool.false_eq_true, ↓reduceIte]
  ring

include hcoord in
/-- The actual normalized physical remainder is the half-smoothed Fourier
transform of the actual coordinate flux. The Jacobian is proved, not assumed. -/
theorem localConformalVekuaNormalizedConormalRemainder_eq_coordinate (E : ℂ) (b : L2Z) :
    localConformalVekuaNormalizedConormalRemainder coords hγ hτ (F 1) E b =
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier (CCF E b)) := by
  apply localConformalDiskHalfTrace_separates coords
  intro w
  rw [localConformalVekuaNormalizedConormalRemainder,
    localConformalBoundaryLoad_inner coords hγ hτ hcoord,
    bridge_physicalFlux_split coords hγ,
    inner_add_right, inner_smul_right, inner_smul_right]
  have hh := inner_sobolevSmoothing_half (QF w) (boundaryFourier (TF w))
    (boundaryFourier (CCF E b)) (fun n => by rfl)
  rw [hh, boundaryFourier.inner_map_map]
  change _ = ⟪TF w, (-Complex.I) • boundaryContinuousMultiplier
      (localConformalVelocityCircle F) (TF (AF (F 1) E b)) +
    Complex.I • boundaryContinuousMultiplier (localConformalPrimitiveCircle F)
      (TF (BF (F 1) E b))⟫_ℂ
  let uA : NeumannH1 ΩF := AF (F 1) E b
  let uB : NeumannH1 ΩF := BF (F 1) E b
  have hA := bridge_velocity_pairing coords
    hγ hτ hcoord false w uA
  have hB := bridge_velocity_pairing coords
    hγ hτ hcoord true w uB
  simp   at hA hB
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  exact congrArg₂ (fun x y : ℂ => (-Complex.I) * x + Complex.I * y) hA hB

end

section

variable {F}
include coords

/-- Independent affine and primitive powers have their actual coefficient
convolution. The primitive constant and the frequency-zero term are included. -/
theorem localConformalVekuaConormal_trace_term (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j k : ℕ) :
    (boundaryFourier (TF ((MF ^ j) (UF ((JF ^ k) b)))) : ℤ → ℂ) =
      seqConv (seqConvPow gF j) (antiPrimIter aF k (fromL2 (1 / 2 : ℝ) b)) := by
  rw [← fromL2_half_localConformalDiskHalfTrace,
    localConformalDiskHalfTrace_affineMultiplier_pow coords,
    fromL2_normalizedHardyMultiplier,
    localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive coords _
      (localConformalHardyPrimitive_pow_nonpositive coords.one_lt_radius F coords.smooth coords.holomorphic b hbn k),
    fromL2_localConformalHardyPrimitive_pow]

end

def bridge_coordinateNormalizer : BoundaryL2 →L[ℂ] L2Z :=
  (sobolevSmoothing (1 / 2 : ℝ) (by norm_num)).comp
    boundaryFourier.toLinearIsometry.toContinuousLinearMap

private theorem bridge_coordinateNormalizer_apply (g : BoundaryL2) (n : ℤ) :
    bridge_coordinateNormalizer g n =
      ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * boundaryFourier g n := rfl

private theorem bridge_coordinateNormalizer_multiplier (A : C(AddCircle (2 * Real.pi), ℂ))
    (hA : Summable (fourierCoeff A)) (u : NeumannH1 ΩF) (n : ℤ) :
    bridge_coordinateNormalizer (boundaryContinuousMultiplier A ((localConformalDiskH1Trace hR F hFs hL) u)) n =
      ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        seqConv (fourierCoeff A) (boundaryFourier ((localConformalDiskH1Trace hR F hFs hL) u)) n := by
  rw [bridge_coordinateNormalizer_apply, boundaryFourier_continuousMultiplier A hA]

private theorem bridge_smoothed_conormalTerm_apply (j : ℕ) (b : L2Z) (n : ℤ) :
    sobolevSmoothing 1 zero_le_one
        (conormalTermOp (by norm_num) (localConformalVelocityCircle_isWL1_half hR F hFs) (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs) (localConformalCenteredCircle_isWL1_half hR F hFs) j b) n =
      ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        conormalTermMap βF aF (fourierCoeff (localConformalCenteredCircle hR F hFs)) j (fromL2 (1 / 2 : ℝ) b) n := by
  change ((sobWeight n ^ (-(1 : ℝ)) : ℝ) : ℂ) *
      conormalTermOp (by norm_num) (localConformalVelocityCircle_isWL1_half hR F hFs) (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs) (localConformalCenteredCircle_isWL1_half hR F hFs) j b n = _
  rw [conormalTermOp, SeqOpBound.toCLM_apply, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_add (sobWeight_pos n)]
  ring

section

variable {F}
include coords

/-- Each actual coordinate flux term equals the existing normalized conormal
term after smoothing. Its velocities use averaged Fourier coefficients. -/
theorem localConformalVekuaConormal_coordinate_term (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j : ℕ) :
    bridge_coordinateNormalizer
      ((-Complex.I) • boundaryContinuousMultiplier (localConformalVelocityCircle F)
          (TF ((physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
            (MF ^ j) (UF ((JF ^ (j + 1)) b)))) +
        Complex.I • boundaryContinuousMultiplier (localConformalPrimitiveCircle F)
          (TF (physicalVekuaCoeff E (j + 1) •
            (MF ^ (j + 1)) (UF ((JF ^ j) b))))) =
      conormalCoeff E j • sobolevSmoothing 1 zero_le_one
        (conormalTermOp (by norm_num) hβF haF hgF j b) := by
  have hβ : Summable βF := IsWL1.summable (by norm_num) hβF
  have ha : Summable (fourierCoeff (localConformalPrimitiveCircle F)) := by
    rw [localConformalPrimitiveCircle_coeff coords.one_lt_radius F coords.smooth]
    exact IsWL1.summable (by norm_num) haF
  apply lp.ext
  funext n
  simp only [map_add, map_smul, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
    Pi.smul_apply]
  rw [bridge_coordinateNormalizer_multiplier coords.one_lt_radius F coords.smooth coords.lipschitz _ hβ,
    bridge_coordinateNormalizer_multiplier coords.one_lt_radius F coords.smooth coords.lipschitz _ ha,
    localConformalPrimitiveCircle_coeff coords.one_lt_radius F coords.smooth,
    localConformalVekuaConormal_trace_term coords b hbn,
    localConformalVekuaConormal_trace_term coords b hbn,
    bridge_smoothed_conormalTerm_apply coords.one_lt_radius F coords.smooth j b n]
  simp only [conormalTermMap, Pi.add_apply, Pi.smul_apply, conormalCoeff, physicalVekuaCoeff]
  ring

/-- Exact identification with the old operator series. This is obtained
from genuine H¹ trace HasSums, without a premise identifying the conormal. -/
theorem localConformalVekuaCoordinateConormalRemainder_eq_conormalRemOp
    (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier (CCF E b)) =
      sobolevSmoothing 1 zero_le_one
        (conormalRemOp (by norm_num) hβF haF hgF E b) := by
  let P := (boundaryContinuousMultiplier (localConformalVelocityCircle F)).comp TF
  let Q := (boundaryContinuousMultiplier (localConformalPrimitiveCircle F)).comp TF
  have hA := (P.hasSum (localConformalVekuaGradientA_hasSum coords (F 1) E b)).const_smul (-Complex.I)
  have hB := (Q.hasSum (localConformalVekuaGradientB_hasSum coords (F 1) E b)).const_smul Complex.I
  have hl := bridge_coordinateNormalizer.hasSum (hA.add hB)
  have heq (j : ℕ) :=
    localConformalVekuaConormal_coordinate_term coords E b hbn j
  have hl' : HasSum (fun j : ℕ => conormalCoeff E j • sobolevSmoothing 1 zero_le_one
      (conormalTermOp (by norm_num) hβF haF hgF j b))
      (sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier (CCF E b))) := by
    have hl0 := hl.congr_fun (fun j => (heq j).symm)
    assumption
  have hr := (sobolevSmoothing 1 zero_le_one).hasSum
    ((ContinuousLinearMap.apply ℂ L2Z b).hasSum
      (summable_conormalSeries (by norm_num) hβF haF hgF E).hasSum)
  have hr' : HasSum (fun j : ℕ => conormalCoeff E j • sobolevSmoothing 1 zero_le_one
      (conormalTermOp (by norm_num) hβF haF hgF j b))
      (sobolevSmoothing 1 zero_le_one
        (conormalRemOp (by norm_num) hβF haF hgF E b)) := by
    simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
      map_smul, conormalRemOp] using hr
  exact hl'.unique hr'

include hcoord in
/-- The actual physical normalized flux is precisely the Fourier conormal
remainder used by formal transmutation, including the zero Fourier mode. -/
theorem localConformalVekuaNormalizedConormalRemainder_eq_conormalRemOp
    (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    localConformalVekuaNormalizedConormalRemainder coords hγ hτ (F 1) E b =
      sobolevSmoothing 1 zero_le_one
        (conormalRemOp (by norm_num) hβF haF hgF E b) := by
  rw [localConformalVekuaNormalizedConormalRemainder_eq_coordinate coords hγ hτ hcoord]
  exact localConformalVekuaCoordinateConormalRemainder_eq_conormalRemOp coords E b hbn

include hγ hτ hcoord in
/-- The actual Vekua solution has the existing normalized conormal weak
form, proved through its genuine physical gradient and boundary flux. -/
theorem localConformalVekuaH1_normalizedConormal_weak_form (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (w : NeumannH1 ΩF) :
    (∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i
      (localConformalVekuaH1 coords
        (F 1) E b)⟫_ℂ) - E * ⟪h1Value ΩF w, h1Value ΩF
      (localConformalVekuaH1 coords
        (F 1) E b)⟫_ℂ =
      ⟪QF w, normalizedConormal hβF haF hgF E b⟫_ℂ := by
  have h := localConformalVekuaH1_normalized_weak_form coords hγ hτ hcoord (F 1) E b hbn w
  rw [localConformalVekuaNormalizedConormalRemainder_eq_conormalRemOp coords hγ hτ hcoord E b hbn] at h
  have hbproj : (1 - posProj) b = b := by
    ext n
    simp only [posProj]
    by_cases hn : 0 < n
    · simp [hbn n hn]
    simp_all
  simpa only [hbproj, normalizedConormal, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply] using h

end

end VekuaCoordinates

end PolyaNeumann

end
