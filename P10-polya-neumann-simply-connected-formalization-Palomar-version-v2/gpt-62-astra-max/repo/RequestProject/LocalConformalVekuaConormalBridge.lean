module

public import RequestProject.CircleAnalysisNotation

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalVekuaConormal
public import RequestProject.LocalConformalVekuaTrace
public import RequestProject.DiskWeakModes
public import RequestProject.PlanarNotation

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

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology InnerProductSpace ComplexConjugate

section

variable (Φ : SmoothDiskMap)

/-- The actual continuous nonconjugate angular velocity of F on the circle. -/
def localConformalVelocityCircle (F : ℂ → ℂ) : C(ParamCircle, ℂ) :=
  ⟨fun q => conj (localConformalPrimitiveCircle F q),
    Complex.continuous_conj.comp (localConformalPrimitiveCircle F).continuous⟩

theorem localConformalVelocityCircle_apply (θ : ℝ) :
    localConformalVelocityCircle Φ.map (θ : ParamCircle) =
      deriv Φ.boundary θ := by
  change conj (localConformalPrimitiveCircle Φ.map (θ : ParamCircle)) = _
  rw [localConformalPrimitiveCircle_apply Φ, Complex.conj_conj]

theorem localConformalVelocityCircle_coeff :
    fourierCoeff (localConformalVelocityCircle Φ.map) =
      angleCoeff (deriv Φ.boundary) := by
  rw [circle_fourierCoeff_eq]
  congr 1
  exact funext (localConformalVelocityCircle_apply Φ)

theorem localConformalVelocityCircle_isWL1_half :
    IsWL1 halfOrder (fourierCoeff (localConformalVelocityCircle Φ.map)) := by
  rw [localConformalVelocityCircle_coeff Φ]
  exact vekua_isWL1_mono (by norm_num)
    (periodic_contDiff_four_fourier_weights
      Φ.boundaryC4
      Φ.periodic_boundary).1

end

/-- The normalized conormal in the Fourier coordinates of this disk map. -/
abbrev SmoothDiskMap.conormal (φ : SmoothDiskMap) :=
  normalizedConormal (localConformalVelocityCircle_isWL1_half φ)
    (localConformalHardyPrimitiveMultiplier_isWL1 φ) (localConformalCenteredCircle_isWL1_half φ)

private def bridge_physicalVelocity {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (conjugated : Bool) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  let B  := Classical.choose hγ.lipschitz
  let hB  := Classical.choose_spec hγ.lipschitz
  lpBoundedMultiplier
    (fun θ => if conjugated then conj (deriv γ θ) else deriv γ θ)
    (by cases conjugated
        · exact (measurable_deriv γ).aestronglyMeasurable.restrict
        · exact (Complex.continuous_conj.comp_aestronglyMeasurable
            (measurable_deriv γ).aestronglyMeasurable).restrict)
    (Eventually.of_forall fun θ => by
      cases conjugated <;> simpa using
        (norm_deriv_le_of_lipschitz hB : ‖deriv γ θ‖ ≤ B))

private theorem bridge_physicalVelocity_ae {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (conjugated : Bool) (g : BoundaryL2) :
    (bridge_physicalVelocity hγ conjugated g : ℝ → ℂ) =ᵐ[
      angleMeasure]
      fun θ => (if conjugated then conj (deriv γ θ) else deriv γ θ) * g θ :=
  by unfold bridge_physicalVelocity; apply lpBoundedMultiplier_ae

section CoordinatePairing

private theorem bridge_velocity_jacobian (Φ : SmoothDiskMap) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (conjugated : Bool) :
    (fun θ : ℝ => if conjugated then
        localConformalPrimitiveCircle Φ.map (θ : ParamCircle) else
        localConformalVelocityCircle Φ.map (θ : ParamCircle)) =ᵐ[
      angleMeasure]
      fun θ => deriv τ θ •
        (if conjugated then conj (deriv γ (τ θ)) else deriv γ (τ θ)) := by
  obtain ⟨B, hB⟩ := hγ.lipschitz
  obtain ⟨D, hD⟩ := hτ.lipschitz
  have hchain := (ae_deriv_comp hB hτ.monotone hD).filter_mono
    (ae_restrict_le : ae angleMeasure ≤ ae volume)
  have he : γ ∘ τ = Φ.boundary := funext fun θ => (hcoord θ).symm
  rw [he] at hchain
  filter_upwards [hchain] with θ hθ
  cases conjugated <;> simp [↓reduceIte, localConformalPrimitiveCircle_apply Φ, localConformalVelocityCircle_apply Φ, hθ, Complex.real_smul, map_mul, Complex.conj_ofReal]

/-- Actual velocity multiplication transforms with the real Jacobian. The
two trace inputs are extended separately from smooth H¹ restrictions. -/
private theorem bridge_velocity_pairing (Φ : ConformalDiskMap) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (conjugated : Bool) (w u : NeumannH1 Φ.domain) :
    ⟪(h1BoundaryTrace Φ.lipschitzDomain hγ) w, bridge_physicalVelocity hγ conjugated ((h1BoundaryTrace Φ.lipschitzDomain hγ) u)⟫_ℂ =
      ⟪(Φ.pulledBackTrace Φ.lipschitzDomain) w, boundaryContinuousMultiplier
        (if conjugated then localConformalPrimitiveCircle Φ.map else
          localConformalVelocityCircle Φ.map) ((Φ.pulledBackTrace Φ.lipschitzDomain) u)⟫_ℂ := by
  refine (denseRange_smoothTraceH1Lin Φ.bounded Φ.lipschitzDomain).induction_on
     w ?_ ?_
  · exact isClosed_eq (((h1BoundaryTrace Φ.lipschitzDomain hγ)).continuous.inner continuous_const)
      (((Φ.pulledBackTrace Φ.lipschitzDomain)).continuous.inner continuous_const)
  · intro f
    refine (denseRange_smoothTraceH1Lin Φ.bounded Φ.lipschitzDomain).induction_on
       u ?_ ?_
    · exact isClosed_eq
        (continuous_const.inner ((bridge_physicalVelocity hγ conjugated).continuous.comp
          ((h1BoundaryTrace Φ.lipschitzDomain hγ)).continuous))
        (continuous_const.inner ((boundaryContinuousMultiplier
          (if conjugated then localConformalPrimitiveCircle Φ.map else
            localConformalVelocityCircle Φ.map)).continuous.comp (Φ.pulledBackTrace Φ.lipschitzDomain).continuous))
    · intro g
      simp
      calc
        _ = ∫ s in angleIoc, conj (f (γ s)) *
            ((if conjugated then conj (deriv γ s) else deriv γ s) * g (γ s)) := by
          apply integral_congr_ae
          filter_upwards [h1BoundaryTrace_smooth_ae Φ.bounded Φ.lipschitzDomain hγ f,
            h1BoundaryTrace_smooth_ae Φ.bounded Φ.lipschitzDomain hγ g,
            bridge_physicalVelocity_ae hγ conjugated ((h1BoundaryTrace Φ.lipschitzDomain hγ) (smoothTraceH1 Φ.domain g))]
            with s hf hg hp
          simp only [RCLike.inner_apply', hf, hp, hg]
        _ = _ :=
          (integral_traceReparam_conormal hτ _).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [localConformalDiskH1Trace_smooth_ae Φ f,
            localConformalDiskH1Trace_smooth_ae Φ g,
            boundaryContinuousMultiplier_ae
              (if conjugated then localConformalPrimitiveCircle Φ.map else
                localConformalVelocityCircle Φ.map) ((Φ.pulledBackTrace Φ.lipschitzDomain) (smoothTraceH1 Φ.domain g)),
            bridge_velocity_jacobian Φ hγ hτ hcoord conjugated]
            with θ hf hg hm hj
          cases conjugated <;>
            simp only [Bool.false_eq_true, ↓reduceIte] at * <;>
            simp only [RCLike.inner_apply', hf, hm, hg, hcoord] <;>
            rw [hj] <;> simp <;> ring

end CoordinatePairing

section VekuaCoordinates

section

variable (Φ : DiskCoordinates) (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) (j : ℕ)

include E Φ in
/-- The genuine coordinate flux; its two inputs are the actual H¹ gradient
representatives. The variable circle speed is included in its velocities. -/
def DiskCoordinates.vekuaCoordinateConormalRemainder : L2Z →L[ℂ] BoundaryL2 :=
  (-Complex.I) • ((boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)).comp
      (((Φ.pulledBackTrace Φ.lipschitzDomain)).comp (Φ.vekuaGradientA (Φ.map 1) E))) +
    Complex.I • ((boundaryContinuousMultiplier (localConformalPrimitiveCircle Φ.map)).comp
      (((Φ.pulledBackTrace Φ.lipschitzDomain)).comp (Φ.vekuaGradientB (Φ.map 1) E)))

/-- The actual conformal half trace separates L² coefficient vectors.
This uses genuine harmonic tests and the constructed H¹ inverse. -/
theorem localConformalDiskHalfTrace_separates (x y : L2Z)
    (hxy : ∀ w : NeumannH1 Φ.domain, ⟪(Φ.pulledBackHalfTrace Φ.lipschitzDomain) w, x⟫_ℂ = ⟪(Φ.pulledBackHalfTrace Φ.lipschitzDomain) w, y⟫_ℂ) : x = y := by
  ext n
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · have h := hxy (Φ.h1Pushforward (diskHolomorphicH1Test m))
    change ⟪diskHalfTrace (Φ.h1Pullback Φ.lipschitzDomain _), x⟫_ℂ =
      ⟪diskHalfTrace (Φ.h1Pullback Φ.lipschitzDomain _), y⟫_ℂ at h
    rw [localConformalH1Pullback_pushforward, diskHalfTrace_holomorphicTest,
      inner_smul_left, inner_smul_left, hardy_inner_stdBasisZ, hardy_inner_stdBasisZ] at h
    exact mul_left_cancel₀ (by
      simp only [map_mul, Complex.conj_ofReal]
      exact mul_ne_zero
        (by exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos m)).ne')
        (by exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne')) h
  · have h := hxy (Φ.h1Pushforward (diskAntiholomorphicH1Test m))
    change ⟪diskHalfTrace (Φ.h1Pullback Φ.lipschitzDomain _), x⟫_ℂ =
      ⟪diskHalfTrace (Φ.h1Pullback Φ.lipschitzDomain _), y⟫_ℂ at h
    rw [localConformalH1Pullback_pushforward, diskHalfTrace_antiholomorphicTest,
      inner_smul_left, inner_smul_left, hardy_inner_stdBasisZ, hardy_inner_stdBasisZ] at h
    exact mul_left_cancel₀ (by
      simp only [map_mul, Complex.conj_ofReal]
      exact mul_ne_zero
        (by exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos (-m))).ne')
        (by exact_mod_cast (by positivity))) h

private theorem bridge_physicalFlux_split {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) (E : ℂ) (b : L2Z) :
    Φ.vekuaConormalRemainder hγ (Φ.map 1) E b =
      (-Complex.I) • bridge_physicalVelocity hγ false
        (h1BoundaryTrace Φ.lipschitzDomain hγ (Φ.vekuaGradientA (Φ.map 1) E b)) +
        Complex.I • bridge_physicalVelocity hγ true
          (h1BoundaryTrace Φ.lipschitzDomain hγ (Φ.vekuaGradientB (Φ.map 1) E b)) := by
  apply Lp.ext
  filter_upwards [localConformalVekuaConormalRemainder_ae Φ hγ (Φ.map 1) E b,
    Lp.coeFn_add
      ((-Complex.I) • bridge_physicalVelocity hγ false
        (h1BoundaryTrace Φ.lipschitzDomain hγ (Φ.vekuaGradientA (Φ.map 1) E b)))
      (Complex.I • bridge_physicalVelocity hγ true
        (h1BoundaryTrace Φ.lipschitzDomain hγ (Φ.vekuaGradientB (Φ.map 1) E b))),
    Lp.coeFn_smul (-Complex.I) (bridge_physicalVelocity hγ false
      (h1BoundaryTrace Φ.lipschitzDomain hγ (Φ.vekuaGradientA (Φ.map 1) E b))),
    Lp.coeFn_smul Complex.I (bridge_physicalVelocity hγ true
      (h1BoundaryTrace Φ.lipschitzDomain hγ (Φ.vekuaGradientB (Φ.map 1) E b))),
    bridge_physicalVelocity_ae hγ false (h1BoundaryTrace Φ.lipschitzDomain hγ (Φ.vekuaGradientA (Φ.map 1) E b)),
    bridge_physicalVelocity_ae hγ true (h1BoundaryTrace Φ.lipschitzDomain hγ (Φ.vekuaGradientB (Φ.map 1) E b))]
    with θ hc ha hA hB hv hvc
  rw [hc, ha]
  simp only [Pi.add_apply, hA, hB, Pi.smul_apply, hv, hvc, Bool.false_eq_true, ↓reduceIte]
  ring

/-- The actual normalized physical remainder is the half-smoothed Fourier
transform of the actual coordinate flux. The Jacobian is proved, not assumed. -/
theorem localConformalVekuaNormalizedConormalRemainder_eq_coordinate {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (E : ℂ) (b : L2Z) :
    Φ.vekuaNormalizedConormalRemainder hγ hτ (Φ.map 1) E b =
      sobolevSmoothing halfOrder (by norm_num) (boundaryFourier (Φ.vekuaCoordinateConormalRemainder E b)) := by
  apply localConformalDiskHalfTrace_separates Φ
  intro w
  rw [DiskCoordinates.vekuaNormalizedConormalRemainder,
    localConformalBoundaryLoad_inner Φ hγ hτ hcoord,
    bridge_physicalFlux_split Φ hγ,
    inner_add_right, inner_smul_right, inner_smul_right]
  have hh := boundaryLoad_half_pairing ((Φ.pulledBackHalfTrace Φ.lipschitzDomain) w) _
    (boundaryFourier (Φ.vekuaCoordinateConormalRemainder E b)) (fun n => localConformalDiskHalfTrace_apply Φ Φ.lipschitzDomain w n)
  rw [hh, boundaryFourier.inner_map_map]
  change _ = ⟪(Φ.pulledBackTrace Φ.lipschitzDomain) w, (-Complex.I) • boundaryContinuousMultiplier
      (localConformalVelocityCircle Φ.map) ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaGradientA (Φ.map 1) E b)) +
    Complex.I • boundaryContinuousMultiplier (localConformalPrimitiveCircle Φ.map)
      ((Φ.pulledBackTrace Φ.lipschitzDomain) (Φ.vekuaGradientB (Φ.map 1) E b))⟫_ℂ
  
  
  have hA := bridge_velocity_pairing Φ hγ hτ hcoord false w (Φ.vekuaGradientA (Φ.map 1) E b)
  have hB := bridge_velocity_pairing Φ hγ hτ hcoord true w (Φ.vekuaGradientB (Φ.map 1) E b)
  
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  exact congrArg₂ (fun x y : ℂ => (-Complex.I) * x + Complex.I * y) hA hB

include hbn in
/-- Independent affine and primitive powers have their actual coefficient
convolution. The primitive constant and the frequency-zero term are included. -/
theorem localConformalVekuaConormal_trace_term (k : ℕ) :
    (boundaryFourier ((Φ.pulledBackTrace Φ.lipschitzDomain) (((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ k) b)))) : ℤ → ℂ) =
      seqConv (seqConvPow (fourierCoeff Φ.centeredCircle) j) (antiPrimIter (localConformalHardyPrimitiveMultiplier Φ.map) k (fromL2 halfOrder b)) := by
  rw [← fromL2_half_localConformalDiskHalfTrace,
    localConformalDiskHalfTrace_affineMultiplier_pow Φ,
    vekua_fromL2_multiplier,
    localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive Φ _
      (localConformalHardyPrimitive_pow_nonpositive Φ Φ.holomorphic b hbn k),
    fromL2_localConformalHardyPrimitive_pow]

def bridge_coordinateNormalizer : BoundaryL2 →L[ℂ] L2Z :=
  (sobolevSmoothing halfOrder (by norm_num)).comp
    boundaryFourier.toLinearIsometry.toContinuousLinearMap

private theorem bridge_coordinateNormalizer_apply (g : BoundaryL2) (n : ℤ) :
    bridge_coordinateNormalizer g n =
      ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) * boundaryFourier g n := rfl

private theorem bridge_coordinateNormalizer_multiplier (Φ : SmoothDiskMap)
    (hL : IsLipschitzDomain Φ.domain) (A : C(ParamCircle, ℂ)) (hA : Summable (fourierCoeff A))
    (u : NeumannH1 Φ.domain) (n : ℤ) :
    bridge_coordinateNormalizer (boundaryContinuousMultiplier A ((Φ.pulledBackTrace hL) u)) n =
      ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) *
        seqConv (fourierCoeff A) (boundaryFourier ((Φ.pulledBackTrace hL) u)) n := by
  rw [bridge_coordinateNormalizer_apply, boundaryFourier_continuousMultiplier A hA]

private theorem bridge_smoothed_conormalTerm_apply (Φ : SmoothDiskMap) (j : ℕ) (b : L2Z)
    (n : ℤ) :
    sobolevSmoothing 1 zero_le_one
        (conormalTermOp (by norm_num) (localConformalVelocityCircle_isWL1_half Φ) (localConformalHardyPrimitiveMultiplier_isWL1 Φ) (localConformalCenteredCircle_isWL1_half Φ) j b) n =
      ((sobWeight n ^ (-halfOrder) : ℝ) : ℂ) *
        conormalTermMap (fourierCoeff (localConformalVelocityCircle Φ.map)) (localConformalHardyPrimitiveMultiplier Φ.map) (fourierCoeff Φ.centeredCircle) j (fromL2 halfOrder b) n := by
  change ((sobWeight n ^ (-(1 : ℝ)) : ℝ) : ℂ) *
      conormalTermOp (by norm_num) (localConformalVelocityCircle_isWL1_half Φ) (localConformalHardyPrimitiveMultiplier_isWL1 Φ) (localConformalCenteredCircle_isWL1_half Φ) j b n = _
  rw [conormalTermOp, multiplier_toCLM_apply, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_add (sobWeight_pos n)]
  ring

include hbn in
/-- Each actual coordinate flux term equals the existing normalized conormal
term after smoothing. Its velocities use averaged Fourier coefficients. -/
theorem localConformalVekuaConormal_coordinate_term :
    bridge_coordinateNormalizer
      ((-Complex.I) • boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)
          ((Φ.pulledBackTrace Φ.lipschitzDomain) ((physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
            ((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ j) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ (j + 1)) b)))) +
        Complex.I • boundaryContinuousMultiplier (localConformalPrimitiveCircle Φ.map)
          ((Φ.pulledBackTrace Φ.lipschitzDomain) (physicalVekuaCoeff E (j + 1) •
            ((neumannH1AffineMultiplier Φ.bounded (Φ.map 1)) ^ (j + 1)) (Φ.hardyH1Extension ((Φ.hardyPrimitive ^ j) b))))) =
      conormalCoeff E j • sobolevSmoothing 1 zero_le_one
        (conormalTermOp (by norm_num) (localConformalVelocityCircle_isWL1_half Φ) (localConformalHardyPrimitiveMultiplier_isWL1 Φ) (localConformalCenteredCircle_isWL1_half Φ) j b) := by
  
  
  ext n
  simp only [map_add, map_smul, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [bridge_coordinateNormalizer_multiplier Φ Φ.lipschitzDomain _ (vekua_summable_coeff (by norm_num) (localConformalVelocityCircle_isWL1_half Φ)),
    bridge_coordinateNormalizer_multiplier Φ Φ.lipschitzDomain _ (by
        rw [localConformalPrimitiveCircle_coeff Φ]
        exact vekua_summable_coeff (by norm_num) (localConformalHardyPrimitiveMultiplier_isWL1 Φ)),
    localConformalPrimitiveCircle_coeff Φ,
    localConformalVekuaConormal_trace_term Φ b hbn,
    localConformalVekuaConormal_trace_term Φ b hbn,
    bridge_smoothed_conormalTerm_apply Φ j b n]
  simp [conormalTermMap, smul_eq_mul, conormalCoeff, physicalVekuaCoeff] <;> ring

include hbn in
/-- Exact identification with the old operator series. This is obtained
from genuine H¹ trace HasSums, without a premise identifying the conormal. -/
theorem localConformalVekuaCoordinateConormalRemainder_eq_conormalRemOp :
    sobolevSmoothing halfOrder (by norm_num) (boundaryFourier (Φ.vekuaCoordinateConormalRemainder E b)) =
      sobolevSmoothing 1 zero_le_one
        (conormalRemOp (by norm_num) (localConformalVelocityCircle_isWL1_half Φ) (localConformalHardyPrimitiveMultiplier_isWL1 Φ) (localConformalCenteredCircle_isWL1_half Φ) E b) := by
  
  
  have hA := (((boundaryContinuousMultiplier (localConformalVelocityCircle Φ.map)).comp (Φ.pulledBackTrace Φ.lipschitzDomain)).hasSum (localConformalVekuaGradientA_hasSum Φ (Φ.map 1) E b)).const_smul (-Complex.I)
  have hB := (((boundaryContinuousMultiplier (localConformalPrimitiveCircle Φ.map)).comp (Φ.pulledBackTrace Φ.lipschitzDomain)).hasSum (localConformalVekuaGradientB_hasSum Φ (Φ.map 1) E b)).const_smul Complex.I
  
  have heq (j : ℕ)  :=
    localConformalVekuaConormal_coordinate_term Φ E b hbn j
  have hl' : HasSum (fun j : ℕ => conormalCoeff E j • sobolevSmoothing 1 zero_le_one
      (conormalTermOp (by norm_num) (localConformalVelocityCircle_isWL1_half Φ) (localConformalHardyPrimitiveMultiplier_isWL1 Φ) (localConformalCenteredCircle_isWL1_half Φ) j b))
      (sobolevSmoothing (1 / 2) (by norm_num) (boundaryFourier (Φ.vekuaCoordinateConormalRemainder E b))) := by
    have hl0 := (bridge_coordinateNormalizer.hasSum (hA.add hB)).congr_fun (fun j => (heq j).symm)
    assumption
  have hr := (sobolevSmoothing 1 zero_le_one).hasSum
    ((ContinuousLinearMap.apply ℂ L2Z b).hasSum
      (summable_conormalSeries (by norm_num) (localConformalVelocityCircle_isWL1_half Φ) (localConformalHardyPrimitiveMultiplier_isWL1 Φ) (localConformalCenteredCircle_isWL1_half Φ) E).hasSum)
  
  apply hl'.unique
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
    map_smul, conormalRemOp] using hr

/-- The actual physical normalized flux is precisely the Fourier conormal
remainder used by formal transmutation, including the zero Fourier mode. -/
theorem localConformalVekuaNormalizedConormalRemainder_eq_conormalRemOp {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    Φ.vekuaNormalizedConormalRemainder hγ hτ (Φ.map 1) E b =
      sobolevSmoothing 1 zero_le_one
        (conormalRemOp (by norm_num) (localConformalVelocityCircle_isWL1_half Φ) (localConformalHardyPrimitiveMultiplier_isWL1 Φ) (localConformalCenteredCircle_isWL1_half Φ) E b) := by
  rw [localConformalVekuaNormalizedConormalRemainder_eq_coordinate Φ hγ hτ hcoord]
  exact localConformalVekuaCoordinateConormalRemainder_eq_conormalRemOp Φ E b hbn

/-- The actual Vekua solution has the existing normalized conormal weak
form, proved through its genuine physical gradient and boundary flux. -/
theorem localConformalVekuaH1_normalizedConormal_weak_form {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Φ.domain γ) {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, Φ.map (unitCirclePt θ) = γ (τ θ)) (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (w : NeumannH1 Φ.domain) :
    (∑ i : Fin 2, ⟪h1Gradient Φ.domain i w, h1Gradient Φ.domain i
      (Φ.vekuaH1 (Φ.map 1) E b)⟫_ℂ) - E * ⟪h1Value Φ.domain w, h1Value Φ.domain
      (Φ.vekuaH1 (Φ.map 1) E b)⟫_ℂ =
      ⟪(Φ.pulledBackHalfTrace Φ.lipschitzDomain) w, normalizedConormal (localConformalVelocityCircle_isWL1_half Φ) (localConformalHardyPrimitiveMultiplier_isWL1 Φ) (localConformalCenteredCircle_isWL1_half Φ) E b⟫_ℂ := by
  have h := localConformalVekuaH1_normalized_weak_form Φ hγ hτ hcoord (Φ.map 1) E b hbn w
  rw [localConformalVekuaNormalizedConormalRemainder_eq_conormalRemOp Φ hγ hτ hcoord E b hbn] at h
  have hbproj : (1 - posProj) b = b := by
    ext n
    simp only [Pi.sub_apply, posProj, diagOp_apply]
    by_cases hn : 0 < n
    · simp [hbn n hn]
    · simp [hn]
  simpa [hbproj, normalizedConormal] using h

end

end VekuaCoordinates

end PolyaNeumann

end
