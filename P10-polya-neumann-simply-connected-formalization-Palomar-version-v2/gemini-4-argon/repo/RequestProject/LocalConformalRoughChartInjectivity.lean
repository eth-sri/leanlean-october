module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import RequestProject.RoughVekuaTransport
public import RequestProject.LocalConformalRoughHardySupport
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


noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ComplexConjugate ContDiff

variable {L : NNReal} {d : ℕ}

local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
local notation "H₀" => nonpositiveFourierSubspace

/-- A true L2 Hardy split controls the positive rough primitive. This
This lemma concerns actual boundary vectors and uses no endpoint value. -/
theorem roughNormalizedPrimitive_pos_one_of_hardy_split
    (y : L2Z) H K
    (hH : IsNonpositiveFourierSupport (boundaryFourier H : ℤ → ℂ))
    (hK : IsSobolevSeq 1 (boundaryFourier K : ℤ → ℂ))
    (hsplit : H = -Complex.I • roughNormalizedPrimitive y + K) :
    IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ) := by
  let p := posProj (boundaryFourier (roughNormalizedPrimitive y))
  let k := posProj (boundaryFourier K)
  have hs := congrArg (fun B => posProj (boundaryFourier B)) hsplit
  change posProj (boundaryFourier H) =
    posProj (boundaryFourier (-Complex.I • roughNormalizedPrimitive y + K)) at hs
  rw [show posProj (boundaryFourier H) = 0 by
    apply lp.ext
    funext n
    by_cases hn : 0 < n
    · simp [posProj, if_pos hn, hH n hn]
    · simp [posProj, if_neg hn], map_add, map_smul, map_add, map_smul] at hs
  change 0 = -Complex.I • p + k at hs
  have hi := congrArg (fun B => Complex.I • B) hs
  simp [smul_smul] at hi
  change p ∈ fourierSobolevSubmodule 1
  rw [show p = -Complex.I • k by
    simpa using eq_neg_of_add_eq_zero_left hi.symm]
  exact (fourierSobolevSubmodule 1).smul_mem _ (isSobolevSeq_posProj hK)

theorem roughNormalizedPrimitive_pos_one_of_hardy_split_ae
    (y : L2Z) H K
    (hH : IsNonpositiveFourierSupport (boundaryFourier H : ℤ → ℂ))
    (hK : IsSobolevSeq 1 (boundaryFourier K : ℤ → ℂ))
    (hsplit : (H : ℝ → ℂ) =ᵐ[μB]
      (fun θ => -Complex.I * roughNormalizedPrimitive y θ + K θ)) :
    IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ) := by
  apply roughNormalizedPrimitive_pos_one_of_hardy_split y H K hH hK
  apply Lp.ext
  filter_upwards [hsplit, Lp.coeFn_add (-Complex.I • roughNormalizedPrimitive y) K,
    Lp.coeFn_smul (-Complex.I) (roughNormalizedPrimitive y)] with θ hs ha hm
  simpa only [ha, hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hs

/-- Actual raw L2 gauges and corrections can be passed to the boundary
vector split without introducing pointwise periodicity of the gauge. -/
theorem roughNormalizedPrimitive_pos_one_of_raw_hardy_split
    (y : L2Z) H K (hH2 : MemLp H 2 μB) (hK2 : MemLp K 2 μB)
    (hH : IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H))
    (hK1 : IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos K))
    (hsplit : H =ᵐ[μB] fun θ => -Complex.I * roughNormalizedPrimitive y θ + K θ) :
    IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ) := by
  apply roughNormalizedPrimitive_pos_one_of_hardy_split_ae y (hH2.toLp H) (hK2.toLp K)
    (by
      intro n hn
      rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hH2.coeFn_toLp,
        hH n hn, mul_zero]) (by
          rw [show (boundaryFourier (hK2.toLp K) : ℤ → ℂ) = (Real.sqrt (2 * Real.pi) : ℂ) • fourierCoeffOn Real.two_pi_pos K by
            funext n
            rw [boundaryFourier_apply,
              fourierCoeffOn_congr_ae Real.two_pi_pos hK2.coeFn_toLp]
            rfl]
          exact isSobolevSeq_smul _ hK1)
  filter_upwards [hH2.coeFn_toLp, hK2.coeFn_toLp, hsplit] with θ hh hk hs
  rw [hh, hk]
  exact hs

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (Metric.ball 0 R))
    (hb : Bornology.IsBounded (F '' Metric.ball 0 1))
    (hL : IsLipschitzDomain (F '' Metric.ball 0 1))
    (hhol : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hinj : InjOn F (Metric.ball 0 1))
    (hC : ∀ z ∈ Metric.ball 0 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ Metric.ball 0 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : ↑e = F)
    (hsource : Metric.closedBall 0 1 ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target)

local notation "ΓF" => physicalCircleTrace F
local notation "NF" => normalizedConormal (localConformalVelocityCircle_isWL1_half hR F hFs) (localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs) (localConformalCenteredCircle_isWL1_half hR F hFs)

include hR hFs hb hL hhol e he hsource hes in
/-- The genuine rough driven gauge is Hardy for every normalized
observation-kernel input. The moments come from the actual positive-row
ODE and factorial tails, and the Hardy conclusion uses the true L2
physical moment criterion. -/
theorem localConformal_roughGauge_exists_nonpositive_of_projObsDual_eq_zero
     (hΓLip : LipschitzWith L ΓF)  (hE : 0 < E)
     (hW : IsTransport ΓF E W)
    y (hy : projObsDual W y = 0) :
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
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
  obtain ⟨α, hα0, hαT⟩ :=
    roughVekuaRegularCorrection_exists_periodic_of_projObsDual_eq_zero hΓLip hΓ hW y hy
  have hH2 := roughVekuaGauge_zero_memLp hΓLip hΓ hW
    (roughNormalizedPrimitive y) (roughNormalizedMean y) α
  refine ⟨α, hαT, hH2, ?_⟩
  apply localConformal_physicalMoments_nonpositive_of_memLp_of_smoothInverse
    hR F hFs hb hL hhol e he hsource hes _ hH2
  intro k
  simpa [physicalDrivenMoment, physicalDrivenCentered, mul_assoc] using roughVekuaGauge_physicalMoment_eq_zero hΓLip hΓ hW hE (roughNormalizedPrimitive y) (roughNormalizedMean y) α hαT 0 k

include hR hFs hb hL hhol e he hsource hes in
/-- Original normalized observation nullity gives the positive primitive
H1 regularity. Every gauge and Sobolev fact used here is constructed from
the true rough driven equation. -/
theorem localConformal_roughProjectedObservation_primitive_pos_one
     (hΓLip : LipschitzWith L ΓF)  (hE : 0 < E)
     (hW : IsTransport ΓF E W)
    y (hy : projObsDual W y = 0) :
    IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ) := by
  have hΓ :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
  obtain ⟨α, hαT, hH2, hHn⟩ :=
    localConformal_roughGauge_exists_nonpositive_of_projObsDual_eq_zero
      hR F hFs hb hL hhol e he hsource hes hΓLip hE hW y hy
  apply roughNormalizedPrimitive_pos_one_of_raw_hardy_split y _ _ hH2 (roughVekuaGauge_regular_memLp hΓLip hΓ hW (roughNormalizedPrimitive y) (roughNormalizedMean y) α 0) hHn (roughVekuaGauge_regular_isSobolevSeq_one hΓLip hΓ hW (roughNormalizedPrimitive y) (roughNormalizedMean y) α hαT)
  exact Eventually.of_forall (roughVekuaGauge_zero_split
    (roughNormalizedPrimitive y) (roughNormalizedMean y) α)

include hR hFs hb hL hhol e he hsource hes in
/-- Finite Fourier chart outputs acquire genuine half-order regularity
from their original normalized observation-null equation. No Sobolev or
gauge premise is imposed on the unknown chart vector. -/
theorem localConformal_finiteFourierChart_projectedObservation_kernel_half_regular
     (hΓLip : LipschitzWith L ΓF)  (hE : 0 < E)
     (hW : IsTransport ΓF E W)
     (u : Fin d → H₀ᗮ) v
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (z : H₀ᗮ) (hobs : projObsDual W (finiteFourierChart u v z) = 0) :
    IsSobolevSeq (1 / 2) (finiteFourierChart u v z : ℤ → ℂ) ∧
      IsSobolevSeq (1 / 2) ((z : L2Z) : ℤ → ℂ) := by
  exact finiteFourierChart_half_of_rough_primitive_pos_one u v hv z
    (localConformal_roughProjectedObservation_primitive_pos_one
      hR F hFs hb hL hhol e he hsource hes hΓLip hE hW _ hobs)

include hR hFs hb hL hhol hinj hC hK e he hsource hes in
/-- The full normalized projected-observation kernel of an actual
invertible finite Fourier conormal chart is zero. The half-order step is
proved above, so the true L2 conormal realization applies. -/
theorem localConformal_finiteFourierChart_projectedObservation_kernel_eq_zero
     (hΓLip : LipschitzWith L ΓF)  (hE : 0 < E)
     (hW : IsTransport ΓF E W)
     (u : Fin d → H₀ᗮ) v
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (hunit : IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
      (finiteFourierChart u v) ∘L H₀ᗮ.orthogonalProjection))
    (z : H₀ᗮ) (hobs : projObsDual W (finiteFourierChart u v z) = 0) : z = 0 := by
  exact localConformal_fixed_complement_half_regular_kernel_eq_zero
    hR F hFs hb hL hhol hinj hC hK e he hsource hes hΓLip hE hW
    (finiteFourierChart u v) hunit z ((localConformal_finiteFourierChart_projectedObservation_kernel_half_regular hR F hFs hb hL hhol e he hsource hes hΓLip hE hW u v hv z hobs).1) hobs

include hR hFs hb hL hhol hinj hC hK e he hsource hes in
theorem localConformal_finiteFourierChart_projectedObservation_injective
     (hΓLip : LipschitzWith L ΓF)  (hE : 0 < E)
     (hW : IsTransport ΓF E W)
     (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (hunit : IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
      (finiteFourierChart u v) ∘L H₀ᗮ.orthogonalProjection)) :
    Function.Injective ((projObsDual W).comp (finiteFourierChart u v)) := by
  intro z z' heq
  exact sub_eq_zero.mp
    (localConformal_finiteFourierChart_projectedObservation_kernel_eq_zero
      hR F hFs hb hL hhol hinj hC hK e he hsource hes hΓLip hE hW u v hv hunit (z - z') (by
        rw [map_sub, map_sub]
        change (projObsDual W).comp (finiteFourierChart u v) z -
          (projObsDual W).comp (finiteFourierChart u v) z' = 0
        rw [heq, sub_self]))

include hR hFs hb hL hhol hinj hC hK e he hsource hes in
/-- A genuine nonzero reference cut supplies an actual finite Fourier
complement with full normalized projected-observation injectivity. No
half-order hypothesis is added to its chart inputs. -/
theorem exists_localConformal_fixed_fourier_complement_projectedObservation_injective
     (hΓLip : LipschitzWith L ΓF)  (hE₀ : 0 < E₀)
     (hW : IsTransport ΓF E₀ W)
    (hcut : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → L2Z),
      (∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite) ∧
      (∀ r, (Function.support (v r : ℤ → ℂ)).Finite) ∧
      Function.Injective ((projObsDual W).comp (finiteFourierChart u v)) ∧
      ∃ U ∈ 𝓝 E₀,
        (∀ E ∈ U, IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
          (finiteFourierChart u v) ∘L H₀ᗮ.orthogonalProjection)) ∧
        ContinuousOn (fun E : ℝ => Ring.inverse
          ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
            (finiteFourierChart u v) ∘L H₀ᗮ.orthogonalProjection)) U := by
  obtain ⟨d, u, v, hu, hv, U, hU, hunit, hcont⟩ :=
    exists_localConformal_fixed_fourier_complement_of_cutC_ne_zero
      hR F hFs hb hL hhol hinj hC hK e he hsource hes hE₀.le hW hcut
  refine ⟨d, u, v, hu, hv, ?_, U, hU, hunit, hcont⟩
  exact localConformal_finiteFourierChart_projectedObservation_injective
    hR F hFs hb hL hhol hinj hC hK e he hsource hes hΓLip hE₀ hW u v hv
    (hunit E₀ (mem_of_mem_nhds hU))

end PhysicalCoordinates

end PolyaNeumann

end
