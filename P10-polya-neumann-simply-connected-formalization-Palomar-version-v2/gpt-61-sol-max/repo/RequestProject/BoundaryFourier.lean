module

public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import RequestProject.TraceH1
public import RequestProject.SobolevCircle
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier coordinates for the actual boundary L² space

The source uses ordinary coordinate measure `dθ` on `(0, 2π]`. Its unitary
Fourier coefficients are therefore `sqrt (2π)` times the averaged Fourier
coefficients. The map is constructed through actual Lp functions on the
circle, and its surjectivity follows by pulling those functions back to the
parameter interval. No norm or completeness identity is assumed.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Real



/-- Circle L² with Haar measure of total mass one. -/
abbrev BoundaryCircleHaarL2 := Lp ℂ 2
  (@AddCircle.haarAddCircle circlePeriod circlePeriodPositive)

private theorem boundaryCircle_ae_volume_iff {p : AddCircle circlePeriod → Prop} :
    (∀ᵐ q ∂(volume : Measure (AddCircle circlePeriod)), p q) ↔
      ∀ᵐ q ∂AddCircle.haarAddCircle, p q := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  have hs : ENNReal.ofReal circlePeriod ≠ 0 := by positivity
  simp_all

/-- Transport an a.e. equality on the interval through its actual representative map. -/
theorem boundary_liftIoc_congr_ae {f g : ComplexCurve}
    (h : f =ᵐ[volume.restrict boundaryHalfOpenInterval] g) :
    AddCircle.liftIoc circlePeriod 0 f =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIoc circlePeriod 0 g := by
  have hmp : MeasurePreserving
      (fun q : AddCircle circlePeriod => (AddCircle.equivIoc circlePeriod 0 q : ℝ))
      volume (volume.restrict boundaryHalfOpenInterval) := by
    simpa  [Function.comp_def] using
      (measurePreserving_subtype_coe measurableSet_Ioc).comp
        (AddCircle.measurePreserving_equivIoc circlePeriod (a := 0))
  apply boundaryCircle_ae_volume_iff.mp
  simpa  [AddCircle.liftIoc] using
    hmp.quasiMeasurePreserving.ae h

/-- Every actual boundary L² function has an L² circle lift, without a boundedness assumption. -/
theorem boundaryCircleLift_memLp (g : BoundaryL2) :
    MemLp (AddCircle.liftIoc circlePeriod 0 (g : ComplexCurve)) 2
      AddCircle.haarAddCircle := by
  have hg : MemLp (g : ComplexCurve) 2 (volume.restrict (Ioc 0 (0 + 2 * π))) := by
    simpa   using Lp.memLp g
  exact hg.memLp_liftIoc.haarAddCircle

/-- The unscaled circle lift; its squared norm is divided by `2π`. -/
def boundaryCircleLift g  :=
  (boundaryCircleLift_memLp g).toLp (AddCircle.liftIoc circlePeriod 0 (g : ComplexCurve))

theorem boundaryCircleLift_coe g :
    (boundaryCircleLift g : AddCircle circlePeriod → ℂ) =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIoc circlePeriod 0 (g : ComplexCurve) :=
  (boundaryCircleLift_memLp g).coeFn_toLp

def boundaryCircleLiftLin : BoundaryL2 →ₗ[ℂ] BoundaryCircleHaarL2 where
  toFun := boundaryCircleLift
  map_add' g h := by
    apply Lp.ext
    filter_upwards [boundaryCircleLift_coe (g + h),
      boundaryCircleLift_coe g, boundaryCircleLift_coe h,
      Lp.coeFn_add (boundaryCircleLift g) (boundaryCircleLift h),
      boundary_liftIoc_congr_ae (Lp.coeFn_add g h)] with q hgh hg hh hadd hlift
    measurability
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [boundaryCircleLift_coe (c • g), boundaryCircleLift_coe g,
      Lp.coeFn_smul c (boundaryCircleLift g),
      boundary_liftIoc_congr_ae (Lp.coeFn_smul c g)] with q hcg hg hsmul hlift
    measurability

private theorem boundary_integral_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : Lp ℂ 2 μ) : ∫ x, ‖f x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) f f)
  rw [inner_self_eq_norm_sq, ← integral_re (L2.integrable_inner f f)] at h
  simp_rw [inner_self_eq_norm_sq] at h
  exact h.symm

theorem boundaryCircleLift_norm_sq g :
    ‖boundaryCircleLift g‖ ^ 2 = circlePeriod⁻¹ * ‖g‖ ^ 2 := by
  calc
    ‖boundaryCircleLift g‖ ^ 2 =
        ∫ q : AddCircle circlePeriod, ‖boundaryCircleLift g q‖ ^ 2
          ∂AddCircle.haarAddCircle := (boundary_integral_norm_sq _).symm
    _ = ∫ q : AddCircle circlePeriod,
        ‖AddCircle.liftIoc circlePeriod 0 g q‖ ^ 2
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [boundaryCircleLift_coe g] with q hq
      rw [hq]
    _ = circlePeriod⁻¹ * ∫ θ in boundaryHalfOpenInterval, ‖g θ‖ ^ 2 := by
      rw [AddCircle.integral_haarAddCircle]
      change circlePeriod⁻¹ • (∫ q : AddCircle circlePeriod,
        AddCircle.liftIoc circlePeriod 0 (fun θ => ‖g θ‖ ^ 2) q) = _
      rw [AddCircle.integral_liftIoc_eq_intervalIntegral, zero_add,
        intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul]
    _ = circlePeriod⁻¹ * ‖g‖ ^ 2 := by rw [boundary_integral_norm_sq]

private theorem boundary_liftIoc_pullback (f : AddCircle circlePeriod → ℂ) :
    AddCircle.liftIoc circlePeriod 0 (fun θ : ℝ => f (θ : AddCircle circlePeriod)) = f := by
  funext q
  have hrep  :=
    (AddCircle.equivIoc circlePeriod 0).symm_apply_apply q
  exact congrArg f hrep

/-- Circle functions can all be recovered from actual L² functions on the parameter interval. -/
theorem boundaryCircleLift_surjective : Function.Surjective boundaryCircleLift := by
  intro f
  have hf  := (Lp.memLp f).of_haarAddCircle
  have hgp : MemLp (fun θ : ℝ => f (θ : AddCircle circlePeriod)) 2
      (volume.restrict boundaryHalfOpenInterval) := by
    simpa  [Function.comp_def] using
      hf.comp_measurePreserving (AddCircle.measurePreserving_mk circlePeriod 0)
  let g  := hgp.toLp (fun θ : ℝ => f θ)
  refine ⟨g, Lp.ext ?_⟩
  exact (boundaryCircleLift_coe g).trans
    ((boundary_liftIoc_congr_ae hgp.coeFn_toLp).trans
      (Eventually.of_forall (congrFun (boundary_liftIoc_pullback f))))

/-- Scaling the circle lift converts ordinary boundary measure to normalized Haar measure. -/
def boundaryCircleUnitaryLin : BoundaryL2 →ₗ[ℂ] BoundaryCircleHaarL2 :=
  (√circlePeriod : ℂ) • boundaryCircleLiftLin

theorem boundaryCircleUnitaryLin_norm g :
    ‖boundaryCircleUnitaryLin g‖ = ‖g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(√circlePeriod : ℂ) • boundaryCircleLift g‖ ^ 2 = ‖g‖ ^ 2
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt two_pi_pos.le, boundaryCircleLift_norm_sq,
    ← mul_assoc, mul_inv_cancel₀ two_pi_pos.ne', one_mul]

def boundaryCircleUnitaryIsometry : BoundaryL2 →ₗᵢ[ℂ] BoundaryCircleHaarL2 where
  toLinearMap := boundaryCircleUnitaryLin
  norm_map' := boundaryCircleUnitaryLin_norm

theorem boundaryCircleUnitary_surjective :
    Function.Surjective boundaryCircleUnitaryIsometry := by
  intro f
  obtain ⟨g, hg⟩ := boundaryCircleLift_surjective ((√circlePeriod)⁻¹ • f)
  refine ⟨g, ?_⟩
  change (√circlePeriod) • boundaryCircleLift g = f
  rw [hg, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast (Real.sqrt_pos.mpr two_pi_pos).ne'

def boundaryCircleUnitary  :=
  LinearIsometryEquiv.ofSurjective boundaryCircleUnitaryIsometry
    boundaryCircleUnitary_surjective

/-- The genuine unitary Fourier map from boundary L² with ordinary `dθ` to `ℓ²(ℤ)`. -/
def boundaryFourier : BoundaryL2 ≃ₗᵢ[ℂ] L2Z :=
  boundaryCircleUnitary.trans (fourierBasis (T := 2 * π)).repr

/-- Its coordinates are the orthonormal Fourier coefficients for ordinary parameter measure. -/
theorem boundaryFourier_apply g n :
    boundaryFourier g n = (√circlePeriod : ℂ) *
      fourierCoeffOn two_pi_pos (g : ComplexCurve) n := by
  change (fourierBasis (T := 2 * π)).repr
    ((√circlePeriod : ℂ) • boundaryCircleLift g) n = _
  rw [fourierBasis_repr,
    fourierCoeff_congr_ae (Lp.coeFn_smul (√circlePeriod : ℂ) (boundaryCircleLift g)),
    fourierCoeff.const_smul,
    fourierCoeff_congr_ae (boundaryCircleLift_coe g), fourierCoeff_liftIoc_eq]
  simp  

/-- Fourier coordinates can be computed using any almost-everywhere representative. -/
theorem boundaryFourier_congr_ae (v : BoundaryL2)
    (hv : (v : ComplexCurve) =ᵐ[volume.restrict boundaryHalfOpenInterval] f) n :
    boundaryFourier v n = (Real.sqrt circlePeriod : ℂ) *
      fourierCoeffOn Real.two_pi_pos f n := by
  rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hv]

/-- The half-open representatives differ only at the identified endpoint, a Haar-null point. -/
theorem boundary_liftIoc_eq_liftIco_ae (f : ComplexCurve) :
    AddCircle.liftIoc circlePeriod 0 f =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIco circlePeriod 0 f := by
  have hv : (volume : Measure (AddCircle circlePeriod)) {0} = 0 := by
    have h := AddCircle.volume_closedBall (T := 2 * π) (x := 0) 0
    simp_all
  have hh : (@AddCircle.haarAddCircle circlePeriod _) {0} = 0 := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul] at hv
    exact (mul_eq_zero.mp hv).resolve_left (by positivity)
  have hne : ∀ᵐ q : AddCircle circlePeriod ∂AddCircle.haarAddCircle, q ≠ 0 := by
    rw [ae_iff]
    simp_all
  filter_upwards [hne] with q hq
  exact?

end PolyaNeumann

end
