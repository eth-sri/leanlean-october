module

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
open scoped InnerProductSpace ComplexConjugate

local instance boundaryFourierTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- Circle L² with Haar measure of total mass one. -/
abbrev BoundaryCircleHaarL2 := Lp ℂ 2
  (@AddCircle.haarAddCircle (2 * π) boundaryFourierTwoPiPos)

private theorem boundaryCircle_ae_volume_iff {p : AddCircle (2 * π) → Prop} :
    (∀ᵐ q ∂(volume : Measure (AddCircle (2 * π))), p q) ↔
      ∀ᵐ q ∂AddCircle.haarAddCircle, p q := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, show ENNReal.ofReal (2 * π) ≠ 0 by positivity, false_or]

/-- Transport an a.e. equality on the interval through its actual representative map. -/
theorem boundary_liftIoc_congr_ae {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Ioc 0 (2 * π))] g) :
    AddCircle.liftIoc (2 * π) 0 f =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIoc (2 * π) 0 g := by
  apply boundaryCircle_ae_volume_iff.mp
  simpa [AddCircle.liftIoc, Set.restrict_def, Function.comp_def] using
    (show MeasurePreserving (fun q : AddCircle (2 * π) => (AddCircle.equivIoc (2 * π) 0 q : ℝ)) volume (volume.restrict (Ioc 0 (2 * π))) by
      simpa [Function.comp_def] using
        (measurePreserving_subtype_coe measurableSet_Ioc).comp
          (AddCircle.measurePreserving_equivIoc (2 * π) (a := 0))).quasiMeasurePreserving.ae h

/-- Every actual boundary L² function has an L² circle lift, without a boundedness assumption. -/
theorem boundaryCircleLift_memLp (g : BoundaryL2) :
    MemLp (AddCircle.liftIoc (2 * π) 0 (g : ℝ → ℂ)) 2
      AddCircle.haarAddCircle := by
  exact (show MemLp g 2 (volume.restrict (Ioc 0 (0 + 2 * π))) by
    simpa using Lp.memLp g).memLp_liftIoc.haarAddCircle

/-- The unscaled circle lift; its squared norm is divided by `2π`. -/
def boundaryCircleLift (g : BoundaryL2) : BoundaryCircleHaarL2 :=
  (boundaryCircleLift_memLp g).toLp (AddCircle.liftIoc (2 * π) 0 (g : ℝ → ℂ))

theorem boundaryCircleLift_coe (g : BoundaryL2) :
    (boundaryCircleLift g : AddCircle (2 * π) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIoc (2 * π) 0 (g : ℝ → ℂ) :=
  (boundaryCircleLift_memLp g).coeFn_toLp

def boundaryCircleLiftLin : BoundaryL2 →ₗ[ℂ] BoundaryCircleHaarL2 where
  toFun := boundaryCircleLift
  map_add' g h := by
    apply Lp.ext
    filter_upwards [boundaryCircleLift_coe (g + h),
      boundaryCircleLift_coe g, boundaryCircleLift_coe h,
      Lp.coeFn_add (boundaryCircleLift g) (boundaryCircleLift h),
      boundary_liftIoc_congr_ae (Lp.coeFn_add g h)] with q hgh hg hh hadd hlift
    change boundaryCircleLift (g + h) q = (boundaryCircleLift g + boundaryCircleLift h) q
    rw [hgh, hadd]
    change AddCircle.liftIoc (2 * π) 0 ((g + h : BoundaryL2) : ℝ → ℂ) q =
      boundaryCircleLift g q + boundaryCircleLift h q
    rw [hg, hh, hlift]
    rfl
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [boundaryCircleLift_coe (c • g), boundaryCircleLift_coe g,
      Lp.coeFn_smul c (boundaryCircleLift g),
      boundary_liftIoc_congr_ae (Lp.coeFn_smul c g)] with q hcg hg hsmul hlift
    change boundaryCircleLift (c • g) q = (c • boundaryCircleLift g) q
    rw [hcg, hsmul]
    change AddCircle.liftIoc (2 * π) 0 ((c • g : BoundaryL2) : ℝ → ℂ) q =
      c • boundaryCircleLift g q
    rw [hg, hlift]
    rfl

private theorem boundary_integral_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : Lp ℂ 2 μ) : ∫ x, ‖f x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) f f)
  rw [inner_self_eq_norm_sq, ← integral_re (L2.integrable_inner f f)] at h
  simp_rw [inner_self_eq_norm_sq] at h
  exact h.symm

def boundaryCircleUnitaryLin : BoundaryL2 →ₗ[ℂ] BoundaryCircleHaarL2 :=
  (√(2 * π) : ℂ) • boundaryCircleLiftLin

theorem boundaryCircleUnitaryLin_norm (g : BoundaryL2) :
    ‖boundaryCircleUnitaryLin g‖ = ‖g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(√(2 * π) : ℂ) • boundaryCircleLift g‖ ^ 2 = _
  have h_inl g : ‖boundaryCircleLift g‖ ^ 2 = (2 * π)⁻¹ * ‖g‖ ^ 2 := by
    calc
      _ = _ := (boundary_integral_norm_sq _).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [boundaryCircleLift_coe g] with q hq
        rw [hq]
      _ = (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), ‖g θ‖ ^ 2 := by
        rw [AddCircle.integral_haarAddCircle]
        change (2 * π)⁻¹ • (∫ q : AddCircle (2 * π),
          AddCircle.liftIoc (2 * π) 0 (fun θ => ‖g θ‖ ^ 2) q) = _
        rw [AddCircle.integral_liftIoc_eq_intervalIntegral, zero_add,
          intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul]
      _ = (2 * π)⁻¹ * ‖g‖ ^ 2 := by rw [boundary_integral_norm_sq]
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt two_pi_pos.le, h_inl,
    ← mul_assoc, mul_inv_cancel₀ two_pi_pos.ne', one_mul]

def boundaryCircleUnitaryIsometry : BoundaryL2 →ₗᵢ[ℂ] BoundaryCircleHaarL2 where
  toLinearMap := boundaryCircleUnitaryLin
  norm_map' := boundaryCircleUnitaryLin_norm

def boundaryCircleUnitary : BoundaryL2 ≃ₗᵢ[ℂ] BoundaryCircleHaarL2 :=
  LinearIsometryEquiv.ofSurjective boundaryCircleUnitaryIsometry
    (show Function.Surjective boundaryCircleUnitaryIsometry by
      intro f
      obtain ⟨g, hg⟩ := (show Function.Surjective boundaryCircleLift by
        intro f
        have hgp : MemLp (fun θ : ℝ => f (θ : AddCircle (2 * π))) 2
            (volume.restrict (Ioc 0 (2 * π))) := by
          simpa [Function.comp_def] using
            ((Lp.memLp f).of_haarAddCircle).comp_measurePreserving (AddCircle.measurePreserving_mk (2 * π) 0)
        let g := hgp.toLp (fun θ : ℝ => f (θ : AddCircle (2 * π)))
        refine ⟨g, Lp.ext ?_⟩
        exact (boundaryCircleLift_coe g).trans
          ((boundary_liftIoc_congr_ae hgp.coeFn_toLp).trans
            (Eventually.of_forall fun q => congrFun (show AddCircle.liftIoc (2 * π) 0 (fun θ => f (θ : AddCircle (2 * π))) = f by
              funext q
              exact congrArg f ((AddCircle.equivIoc (2 * π) 0).symm_apply_apply q)) q))) ((√(2 * π) : ℂ)⁻¹ • f)
      refine ⟨g, ?_⟩
      change (√(2 * π) : ℂ) • boundaryCircleLift g = f
      rw [hg, smul_smul, mul_inv_cancel₀, one_smul]
      exact_mod_cast (Real.sqrt_pos.mpr two_pi_pos).ne')

/-- The genuine unitary Fourier map from boundary L² with ordinary `dθ` to `ℓ²(ℤ)`. -/
def boundaryFourier : BoundaryL2 ≃ₗᵢ[ℂ] L2Z :=
  boundaryCircleUnitary.trans (fourierBasis (T := 2 * π)).repr

/-- Its coordinates are the orthonormal Fourier coefficients for ordinary parameter measure. -/
theorem boundaryFourier_apply (g : BoundaryL2) n :
    boundaryFourier g n = (√(2 * π) : ℂ) *
      fourierCoeffOn two_pi_pos (g : ℝ → ℂ) n := by
  change (fourierBasis (T := 2 * π)).repr
    ((√(2 * π) : ℂ) • boundaryCircleLift g) n = _
  rw [fourierBasis_repr,
    fourierCoeff_congr_ae (Lp.coeFn_smul (√(2 * π) : ℂ) (boundaryCircleLift g)),
    fourierCoeff.const_smul,
    fourierCoeff_congr_ae (boundaryCircleLift_coe g), fourierCoeff_liftIoc_eq]
  simp

/-- The half-open representatives differ only at the identified endpoint, a Haar-null point. -/
theorem boundary_liftIoc_eq_liftIco_ae (f : ℝ → ℂ) :
    AddCircle.liftIoc (2 * π) 0 f =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIco (2 * π) 0 f := by
  have hv : (volume : Measure (AddCircle (2 * π))) {0} = 0 := by
    have h := AddCircle.volume_closedBall (T := 2 * π) (x := 0) 0
    simpa [min_eq_right two_pi_pos.le] using h
  filter_upwards [show ∀ᵐ q : AddCircle (2 * π) ∂AddCircle.haarAddCircle, q ≠ 0 by
    rw [ae_iff]
    simpa [Set.setOf_eq_eq_singleton] using show (@AddCircle.haarAddCircle (2 * π) _) {0} = 0 by
      rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul] at hv
      exact (mul_eq_zero.mp hv).resolve_left (by positivity)] with q hq
  obtain ⟨θ, hθ, rfl⟩ := AddCircle.eq_coe_Ico q
  have hθ0 : θ ≠ 0 := fun h => hq (by rw [h]; rfl)
  have hθpos := lt_of_le_of_ne hθ.1 hθ0.symm
  rw [AddCircle.liftIoc_zero_coe_apply ⟨hθpos, hθ.2.le⟩,
    AddCircle.liftIco_zero_coe_apply hθ]

end PolyaNeumann

end
