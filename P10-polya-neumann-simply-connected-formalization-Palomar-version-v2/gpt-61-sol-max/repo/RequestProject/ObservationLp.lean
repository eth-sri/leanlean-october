module

public import RequestProject.PlanarTypes

public import RequestProject.CirclePeriod

public import RequestProject.PlanarGeometry

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import RequestProject.BoundaryFourier
public import RequestProject.ObservationDual

/-!
# The projected observation on actual boundary L²

The Fourier synthesis operator is identified with the actual observation
integral for every L² input, including representatives which are neither
continuous nor bounded. Boundary measure is ordinary `dθ`. Thus the input
to the existing synthesis operator is `sqrt (2π) Λ⁻¹ᐟ² boundaryFourier g`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology Real
open scoped Real ComplexConjugate InnerProductSpace



private lemma smoothing_half_apply f n :
    sobolevSmoothing (1 / 2 : ℝ) (by norm_num) f n =
      (Real.sqrt (1 + |(n : ℝ)|) : ℂ)⁻¹ * f n := by
  change ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ)) * f n = _
  rw [Real.rpow_neg (sobWeight_pos n).le, ← Real.sqrt_eq_rpow,
    Complex.ofReal_inv]
  rfl

section Physical

variable {γ : ComplexCurve} {K : NNReal} {E : ℝ}
  {W : ℝ → ComplexEnd Ell2}

section
variable (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (v : Ell2)

include hK hW v in
theorem memLp_projectedObservation :
    MemLp (fun θ => ⟪projObsRow W θ, v⟫_ℂ) 2
      (volume.restrict boundaryHalfOpenInterval) := by
  have hc : ContinuousOn (fun θ => ⟪projObsRow W θ, v⟫_ℂ)
      boundaryHalfOpenInterval :=
    ((continuousOn_projObsRow hK hW).mono Ioc_subset_Icc_self).inner continuousOn_const
  refine MemLp.of_bound (hc.aestronglyMeasurable measurableSet_Ioc) ‖v‖ ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  calc
    ‖⟪projObsRow W θ, v⟫_ℂ‖ ≤ ‖projObsRow W θ‖ * ‖v‖ := norm_inner_le_norm _ _
    _ ≤ 1 * ‖v‖ := by
      gcongr
      exact norm_projObsRow_le hK hW (Ioc_subset_Icc_self hθ)
    _ = ‖v‖ := one_mul _

/-- The actual projected observation as an ordinary boundary L² element. -/
def projectedObservationBoundary (hK : LipschitzWith K γ)
    (hW : IsTransport γ E W) v  :=
  (memLp_projectedObservation hK hW v).toLp (fun θ => ⟪projObsRow W θ, v⟫_ℂ)

section
include hK hW v

theorem projectedObservationBoundary_coe :
    (projectedObservationBoundary hK hW v : ComplexCurve) =ᵐ[
      volume.restrict boundaryHalfOpenInterval]
        (fun θ => ⟪projObsRow W θ, v⟫_ℂ) :=
  (memLp_projectedObservation hK hW v).coeFn_toLp

theorem boundaryFourier_projectedObservation n :
    boundaryFourier (projectedObservationBoundary hK hW v) n =
      (√circlePeriod : ℂ) * ⟪projObsCoeffVec W n, v⟫_ℂ := by
  rw [boundaryFourier_apply]
  congr 1
  rw [inner_projObsCoeffVec hK hW]
  refine (congrFun (fourierCoeffOn_congr_ae two_pi_pos
    (projectedObservationBoundary_coe hK hW v)) n).trans ?_
  exact congrFun (fourierCoeffOn_congr_ae two_pi_pos
    (Eventually.of_forall fun θ => (observation_cutProj_eq W v θ).symm)) n

end


end


section
variable (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (g : BoundaryL2)
include hK hW g

/-- The Fourier identification holds for all actual L² boundary data. -/
theorem projObsDual_boundary_inner (v : Ell2) :
    ⟪v, projObsDual W ((√circlePeriod : ℂ) •
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier g))⟫_ℂ =
        ⟪projectedObservationBoundary hK hW v, g⟫_ℂ := by
  rw [projObsDual_eq hK hW, inner_rowSynth]
  have hterm (n : ℤ) :
      ⟪v, normProjObsRow W n⟫_ℂ *
          (((√circlePeriod : ℂ) • sobolevSmoothing (1 / 2 : ℝ)
            (by norm_num) (boundaryFourier g)) : L2Z) n =
        ⟪boundaryFourier (projectedObservationBoundary hK hW v) n,
          boundaryFourier g n⟫_ℂ := by
    have hn : (Real.sqrt (1 + |(n : ℝ)|) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
    rw [normProjObsRow, inner_smul_right, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, smoothing_half_apply, boundaryFourier_projectedObservation,
      RCLike.inner_apply', map_mul, Complex.conj_ofReal,
      ← inner_conj_symm]
    field_simp
  simp_rw [hterm]
  exact boundaryFourier.inner_map_map _ _

theorem projObsDual_boundary_integral (v : Ell2) :
    ⟪v, projObsDual W ((√circlePeriod : ℂ) •
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier g))⟫_ℂ =
        ∫ θ in boundaryHalfOpenInterval, conj (⟪projObsRow W θ, v⟫_ℂ) * g θ := by
  rw [projObsDual_boundary_inner hK hW, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [projectedObservationBoundary_coe hK hW v] with θ hθ
  simp only [RCLike.inner_apply', hθ]

theorem integrable_boundary_observation_load :
    Integrable (fun θ => g θ • ContinuousLinearMap.adjoint (W θ) (basisVec 0))
      (volume.restrict boundaryHalfOpenInterval) := by
  have hc  :=
    (continuousOn_adjoint_apply hW.1 (basisVec 0)).mono Ioc_subset_Icc_self
  have hg  :=
    (Lp.memLp g).integrable one_le_two
  refine hg.smul_bdd 1 (hc.aestronglyMeasurable measurableSet_Ioc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  refine ((ContinuousLinearMap.adjoint (W θ)).le_opNorm (basisVec 0)).trans ?_
  rw [LinearIsometryEquiv.norm_map, show ‖basisVec 0‖ = 1 by simp [basisVec], mul_one]
  exact norm_transport_le_one hK hW (Ioc_subset_Icc_self hθ)

/-- The old pointwise integral agrees with the genuine bounded L² operator.
No continuity or pointwise bound on the input representative is required. -/
theorem projObsDual_boundary_normalized :
    projObsDual W ((√circlePeriod : ℂ) •
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier g)) =
        cutProj (cutC (W circlePeriod) (basisVec 0))
          (observationAdj W (g : ComplexCurve)) := by
  apply ext_inner_left ℂ
  intro v
  rw [projObsDual_boundary_integral hK hW, ← inner_cutProj_left, observationAdj]
  have hi  :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).mpr
      (integrable_boundary_observation_load hK hW g)
  have h := ContinuousLinearMap.intervalIntegral_comp_comm
    (innerSL ℂ (cutProj (cutC (W circlePeriod) (basisVec 0)) v)) hi
  simp only [innerSL_apply_apply] at h
  rw [← h, intervalIntegral.integral_of_le two_pi_pos.le]
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => by
    change conj (⟪projObsRow W θ, v⟫_ℂ) * g θ =
      ⟪cutProj (cutC (W circlePeriod) (basisVec 0)) v,
        g θ • ContinuousLinearMap.adjoint (W θ) (basisVec 0)⟫_ℂ
    rw [inner_smul_right, inner_cutProj_left, ← inner_conj_symm]
    simp  
    exact mul_comm _ _

end


end Physical

end PolyaNeumann

end
