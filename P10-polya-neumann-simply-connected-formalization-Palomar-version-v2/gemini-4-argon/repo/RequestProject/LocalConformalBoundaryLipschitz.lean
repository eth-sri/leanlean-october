module

public import RequestProject.LocalConformalArcReparam
public import Mathlib.Analysis.Complex.Angle

/-!
# Genuine chord bounds for supplied physical boundary coordinates

A compact smooth physical extension of the actual inverse coordinate is
globally Lipschitz. Its proved values on the closed-disk image therefore
give a true inverse chord bound. A C1 periodic density has a globally bounded
derivative, obtained on one compact period and extended by periodicity.

The shortest angular difference is bounded by pi/2 times the unit-circle
chord, using Mathlib's actual arc/chord estimate. Combining these results
proves a finite chord-Lipschitz bound for the density on the physical circle
trace. Neither a chord bound nor a density extension is assumed. Initial
conformal-map existence remains a separate obligation.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology ContDiff

/-- A C1 periodic density has a genuine global derivative bound and is
globally Lipschitz, without requiring a nonzero derivative. -/
theorem exists_periodic_C1_density_lipschitz (K : ℝ → ℂ)
    (hK : ContDiff ℝ 1 K) (hper : Function.Periodic K (2 * Real.pi)) :
    ∃ L : NNReal, LipschitzWith L K := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 (2 * Real.pi)) hK.continuous_deriv_one.continuousOn
  have hbound θ : ‖deriv K θ‖ ≤ M := by
    let θ' := toIcoMod Real.two_pi_pos 0 θ
    rw [← (show ‖deriv K θ'‖ = ‖deriv K θ‖ by
      dsimp only [θ']
      rw [toIcoMod, (show Function.Periodic (fun θ => ‖deriv K θ‖) (2 * Real.pi) by
        intro θ
        exact congrArg (fun z => ‖z‖) (deriv_periodic hper θ)).sub_zsmul_eq])]
    exact hM θ' (Ico_subset_Icc_self (by
      simpa [θ'] using toIcoMod_mem_Ico Real.two_pi_pos 0 θ))
  refine ⟨Real.toNNReal M, ?_⟩
  apply lipschitzWith_of_nnnorm_deriv_le hK.differentiable_one
  intro θ
  apply NNReal.coe_le_coe.mp
  change ‖deriv K θ‖ ≤ _
  rw [Real.coe_toNNReal _ ((norm_nonneg (deriv K 0)).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩))]
  exact hbound θ

/-- A true angular Lipschitz bound plus periodicity gives a chord bound on
the circle. The representative used is the actual shortest angular shift. -/
local notation "Φ0" => circleMap 0 1

theorem periodic_density_chord_bound {K : ℝ → ℂ} 
    (hK : LipschitzWith L K) (hper : Function.Periodic K (2 * Real.pi))
    θ τ :
    ‖K θ - K τ‖ ≤ (L : ℝ) * (Real.pi / 2) *
      ‖Φ0 θ - Φ0 τ‖ := by
  let r := toIocMod Real.two_pi_pos (-Real.pi) (θ - τ)
  calc
    _ ≤ _ := show ‖K θ - K τ‖ ≤ L * |r| by
      simpa [show K (τ + r) = K θ by
        rw [show τ + r = θ - toIocDiv Real.two_pi_pos (-Real.pi) (θ - τ) • (2 * Real.pi) by
          dsimp only [r, toIocMod]
          abel]
        exact hper.sub_zsmul_eq _, dist_eq_norm, Real.dist_eq] using
        hK.dist_le_mul (τ + r) τ
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (show |toIocMod Real.two_pi_pos (-Real.pi) (θ - τ)| ≤ Real.pi / 2 * ‖Φ0 θ - Φ0 τ‖ by
        simpa [circleMap, Complex.angle_exp_exp] using (Complex.angle_le_mul_norm_sub (x := Φ0 θ) (y := Φ0 τ) (by simp) (by simp))) L.coe_nonneg
    _ = _ := by ring

/-- The same physical density bound with the genuine inverse constructed
from the supplied map, rather than included as separate coordinate data. -/
theorem exists_localConformal_boundaryDensity_chord_bound_of_nonzeroDifferential
     (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hhol : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (closedBall 0 1))
    (hnz : ∀ z ∈ closedBall 0 1, fderiv ℝ F z 1 ≠ 0)
    (K : ℝ → ℂ) (hK : ContDiff ℝ 1 K)
    (hper : Function.Periodic K (2 * Real.pi)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ θ τ : ℝ,
      ‖K θ - K τ‖ ≤ L * ‖physicalCircleTrace F θ - physicalCircleTrace F τ‖ := by
  obtain ⟨e, he, hsource, _, hes⟩ := exists_localConformalInverse hR F hFs hhol hinj hnz
  exact (by
    obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ z₁ ∈ closedBall 0 1, ∀ z₂ ∈ closedBall 0 1, ‖z₁ - z₂‖ ≤ C * ‖F z₁ - F z₂‖ := by
      obtain ⟨f, hf, hfe⟩ := localSmoothInverse_testFunction e hes
        (isCompact_closedBall 0 1) hsource
        (contDiff_id : ContDiff ℝ ∞ (fun z => z))
      obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hf.2.1 hf.1 (by simp)
      have hvalue z (hz : z ∈ closedBall 0 1) : f (F z) = z := by
        have hp := (hfe (e z) (mem_image_of_mem e hz)).self_of_nhds
        change f (e z) = e.symm (e z) at hp
        rw [e.left_inv (hsource hz)] at hp
        simpa [he] using hp
      refine ⟨K, K.coe_nonneg, ?_⟩
      intro z₁ hz₁ z₂ hz₂
      simpa [dist_eq_norm, hvalue z₁ hz₁, hvalue z₂ hz₂] using
        hK.dist_le_mul (F z₁) (F z₂)
    obtain ⟨M, hM0, hM⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ θ τ : ℝ, ‖K θ - K τ‖ ≤ L * ‖Φ0 θ - Φ0 τ‖ := by
      obtain ⟨M, hM⟩ := exists_periodic_C1_density_lipschitz K hK hper
      exact ⟨M * (Real.pi / 2), mul_nonneg M.coe_nonneg (by positivity),
        periodic_density_chord_bound hM hper⟩
    refine ⟨M * C, mul_nonneg hM0 hC0, ?_⟩
    intro θ τ
    change ‖K θ - K τ‖ ≤ M * C *
      ‖F (Φ0 θ) - F (Φ0 τ)‖
    calc
      _ ≤ _ := hM θ τ
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left (hC (Φ0 θ) (circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ) (Φ0 τ) (circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) τ)) hM0
      _ = _ := by ring)

end PolyaNeumann

end
