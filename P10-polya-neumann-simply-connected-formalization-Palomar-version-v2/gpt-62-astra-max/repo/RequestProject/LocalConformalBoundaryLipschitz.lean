module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalArcReparam
public import Mathlib.Analysis.Complex.Angle
public import RequestProject.PlanarNotation

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

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology

section

variable (F : ℂ → ℂ) (Φ : SmoothDiskMap) (e : OpenPartialHomeomorph ℂ ℂ)
    (hhol : DifferentiableOn ℂ Φ.map unitDisk) (he : (e : ℂ → ℂ) = F)
    (hinj : InjOn Φ.map closedDisk) (hsource : closedDisk ⊆ e.source)
    (hnz : ∀ z ∈ closedDisk, fderiv ℝ Φ.map z 1 ≠ 0) (hes : ContDiffOn ℝ ∞ e.symm e.target)
    (K : ℝ → ℂ) (hK : ContDiff ℝ 1 K) (hper : Function.Periodic K anglePeriod)

include he hes hsource in
/-- The actual smooth inverse has a compact physical extension, whose
genuine global Lipschitz bound controls inverse chords on the closed disk. -/
theorem exists_localConformal_inverse_chord_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z₁ ∈ closedDisk,
      ∀ z₂ ∈ closedDisk,
        ‖z₁ - z₂‖ ≤ C * ‖F z₁ - F z₂‖ := by
  obtain ⟨f, hf, hfe⟩ := localSmoothInverse_testFunction e hes
    (isCompact_closedBall 0 1) hsource
    contDiff_id
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hf.2.1 hf.1 (by simp)
  have hvalue (z : ℂ) (hz : z ∈ closedDisk) : f (F z) = z := by
    have hp := (hfe (e z) (mem_image_of_mem e hz)).self_of_nhds
    change f (e z) = e.symm (e z) at hp
    rw [e.left_inv (hsource hz)] at hp
    simpa [he] using hp
  refine ⟨K, K.coe_nonneg, ?_⟩
  intro z₁ hz₁ z₂ hz₂
  simpa [dist_eq_norm, hvalue z₁ hz₁, hvalue z₂ hz₂] using
    hK.dist_le_mul (F z₁) (F z₂)

include hK hper in
/-- A C1 periodic density has a genuine global derivative bound and is
globally Lipschitz, without requiring a nonzero derivative. -/
theorem exists_periodic_C1_density_lipschitz :
    ∃ L : NNReal, LipschitzWith L K := by
  have hsp : Function.Periodic (fun θ => ‖deriv K θ‖) anglePeriod := by
    intro θ
    exact congrArg (fun z : ℂ => ‖z‖) (deriv_periodic hper θ)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
     hK.continuous_deriv_one.continuousOn
  
  have hbound (θ : ℝ) : ‖deriv K θ‖ ≤ M := by
    let θ' := toIcoMod Real.two_pi_pos 0 θ
    have hθ' : θ' ∈ angleIco := by
      simpa only [zero_add, θ'] using toIcoMod_mem_Ico Real.two_pi_pos 0 θ
    have heq : ‖deriv K θ'‖ = ‖deriv K θ‖ := by
      dsimp only [θ']
      rw [toIcoMod, hsp.sub_zsmul_eq]
    rw [← heq]
    exact hM θ' (Ico_subset_Icc_self hθ')
  refine ⟨Real.toNNReal M, ?_⟩
  apply lipschitzWith_of_nnnorm_deriv_le hK.differentiable_one
  intro θ
  apply NNReal.coe_le_coe.mp
  
  simp [*]

/-- The actual shortest angular distance is at most pi/2 times the actual
unit-circle chord. -/
theorem unitCircle_arcDistance_le_chord (θ τ : ℝ) :
    |toIocMod Real.two_pi_pos (-Real.pi) (θ - τ)| ≤
      Real.pi / 2 * ‖unitCirclePt θ - unitCirclePt τ‖ := by
  have h := Complex.angle_le_mul_norm_sub
    (x := unitCirclePt θ) (y := unitCirclePt τ) (by simp) (by simp)
  simpa [circleMap, Complex.ofReal_one, Complex.angle_exp_exp] using h

/-- A true angular Lipschitz bound plus periodicity gives a chord bound on
the circle. The representative used is the actual shortest angular shift. -/
theorem periodic_density_chord_bound {K : ℝ → ℂ} {L : NNReal}
    (hK : LipschitzWith L K) (hper : Function.Periodic K anglePeriod)
    (θ τ : ℝ) :
    ‖K θ - K τ‖ ≤ ((L : ℝ) * (Real.pi / 2)) *
      ‖unitCirclePt θ - unitCirclePt τ‖ := by
  let r := toIocMod Real.two_pi_pos (-Real.pi) (θ - τ)
  have hshift : τ + r = θ -
      toIocDiv Real.two_pi_pos (-Real.pi) (θ - τ) • anglePeriod := by
    dsimp only [r, toIocMod]
    abel
  have hvalue : K (τ + r) = K θ := by
    rw [hshift]
    exact hper.sub_zsmul_eq _
  have hangle : ‖K θ - K τ‖ ≤ (L : ℝ) * |r| := by
    simpa only [hvalue, dist_eq_norm, Real.dist_eq, Real.norm_eq_abs, add_sub_cancel_left] using
      hK.dist_le_mul (τ + r) τ
  calc
    _ ≤ _ := hangle
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (unitCircle_arcDistance_le_chord θ τ) L.coe_nonneg
    _ = _ := by ring

include hK hper in
theorem exists_periodic_C1_density_chord_bound :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ θ τ : ℝ,
      ‖K θ - K τ‖ ≤ L * ‖unitCirclePt θ - unitCirclePt τ‖ := by
  obtain ⟨M, hM⟩ := exists_periodic_C1_density_lipschitz K hK hper
  exact ⟨M * (Real.pi / 2), (by positivity),
    periodic_density_chord_bound hM hper⟩

include hK he hes hper hsource in
/-- The actual density is Lipschitz in physical boundary chords. The
constant is derived from the supplied inverse and the actual periodic C1
density; it is not assumed as a replacement geometric hypothesis. -/
theorem exists_localConformal_boundaryDensity_chord_bound :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ θ τ : ℝ,
      ‖K θ - K τ‖ ≤ L * ‖physicalCircleTrace F θ - physicalCircleTrace F τ‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_localConformal_inverse_chord_bound F e he hsource hes
  obtain ⟨M, hM0, hM⟩ := exists_periodic_C1_density_chord_bound K hK hper
  refine ⟨M * C, mul_nonneg hM0 hC0, ?_⟩
  intro θ τ
  have hchord := hC (unitCirclePt θ)
    (circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) θ)
    (unitCirclePt τ)
    (circleMap_mem_closedBall (0 : ℂ) (by norm_num : (0 : ℝ) ≤ 1) τ)
  change ‖K θ - K τ‖ ≤ (M * C) *
    ‖F (unitCirclePt θ) - F (unitCirclePt τ)‖
  calc
    _ ≤ _ := hM θ τ
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left hchord hM0
    _ = _ := by ring

include hK hhol hinj hnz hper in
/-- The same physical density bound with the genuine inverse constructed
from the supplied map, rather than included as separate coordinate data. -/
theorem exists_localConformal_boundaryDensity_chord_bound_of_nonzeroDifferential :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ θ τ : ℝ,
      ‖K θ - K τ‖ ≤ L * ‖Φ.boundary θ - Φ.boundary τ‖ := by
  obtain ⟨e, he, hsource, _, hes⟩ := exists_localConformalInverse Φ hhol hinj hnz
  exact exists_localConformal_boundaryDensity_chord_bound Φ.map e he hsource hes K hK hper

end

end PolyaNeumann

end
