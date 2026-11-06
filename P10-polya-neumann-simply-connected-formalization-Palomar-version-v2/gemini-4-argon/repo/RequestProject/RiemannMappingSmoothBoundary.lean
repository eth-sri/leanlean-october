module

public import RequestProject.RiemannMappingCaratheodory
public import RequestProject.RiemannMappingEnergy
public import RequestProject.SmoothDomain
public import RequestProject.LocalConformalH1
public import RequestProject.DiskGeometry
public import RequestProject.SmoothCompactExtension
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The actual physical Green function for boundary regularity

This file constructs the continuous physical inverse of the actual
closed-disk Riemann map. Its negative log modulus is the genuine
positive, zero-boundary Green function away from the actual pole.
Removing that logarithmic pole produces a harmonic function on the
whole physical domain whose actual boundary data are smooth. The
correction has a genuine H¹ realization. Actual smooth graph geometry
and the Schwarz lemma also supply positive interior tangent-ball
Green barriers, without assuming boundary derivatives.

These are consequences of the original physical domain assumptions.
They do not assert Kellogg--Warschawski regularity or a real smooth
collar extension. Smooth Dirichlet boundary regularity and real jet
extension remain necessary for those conclusions. The proved barrier
is available to exclude a zero boundary derivative once genuine
boundary differentiability has been constructed.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory InnerProductSpace
open scoped Topology ContDiff InnerProductSpace

variable {f : ℂ → ℂ} {a b : ℂ}

/-- The actual inverse of the closed-disk extension on its physical
compact image. Its values outside that image are immaterial. -/
def riemannMappingClosedInverse (F : ℂ → ℂ) : ℂ → ℂ :=
  Function.invFunOn (riemannMappingClosedExtension F) (closedBall 0 1)

/-- The Green function with pole at the actual interior point `F 0`.
The total-function value at the pole is immaterial. -/
def riemannMappingGreen (F : ℂ → ℂ) (w : ℂ) : ℝ :=
  -Real.log ‖riemannMappingClosedInverse F w‖

/-- The actual analytic divided difference of the inverse at the pole;
its value at the pole is the genuine inverse derivative. -/
def riemannMappingInversePoleQuotient (F : ℂ → ℂ) : ℂ → ℂ :=
  dslope (riemannMappingClosedInverse F) (F 0)

/-- The logarithmic pole removed from the actual Green function. -/
def riemannMappingGreenCorrection (F : ℂ → ℂ) (w : ℂ) : ℝ :=
  -Real.log ‖riemannMappingInversePoleQuotient F w‖

private theorem fderiv_neg_log_norm_holomorphic
      (hf : DifferentiableAt ℂ f z) (hne : f z ≠ 0) v :
    fderiv ℝ (fun w => -Real.log ‖f w‖) z v =
      -⟪f z, deriv f z * v⟫_ℝ / ‖f z‖ ^ 2 := by
  have ht := ((hf.restrictScalars ℝ).hasFDerivAt.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))).const_mul (-(1 / 2))
  rw [show (fun w => -(1 / 2) * Real.log (‖f w‖ ^ 2)) = (fun w => -Real.log ‖f w‖) by
    funext w
    rw [Real.log_pow]
    ring] at ht
  have hh := congrArg (fun A : ℂ →L[ℝ] ℝ => A v) ht.fderiv
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul, show fderiv ℝ f z v = deriv f z * v by
      rw [hf.fderiv_restrictScalars ℝ]
      exact fderiv_eq_deriv_mul] at hh
  calc
    _ = _ := by
      simpa only [two_smul, two_mul] using hh
    _ = _ := by rw [div_eq_mul_inv]; ring

private theorem norm_fderiv_neg_log_norm_holomorphic_le
      (hf : DifferentiableAt ℂ f z) (hne : f z ≠ 0) v :
    ‖fderiv ℝ (fun w => -Real.log ‖f w‖) z v‖ ≤
      ‖deriv f z‖ * ‖v‖ / ‖f z‖ := by
  rw [fderiv_neg_log_norm_holomorphic hf hne, norm_div, norm_neg,
    Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ _ :=
      div_le_div_of_nonneg_right (norm_inner_le_norm _ _) (sq_nonneg _)
    _ = _ := by rw [norm_mul]; field_simp [(norm_pos_iff.mpr hne).ne']

private theorem disk_mobius_norm_sq_difference (a b : ℂ) :
    ‖1 - star a * b‖ ^ 2 - ‖b - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
  simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

private theorem disk_mobius_denominator_and_norm  (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    1 - star a * b ≠ 0 ∧ ‖(b - a) / (1 - star a * b)‖ < 1 := by
  have hh := disk_mobius_norm_sq_difference a b
  have hprod := mul_pos (show 0 < 1 - ‖a‖ ^ 2 by nlinarith [norm_nonneg a]) (show 0 < 1 - ‖b‖ ^ 2 by nlinarith [norm_nonneg b])
  have hnorm :=
    (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (show ‖b - a‖ ^ 2 < ‖1 - star a * b‖ ^ 2 by linarith)
  have hd := (norm_nonneg _).trans_lt hnorm
  refine ⟨norm_ne_zero_iff.mp hd.ne', ?_⟩
  rw [norm_div]
  exact (div_lt_one hd).mpr hnorm

private theorem disk_mobius_norm_defect  
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hbound : ‖(b - a) / (1 - star a * b)‖ ≤ t) :
    (1 - ‖a‖) ^ 2 / 2 * (1 - t) ≤ 1 - ‖b‖ := by
  let d := ‖1 - star a * b‖
  have hdpos := norm_pos_iff.mpr (disk_mobius_denominator_and_norm ha hb).1
  have hn2 : ‖b - a‖ ^ 2 ≤ t ^ 2 * d ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht0 hdpos.le)).mpr (by
        rw [norm_div] at hbound
        exact (div_le_iff₀ hdpos).mp hbound)
  have ht2 : t ^ 2 ≤ t := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left ht1 ht0
  have hmul := mul_le_mul_of_nonneg_right ((sq_le_sq₀ (sub_nonneg.mpr ha.le) hdpos.le).mpr (by
    have ht := norm_sub_norm_le 1 (star a * b)
    rw [norm_one, norm_mul, norm_star] at ht
    have hp : ‖a‖ * ‖b‖ ≤ ‖a‖ := by
      simpa using mul_le_mul_of_nonneg_left hb.le (norm_nonneg a)
    dsimp [d]
    simp at ht ⊢
    linarith)) (sub_nonneg.mpr (ht2.trans ht1))
  have hid := disk_mobius_norm_sq_difference a b
  nlinarith only [(mul_le_mul_of_nonneg_left (sub_le_sub_left ht2 1) (sq_nonneg _)).trans ((show (1 - ‖a‖) ^ 2 * (1 - t ^ 2) ≤ 1 - ‖b‖ ^ 2 by
    have hmiddle : d ^ 2 * (1 - t ^ 2) ≤ (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
      dsimp [d] at hn2 ⊢
      simp at hn2 hid ⊢
      nlinarith only [hn2, hid]
    exact hmul.trans (hmiddle.trans (by
      simpa using mul_le_mul_of_nonneg_right
        (show 1 - ‖a‖ ^ 2 ≤ 1 by nlinarith [sq_nonneg ‖a‖]) (show 0 ≤ 1 - ‖b‖ ^ 2 by nlinarith [norm_nonneg b])))).trans (show 1 - ‖b‖ ^ 2 ≤ 2 * (1 - ‖b‖) by nlinarith [sq_nonneg (1 - ‖b‖)]))]

section ActualMap

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)

-- These physical hypotheses occur in proofs of the inverse and Green
-- identities even when they do not occur in the displayed conclusion.
include hb hS hsc hF hinj himage

local notation "G" => riemannMappingClosedExtension F
local notation "J" => riemannMappingClosedInverse F

omit hb hS hsc hF hinj in
theorem riemannMapping_pole_mem : F 0 ∈ Ω := by
  rw [← himage]
  exact mem_image_of_mem F (mem_ball_self zero_lt_one)

local notation "Φ11" => closure Ω

theorem riemannMappingClosedInverse_mem_right  (hw : w ∈ Φ11) :
    J w ∈ closedBall 0 1 ∧ G (J w) = w := by
  exact Function.invFunOn_pos (show w ∈ G '' closedBall 0 1 by
    rw [riemannMappingClosedExtension_closed_image hb hS.isLipschitzDomain hsc F hF hinj himage]
    exact hw)

theorem riemannMappingClosedInverse_left  (hz : z ∈ closedBall 0 1) :
    J (G z) = z := by
  have hx := Function.invFunOn_pos (show G z ∈ G '' closedBall 0 1 from ⟨z, hz, rfl⟩)
  exact riemannMappingClosedExtension_injOn hb hS.isLipschitzDomain hsc F hF hinj himage
    hx.1 hz hx.2

theorem riemannMappingClosedInverse_left_interior  (hz : z ∈ ball 0 1) :
    J (F z) = z := by
  rw [← riemannMappingClosedExtension_eqOn F hF hz]
  exact riemannMappingClosedInverse_left hb hS hsc F hF hinj himage (ball_subset_closedBall hz)

local notation "Φ9" => riemannMappingClosedInverse_left_interior hb hS hsc F hF hinj himage

theorem riemannMappingClosedInverse_zero : J (F 0) = 0 :=
  Φ9 (mem_ball_self zero_lt_one)

/-- The actual physical inverse is continuous on the whole physical
closure, derived from the genuine closed-disk homeomorphism. -/
theorem riemannMappingClosedInverse_continuousOn : ContinuousOn J (Φ11) := by
  obtain ⟨e, he⟩ := exists_riemannMapping_closedDisk_homeomorph
    hb hS.isLipschitzDomain hsc F hF hinj himage
  have hJe (w : Φ11) : J w = e.symm w := by
    calc
      _ = _ := congrArg J (show G (e.symm w) = (w : ℂ) by
        rw [← he (e.symm w), e.apply_symm_apply]).symm
      _ = _ :=
        riemannMappingClosedInverse_left hb hS hsc F hF hinj himage (e.symm w).property
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_subtype_val.comp e.symm.continuous).congr (fun w => (hJe w).symm)

local notation "Φ2" => riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage

theorem riemannMappingClosedInverse_injOn : InjOn J (Φ11) := by
  intro w hw v hv he
  exact (Φ2 hw).2.symm.trans
    ((congrArg G he).trans (Φ2 hv).2)

theorem riemannMappingClosedInverse_mem_disk  (hw : w ∈ Ω) :
    J w ∈ ball 0 1 := by
  have hj := Φ2 (subset_closure hw)
  apply (riemannMappingClosedExtension_mem_domain_iff
    hb hS.isLipschitzDomain hsc F hF hinj himage hj.1).mp
  exact hj.2.symm ▸ hw

/-- The continuous physical inverse retains the actual holomorphic
interior inverse. No boundary derivative is assumed. -/
theorem riemannMappingClosedInverse_differentiableOn : DifferentiableOn ℂ J Ω := by
  obtain ⟨K, hK, hKm, hKF, hFK⟩ := RiemannInterior.exists_holomorphic_inverse
    isOpen_ball (convex_ball 0 1).isPreconnected hF hinj
  rw [himage] at hK hKm hFK
  apply hK.congr
  intro w hw
  calc
    _ = _ := congrArg J (hFK w hw).symm
    _ = _ := Φ9 (hKm hw)

theorem riemannMappingClosedInverse_nonzero  (hw : w ∈ Φ11) (hne : w ≠ F 0) :
    J w ≠ 0 := by
  intro hj0
  have he := (Φ2 hw).2
  rw [hj0, riemannMappingClosedExtension_eqOn F hF (mem_ball_self zero_lt_one)] at he
  exact hne he.symm

theorem riemannMappingClosedInverse_norm_frontier  (hw : w ∈ frontier Ω) : ‖J w‖ = 1 := by
  have hj := Φ2 (frontier_subset_closure hw)
  apply le_antisymm (mem_closedBall_zero_iff.mp hj.1)
  apply le_of_not_gt
  intro hn
  rw [hS.1.1.frontier_eq] at hw
  exact hw.2 (by
    rw [← hj.2]
    exact (riemannMappingClosedExtension_mem_domain_iff
      hb hS.isLipschitzDomain hsc F hF hinj himage hj.1).mpr (mem_ball_zero_iff.mpr hn))

local notation "Φ0" => riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage

theorem riemannMappingClosedInverse_deriv_nonzero  (hw : w ∈ Ω) : deriv J w ≠ 0 :=
  RiemannInterior.deriv_ne_zero_of_injOn hS.1.1
    (Φ0)
    ((riemannMappingClosedInverse_injOn hb hS hsc F hF hinj himage).mono subset_closure) hw

/-- The genuine physical inverse has finite conformal energy, even
before any boundary derivative regularity has been proved. -/
local notation "Φ4" => riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage

theorem riemannMappingClosedInverse_deriv_sq_integrable :
    IntegrableOn (fun w => ‖deriv J w‖ ^ 2) Ω := by
  have hc : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (J '' Ω) := by
    have h_inl : J '' Ω = ball 0 1 := by
      apply Subset.antisymm
      · rintro z ⟨w, hw, rfl⟩
        exact Φ4 hw
      · intro z hz
        refine ⟨F z, ?_, Φ9 hz⟩
        rw [← himage]
        exact mem_image_of_mem F hz
    rw [h_inl]
    exact integrableOn_const unitDisk_bounded.measure_lt_top.ne
  simpa using localConformal_integrable_weight hS.1.1
    (Φ0)
    ((riemannMappingClosedInverse_injOn hb hS hsc F hF hinj himage).mono subset_closure) hc

/-- The actual Green function has zero boundary values. -/
theorem riemannMappingGreen_frontier  (hw : w ∈ frontier Ω) : riemannMappingGreen F w = 0 := by
  rw [riemannMappingGreen, riemannMappingClosedInverse_norm_frontier hb hS hsc F hF hinj himage hw,
    Real.log_one, neg_zero]

local notation "Φ1" => riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage

theorem riemannMappingGreen_continuousOn :
    ContinuousOn (riemannMappingGreen F) (Φ11 \ {F 0}) := by
  exact (((riemannMappingClosedInverse_continuousOn hb hS hsc F hF hinj himage).mono diff_subset).norm.log (fun _ hw => norm_ne_zero_iff.mpr
    (Φ1 hw.1 hw.2))).neg

/-- The genuine physical Green function is harmonic away from its
actual interior pole. This is local interior analyticity, and does not
claim smoothness up to the physical boundary. -/
theorem riemannMappingGreen_harmonicOnNhd :
    HarmonicOnNhd (riemannMappingGreen F) (Ω \ {F 0}) := by
  intro w hw
  have hh := (((Φ0).analyticOnNhd hS.1.1 w hw.1).harmonicAt_log_norm (Φ1 (subset_closure hw.1) hw.2)).const_smul (c := (-1))
  rw [show (-1 : ℝ) • (fun x => Real.log ‖J x‖) = riemannMappingGreen F by
    funext x
    simp [riemannMappingGreen]] at hh
  exact hh

/-- The actual physical Green derivative, derived by the real chain
rule. This identity is asserted only at actual interior points. -/
theorem riemannMappingGreen_fderiv {w : ℂ} (hw : w ∈ Ω) (hne : w ≠ F 0) v :
    fderiv ℝ (riemannMappingGreen F) w v = -⟪J w, deriv J w * v⟫_ℝ / ‖J w‖ ^ 2 := by
  exact fderiv_neg_log_norm_holomorphic ((Φ0).differentiableAt (hS.1.1.mem_nhds hw))
    (Φ1 (subset_closure hw) hne) v

/-- The actual inverse and the Schwarz lemma give a quantitative
Green lower barrier on every genuine interior ball. Boundary
differentiability and a PDE Hopf lemma are not inputs. -/
theorem exists_riemannMappingGreen_ball_lower_barrier {v : ℂ} 
    (hR : 0 < R) (hball : ball v R ⊆ Ω) :
    ∃ A : ℝ, 0 < A ∧ ∀ w ∈ ball v R, w ≠ F 0 →
      A * (R - ‖w - v‖) ≤ riemannMappingGreen F w := by
  let a := J v
  have ha := mem_ball_zero_iff.mp
    (Φ4 (hball (mem_ball_self hR)))
  let M : ℂ → ℂ := fun w => (J w - a) / (1 - star a * J w)
  have hJb :=
    (Φ0).mono hball
  have hM0 : M v = 0 := by dsimp [M, a]; rw [sub_self, zero_div]
  let A := (1 - ‖a‖) ^ 2 / (2 * R)
  refine ⟨A, div_pos (sq_pos_of_pos (sub_pos.mpr ha)) (by positivity), ?_⟩
  intro w hw hne
  have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball (by
    apply (hJb.sub_const a).div ((differentiableOn_const 1).sub ((differentiableOn_const (star a)).mul hJb))
    intro w hw
    exact (disk_mobius_denominator_and_norm ha (mem_ball_zero_iff.mp
      (Φ4 (hball hw)))).1) (show MapsTo M (ball v R) (closedBall (M v) 1) by
    rw [hM0]
    intro w hw
    exact mem_closedBall_zero_iff.mpr
      (disk_mobius_denominator_and_norm ha (mem_ball_zero_iff.mp
        (Φ4 (hball hw)))).2.le) hw
  rw [hM0, dist_zero_right, dist_eq_norm] at hschwarz
  have hdefect := disk_mobius_norm_defect ha (mem_ball_zero_iff.mp (Φ4 (hball hw))) (div_nonneg (norm_nonneg _) hR.le)
    ((div_lt_one hR).mpr (by simpa [dist_eq_norm] using hw)).le (by
      simpa [M, div_eq_mul_inv, mul_comm] using hschwarz)
  have hlog := Real.log_le_sub_one_of_pos (norm_pos_iff.mpr (Φ1 (subset_closure (hball hw)) hne))
  rw [show A * (R - ‖w - v‖) = (1 - ‖a‖) ^ 2 / 2 * (1 - ‖w - v‖ / R) by
    dsimp [A]
    field_simp [hR.ne'], riemannMappingGreen]
  exact hdefect.trans (by linarith)

/-- The actual quotient removes the inverse's simple zero at the pole
by the complex removable-singularity theorem. -/
local notation "Φ10" => riemannMapping_pole_mem F himage

theorem riemannMappingInversePoleQuotient_differentiableOn :
    DifferentiableOn ℂ (riemannMappingInversePoleQuotient F) Ω := by
  exact (Complex.differentiableOn_dslope
    (hS.1.1.mem_nhds (Φ10))).mpr
      (Φ0)

theorem riemannMappingInversePoleQuotient_continuousOn :
    ContinuousOn (riemannMappingInversePoleQuotient F) (Φ11) := by
  exact (continuousOn_dslope (mem_of_superset (hS.1.1.mem_nhds (Φ10)) subset_closure)).mpr
    ⟨riemannMappingClosedInverse_continuousOn hb hS hsc F hF hinj himage, (Φ0).differentiableAt (hS.1.1.mem_nhds (Φ10))⟩

local notation "Φ8" => riemannMappingClosedInverse_zero hb hS hsc F hF hinj himage

theorem riemannMappingInversePoleQuotient_nonzero  (hw : w ∈ Φ11) :
    riemannMappingInversePoleQuotient F w ≠ 0 := by
  by_cases he : w = F 0
  · subst w
    rw [riemannMappingInversePoleQuotient, dslope_same]
    exact riemannMappingClosedInverse_deriv_nonzero hb hS hsc F hF hinj himage
      (Φ10)
  · rw [riemannMappingInversePoleQuotient, dslope_of_ne _ he, slope,
      Φ8,
      vsub_eq_sub, sub_zero, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr he))
      (Φ1 hw he)

/-- The actual pole-subtracted harmonic function is continuous on the
whole physical closure, including at the pole. -/
local notation "Φ3" => riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage

local notation "Φ7" => riemannMappingGreenCorrection F

theorem riemannMappingGreenCorrection_continuousOn :
    ContinuousOn (Φ7) (Φ11) :=
  ((riemannMappingInversePoleQuotient_continuousOn hb hS hsc F hF hinj himage).norm.log
    (fun _ hw => norm_ne_zero_iff.mpr
      (Φ3 hw))).neg

/-- Removing the true logarithmic pole gives a genuine harmonic
function throughout the domain. No elliptic boundary theorem is used. -/
local notation "Φ5" => riemannMappingInversePoleQuotient_differentiableOn hb hS hsc F hF hinj himage

theorem riemannMappingGreenCorrection_harmonicOnNhd :
    HarmonicOnNhd (Φ7) Ω := by
  intro w hw
  have hh := (((Φ5).analyticOnNhd hS.1.1 w hw).harmonicAt_log_norm (Φ3 (subset_closure hw))).const_smul (c := (-1))
  rw [show (-1 : ℝ) • (fun x => Real.log ‖riemannMappingInversePoleQuotient F x‖) = Φ7 by
    funext x
    simp [riemannMappingGreenCorrection]] at hh
  exact hh

theorem riemannMappingGreenCorrection_contDiffOn :
    ContDiffOn ℝ ∞ (Φ7) Ω := by
  intro w hw
  have hne := Φ3
    (subset_closure hw)
  exact ((((((Φ5).analyticOnNhd hS.1.1 w hw).restrictScalars (𝕜 := ℝ)).contDiffAt).norm ℝ hne).log (norm_ne_zero_iff.mpr hne)).neg.contDiffWithinAt

/-- The actual divided-difference derivative away from the physical
pole. Its numerator and both powers of the physical distance are kept
explicit for the finite-energy estimate. -/
theorem exists_riemannMappingInversePoleQuotient_norm_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Φ11, c ≤ ‖riemannMappingInversePoleQuotient F w‖ :=
  hb.isCompact_closure.exists_forall_le'
    (riemannMappingInversePoleQuotient_continuousOn hb hS hsc F hF hinj himage).norm
    (fun _ hw => norm_pos_iff.mpr
      (Φ3 hw))

/-- Every genuine real coordinate derivative of the constructed
harmonic correction belongs to L². This is an energy conclusion, not
a boundary smoothness assumption. -/
local notation "Φ6" => riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage

private theorem riemannMappingGreenCorrection_complex_fderiv  (hw : w ∈ Ω) v :
    fderiv ℝ (fun z => (Φ7 z : ℂ)) w v =
      (fderiv ℝ (Φ7) w v : ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ Φ7) w v = _
  rw [fderiv_comp w Complex.ofRealCLM.differentiableAt (((Φ6).differentiableOn (by simp)).differentiableAt (hS.1.1.mem_nhds hw))]
  simp

private theorem riemannMappingGreenCorrection_complex_gradient_memLp i :
    MemLp (fun w => fderiv ℝ (fun z => (Φ7 z : ℂ)) w (coordDir i)) 2
      (volume.restrict Ω) := by
  have hs : ContDiffOn ℝ ∞ (fun z => (Φ7 z : ℂ)) Ω :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Φ6)
  have hc := (hs.continuousOn_fderiv_of_isOpen hS.1.1 (by simp)).clm_apply
    (show ContinuousOn (fun _ => coordDir i) Ω from continuousOn_const)
  have hm : MemLp (fun w => fderiv ℝ (Φ7) w (coordDir i)) 2 (volume.restrict Ω) := by
    obtain ⟨c, hc, hcn⟩ := exists_riemannMappingInversePoleQuotient_norm_lower_bound
      hb hS hsc F hF hinj himage
    have h_inl : MemLp (deriv (riemannMappingInversePoleQuotient F)) 2 (volume.restrict Ω) := by
      let Q := riemannMappingInversePoleQuotient F
      have hQc := ((Φ5).deriv hS.1.1).continuousOn
      obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
        (hS.1.1.mem_nhds (Φ10))
      obtain ⟨B, hBpos, hB⟩ := (((isCompact_closedBall (F 0) r).image_of_continuousOn (hQc.mono hball)).isBounded).subset_ball_lt 0 0
      have hlocal w (hw : w ∈ closedBall (F 0) r) : ‖deriv Q w‖ ≤ B := by
        have hh := hB (mem_image_of_mem (deriv Q) hw)
        exact (show ‖deriv Q w‖ < B by simpa using hh).le
      letI : IsFiniteMeasure (volume.restrict Ω) :=
        ⟨by simpa [Measure.restrict_apply_univ] using hb.measure_lt_top⟩
      have hmajor : MemLp (fun w => r⁻¹ * ‖deriv J w‖ + (B + r⁻¹ ^ 2)) 2
          (volume.restrict Ω) :=
        ((show MemLp (deriv J) 2 (volume.restrict Ω) by
          apply (memLp_two_iff_integrable_sq_norm
            ((((Φ0).deriv hS.1.1).continuousOn).aestronglyMeasurable hS.1.1.measurableSet)).mpr
          exact riemannMappingClosedInverse_deriv_sq_integrable hb hS hsc F hF hinj himage).norm.const_mul r⁻¹).add (memLp_const (B + r⁻¹ ^ 2))
      apply hmajor.mono' (hQc.aestronglyMeasurable hS.1.1.measurableSet)
      filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
      by_cases hwball : w ∈ closedBall (F 0) r
      · have hp : 0 ≤ r⁻¹ * ‖deriv J w‖ + r⁻¹ ^ 2 := by positivity
        exact (hlocal w hwball).trans (by linarith)
      · have hdist : r ≤ ‖w - F 0‖ := by
          have hh : r < dist w (F 0) := lt_of_not_ge hwball
          have hh' : r < ‖w - F 0‖ := by simpa [dist_eq_norm] using hh
          exact hh'.le
        have hdpos := hr.trans_le hdist
        have hJn := mem_closedBall_zero_iff.mp
          (Φ2 (subset_closure hw)).1
        have hstep : ‖deriv Q w‖ ≤ ‖deriv J w‖ / r + 1 / r ^ 2 := by
          have h_inl : deriv (riemannMappingInversePoleQuotient F) w = (deriv J w * (w - F 0) - J w) / (w - F 0) ^ 2 := by
            rw [(show riemannMappingInversePoleQuotient F =ᶠ[𝓝 w] (fun z => J z / (z - F 0)) by
              filter_upwards [eventually_ne_nhds (sub_ne_zero.mp (norm_ne_zero_iff.mp hdpos.ne'))] with z hz
              rw [riemannMappingInversePoleQuotient, dslope_of_ne _ hz, slope,
                Φ8,
                vsub_eq_sub, sub_zero, smul_eq_mul]
              simp [div_eq_mul_inv, mul_comm]).deriv_eq]
            have h := ((((Φ0).differentiableAt (hS.1.1.mem_nhds hw)).hasDerivAt).div ((hasDerivAt_id w).sub_const (F 0)) (sub_ne_zero.mpr (sub_ne_zero.mp (norm_ne_zero_iff.mp hdpos.ne')))).deriv
            simp at h
            exact h
          rw [h_inl,
            norm_div, norm_pow]
          calc
            _ ≤ _ :=
              div_le_div_of_nonneg_right (norm_sub_le _ _) (sq_nonneg _)
            _ = _ := by
              rw [norm_mul]
              field_simp [hdpos.ne']
            _ ≤ _ := add_le_add
              (div_le_div_of_nonneg_left (norm_nonneg _) hr hdist)
              ((div_le_div_of_nonneg_right hJn (sq_nonneg _)).trans
                (div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hr)
                  ((sq_le_sq₀ hr.le hdpos.le).mpr hdist)))
        have heq : ‖deriv J w‖ / r + 1 / r ^ 2 = r⁻¹ * ‖deriv J w‖ + r⁻¹ ^ 2 := by
          rw [div_eq_mul_inv, one_div, inv_pow]
          ring
        exact hstep.trans (by rw [heq]; linarith)
    apply (h_inl.norm.const_mul c⁻¹).mono' ((((Φ6).continuousOn_fderiv_of_isOpen hS.1.1 (by simp)).clm_apply continuousOn_const).aestronglyMeasurable hS.1.1.measurableSet)
    filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
    calc
      _ ≤ _ :=
        norm_fderiv_neg_log_norm_holomorphic_le ((Φ5).differentiableAt (hS.1.1.mem_nhds hw)) (Φ3 (subset_closure hw)) _
      _ ≤ ‖deriv (riemannMappingInversePoleQuotient F) w‖ / c := by
        rw [norm_coordDir, mul_one]
        exact div_le_div_of_nonneg_left (norm_nonneg _) hc (hcn w (subset_closure hw))
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  apply hm.congr_norm (hc.aestronglyMeasurable hS.1.1.measurableSet)
  filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
  rw [riemannMappingGreenCorrection_complex_fderiv hb hS hsc F hF hinj himage hw]
  simp

/-- The pole-subtracted physical Green function is an actual weak
H¹ vector, represented by its constructed harmonic solution and its
true real derivatives. No boundary elliptic regularity is an input. -/
theorem exists_riemannMappingGreenCorrectionH1 :
    ∃ u : NeumannH1 Ω,
      (h1Value Ω u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
        (fun w => (Φ7 w : ℂ)) ∧
      ∀ i : Fin 2, (h1Gradient Ω i u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
        (fun w => (fderiv ℝ (Φ7) w (coordDir i) : ℂ)) := by
  have hu : MemLp (fun w => (Φ7 w : ℂ)) 2 (volume.restrict Ω) := by
    have h_inl : MemLp (Φ7) 2 (volume.restrict Ω) := by
      letI : IsFiniteMeasure (volume.restrict Ω) :=
        ⟨by simpa [Measure.restrict_apply_univ] using hb.measure_lt_top⟩
      have hcont := riemannMappingGreenCorrection_continuousOn hb hS hsc F hF hinj himage
      obtain ⟨B, _, hB⟩ := ((hb.isCompact_closure.image_of_continuousOn hcont).isBounded).subset_ball_lt 0 0
      apply MemLp.of_bound ((hcont.mono subset_closure).aestronglyMeasurable hS.1.1.measurableSet) B
      filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
      exact (show ‖Φ7 w‖ < B by
        simpa using hB
          (mem_image_of_mem (Φ7) (subset_closure hw))).le
    apply h_inl.congr_norm ((Complex.ofRealCLM.continuous.comp_continuousOn ((riemannMappingGreenCorrection_continuousOn hb hS hsc F hF hinj himage).mono subset_closure)).aestronglyMeasurable hS.1.1.measurableSet)
    exact Eventually.of_forall (fun w => by simp)
  have hg := riemannMappingGreenCorrection_complex_gradient_memLp hb hS hsc F hF hinj himage
  have hs : ContDiffOn ℝ ∞ (fun z => (Φ7 z : ℂ)) Ω :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Φ6)
  have hweak := isWeakGradient_of_contDiffOn hS.1.1 hs hu hg
  refine ⟨h1Vector hweak, ?_, ?_⟩
  · rw [h1Value_h1Vector]
    exact hu.coeFn_toLp
  · intro i
    rw [h1Gradient_h1Vector]
    filter_upwards [(hg i).coeFn_toLp, ae_restrict_mem hS.1.1.measurableSet] with w hw hwΩ
    rw [hw, riemannMappingGreenCorrection_complex_fderiv hb hS hsc F hF hinj himage hwΩ]

/-- The physical correction is exactly the Green function plus the
fundamental logarithmic singularity away from the actual pole. -/
theorem riemannMappingGreenCorrection_eq  (hw : w ∈ Φ11) (hne : w ≠ F 0) :
    Φ7 w = riemannMappingGreen F w + Real.log ‖w - F 0‖ := by
  rw [riemannMappingGreenCorrection, riemannMappingInversePoleQuotient,
    dslope_of_ne _ hne, slope, Φ8,
    vsub_eq_sub, sub_zero, smul_eq_mul, norm_mul, norm_inv, Real.log_mul (inv_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))) (norm_ne_zero_iff.mpr (Φ1 hw hne)), Real.log_inv,
    riemannMappingGreen]
  ring

/-- The actual Dirichlet boundary data of the pole-subtracted harmonic
function are the smooth physical function `log ‖w - F 0‖`. -/
theorem riemannMappingGreenCorrection_frontier  (hw : w ∈ frontier Ω) :
    Φ7 w = Real.log ‖w - F 0‖ := by
  rw [riemannMappingGreenCorrection_eq hb hS hsc F hF hinj himage
    (frontier_subset_closure hw) (by
      intro he
      rw [he, hS.1.1.frontier_eq] at hw
      exact hw.2 (Φ10)),
    riemannMappingGreen_frontier hb hS hsc F hF hinj himage hw, zero_add]

omit hb hS hsc hF hinj himage in
/-- The actual physical Dirichlet data are smooth on an open
neighborhood of the entire frontier, because the pole is interior. -/
theorem riemannMappingGreenBoundaryData_contDiffOn :
    ContDiffOn ℝ ∞ (fun w => Real.log ‖w - F 0‖) {F 0}ᶜ := by
  intro w hw
  have hne := sub_ne_zero.mpr hw
  exact (((contDiffAt_id.sub contDiffAt_const).norm ℝ hne).log
    (norm_ne_zero_iff.mpr hne)).contDiffWithinAt

/-- A genuine globally smooth, compactly supported physical test
function has exactly the pole-subtracted Green function's boundary
data. The cutoff extends already smooth logarithmic data near the
frontier, not the unknown Riemann-map boundary jets. -/
theorem exists_riemannMappingGreenCorrection_smooth_boundary_data :
    ∃ b : smoothTraceTests, ∀ w ∈ frontier Ω,
      Φ7 w = (b w).re := by
  have hs : ContDiffOn ℝ ∞ (fun w => (Real.log ‖w - F 0‖ : ℂ)) {F 0}ᶜ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (riemannMappingGreenBoundaryData_contDiffOn F)
  obtain ⟨b, hbtest, hbe⟩ := exists_smooth_compact_extension (hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure) isOpen_compl_singleton (by
    intro w hw he
    rw [he, hS.1.1.frontier_eq] at hw
    exact hw.2 (Φ10)) hs
  refine ⟨⟨b, hbtest⟩, ?_⟩
  intro w hw
  change Φ7 w = (b w).re
  rw [(hbe w hw).self_of_nhds, Complex.ofReal_re]
  exact riemannMappingGreenCorrection_frontier hb hS hsc F hF hinj himage hw

end ActualMap

/-- A genuine unit inward ray has a strictly positive Green slope
lower bound at every physical frontier point. The whole short ray
avoids the actual Green pole. This is a proved boundary estimate,
without any assumed existence of boundary derivatives. -/
theorem exists_riemannMappingGreen_inward_ray_lower 
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    F (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (himage : F '' ball 0 1 = Ω)
     (hp : p ∈ frontier Ω) :
    ∃ b : ℂ, ∃ δ A : ℝ, ‖b‖ = 1 ∧ 0 < δ ∧ 0 < A ∧
      ∀ t : ℝ, 0 < t → t < δ → p + (t : ℂ) * b ∈ Ω ∧
        p + (t : ℂ) * b ≠ F 0 ∧ A * t ≤ riemannMappingGreen F (p + (t : ℂ) * b) := by
  obtain ⟨v, R, hR, hball, hpR⟩ : ∃ v : ℂ, ∃ R : ℝ, 0 < R ∧ ball v R ⊆ Ω ∧ p ∈ sphere v R := by
    obtain ⟨c, r, h, K, f, hc, hr, hh, hf, _, hf0, _, hgraph⟩ := hS.2 p hp
    obtain ⟨M, hM, hquad⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |x| ≤ 1 → |f x - f 0 - deriv f 0 * x| ≤ M * x ^ 2 := by
      obtain ⟨K, hK⟩ := ((hf.of_le (WithTop.coe_le_coe.mpr le_top)).deriv').contDiffOn.exists_lipschitzOnWith one_ne_zero
        (convex_Icc (-1 : ℝ) 1) (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))
      refine ⟨K, K.coe_nonneg, ?_⟩
      intro x hx
      have h0I : 0 ∈ Icc (-1 : ℝ) 1 := by norm_num
      have hsmall y (hy : y ∈ uIcc 0 x) : |y| ≤ |x| := by
        apply abs_le.mpr
        have hxlo := neg_abs_le x
        have hxhi := le_abs_self x
        rcases mem_uIcc.mp hy with hy | hy <;> constructor <;> linarith [abs_nonneg x]
      let g : ℝ → ℝ := fun y => f y - f 0 - deriv f 0 * y
      have hg y : HasDerivAt g (deriv f y - deriv f 0) y := by
        have h := ((hf.differentiable (by simp) y).hasDerivAt.sub_const (f 0)).sub
            ((hasDerivAt_id y).const_mul (deriv f 0))
        simp at h
        exact h
      have hb y (hy : y ∈ uIcc 0 x) :
          ‖deriv g y‖ ≤ K * |x| := by
        rw [(hg y).deriv]
        exact (show ‖deriv f y - deriv f 0‖ ≤ K * |y| by
          simpa [dist_eq_norm] using (hK.dist_le_mul y ((uIcc_subset_Icc h0I (abs_le.mp hx)) hy) 0 h0I)).trans (mul_le_mul_of_nonneg_left (hsmall y hy) K.coe_nonneg)
      simpa [g, mul_assoc, ← pow_two] using Convex.norm_image_sub_le_of_norm_deriv_le (fun y (_ : y ∈ uIcc 0 x) => (hg y).differentiableAt) hb (convex_uIcc 0 x) left_mem_uIcc right_mem_uIcc
    let a := deriv f 0
    let n := -a + Complex.I
    let C := ‖n‖
    have hC : 0 < C := by
      apply norm_pos_iff.mpr
      intro he
      have him := congrArg Complex.im he
      norm_num [n] at him
    have hCsq : C ^ 2 = a ^ 2 + 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [n, Complex.normSq_apply]
      ring
    let e := min (min (r / (2 * C)) (h / (2 * C)))
      (min (1 / (2 * C)) (1 / (2 * (M + 1))))
    have he : 0 < e := by dsimp [e]; positivity
    obtain ⟨ρ, hρ, hρe⟩ := exists_between he
    have hρM : 2 * ρ * M ≤ 1 := by
      have ht := (lt_div_iff₀ (by positivity)).mp
        (lt_of_lt_of_le hρe ((min_le_right _ _).trans (min_le_right _ _)))
      nlinarith
    let v : ℂ := p + ρ * n / c
    let R := ρ * C
    have hR := mul_pos hρ hC
    have hvc : ‖v - p‖ = R := by
      simp only [v, add_sub_cancel_left, norm_div, norm_mul, hc, div_one,
        Complex.norm_real, Real.norm_of_nonneg hρ.le, R, C]
    refine ⟨v, R, hR, ?_, ?_⟩
    · intro w hw
      have hwR : ‖w - v‖ < R := by simpa [dist_eq_norm] using hw
      have hwp : ‖w - p‖ < 2 * ρ * C := by
        calc
          _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub w v p
          _ < R + R := by rw [hvc]; linarith only [hwR]
          _ = _ := by dsimp [R]; ring
      let z := c * (w - p)
      have hz : ‖z‖ = ‖w - p‖ := by dsimp [z]; rw [norm_mul, hc, one_mul]
      apply (hgraph w ((Complex.abs_re_le_norm z).trans_lt (by rw [hz]; exact hwp.trans (by
        have ht := (lt_div_iff₀ (by positivity)).mp
          (lt_of_lt_of_le hρe ((min_le_left _ _).trans (min_le_left _ _)))
        nlinarith))) ((Complex.abs_im_le_norm z).trans_lt (by rw [hz]; exact hwp.trans (by
        have ht := (lt_div_iff₀ (by positivity)).mp
          (lt_of_lt_of_le hρe ((min_le_left _ _).trans (min_le_right _ _)))
        nlinarith)))).mpr
      have hfx : f z.re ≤ a * z.re + M * z.re ^ 2 := by
        have ht := (abs_le.mp (hquad z.re (((Complex.abs_re_le_norm z).trans_lt (by rw [hz]; exact hwp.trans (by
          have ht := (lt_div_iff₀ (by positivity)).mp
            (lt_of_lt_of_le hρe ((min_le_right _ _).trans (min_le_left _ _)))
          nlinarith))).le))).2
        rw [hf0] at ht
        dsimp [a]
        linarith
      have hball : ‖z - ρ * n‖ < R := by
        rw [show z - ρ * n = c * (w - v) by
          dsimp [z, v]
          field_simp [norm_ne_zero_iff.mp (by rw [hc]; norm_num)]; ring, norm_mul, hc, one_mul]
        exact hwR
      have hs : (z.re + ρ * a) ^ 2 + (z.im - ρ) ^ 2 < ρ ^ 2 * (a ^ 2 + 1) := by
        have ht := (sq_lt_sq₀ (norm_nonneg _) hR.le).mpr hball
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at ht
        rw [show (z - ρ * n).re = z.re + ρ * a by simp [n], show (z - ρ * n).im = z.im - ρ by simp [n]] at ht
        have hRsq : R ^ 2 = ρ ^ 2 * (a ^ 2 + 1) := by dsimp [R]; rw [mul_pow, hCsq]
        rw [hRsq] at ht
        nlinarith
      exact hfx.trans_lt (by
        by_contra hn
        nlinarith [sq_nonneg z.im])
    · simpa [dist_eq_norm, norm_sub_rev] using hvc
  obtain ⟨A, hA, hbarrier⟩ := exists_riemannMappingGreen_ball_lower_barrier
    hb hS hsc F hF hinj himage hR hball
  have hvp : ‖v - p‖ = R := by simpa [dist_eq_norm, norm_sub_rev] using hpR
  let b := (R : ℂ)⁻¹ * (v - p)
  have hb1 : ‖b‖ = 1 := by
    dsimp [b]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le, hvp,
      inv_mul_cancel₀ hR.ne']
  refine ⟨b, min R (‖p - F 0‖ / 2), A, hb1, (lt_min hR (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (by
    intro he
    rw [he, hS.1.1.frontier_eq] at hp
    exact hp.2 (riemannMapping_pole_mem F himage)))) (by norm_num))), hA, ?_⟩
  intro t ht htδ
  have htP := lt_of_lt_of_le htδ (min_le_right _ _)
  have htd := (div_lt_one hR).mpr (lt_of_lt_of_le htδ (min_le_left _ _))
  have hdist : ‖p + t * b - v‖ = R - t := by
    have he : p + t * b - v = (t / R - 1 : ℝ) * (v - p) := by
      dsimp [b]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hR.ne']; ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr htd.le), hvp]
    field_simp [hR.ne']; ring
  have hwball : p + t * b ∈ ball v R := by
    rw [mem_ball, dist_eq_norm, hdist]
    linarith
  have hwne : p + t * b ≠ F 0 := by
    have hn : ‖p + t * b - p‖ = t := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, hb1, mul_one]
    intro he
    rw [he, norm_sub_rev] at hn
    nlinarith
  refine ⟨hball hwball, hwne, ?_⟩
  have hh := hbarrier _ hwball hwne
  rw [hdist] at hh
  simpa using hh

end PolyaNeumann

end
