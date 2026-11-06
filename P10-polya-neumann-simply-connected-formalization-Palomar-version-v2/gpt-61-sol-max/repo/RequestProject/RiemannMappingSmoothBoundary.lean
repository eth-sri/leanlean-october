module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

/-- The actual inverse of the closed-disk extension on its physical
compact image. Its values outside that image are immaterial. -/
def riemannMappingClosedInverse F  :=
  Function.invFunOn (riemannMappingClosedExtension F) closedUnitDisk

/-- The Green function with pole at the actual interior point `F 0`.
The total-function value at the pole is immaterial. -/
def riemannMappingGreen F w  :=
  -Real.log ‖riemannMappingClosedInverse F w‖

/-- The actual analytic divided difference of the inverse at the pole;
its value at the pole is the genuine inverse derivative. -/
def riemannMappingInversePoleQuotient F  :=
  dslope (riemannMappingClosedInverse F) (F 0)

/-- The logarithmic pole removed from the actual Green function. -/
def riemannMappingGreenCorrection F w  :=
  -Real.log ‖riemannMappingInversePoleQuotient F w‖

section
variable {f : PlaneMap} {z } (hf : DifferentiableAt ℂ f z) (hne : f z ≠ 0) (v : ℂ)
include f z hf hne v

private theorem fderiv_neg_log_norm_holomorphic :
    fderiv ℝ (fun w => -Real.log ‖f w‖) z v =
      -⟪f z, deriv f z * v⟫_ℝ / ‖f z‖ ^ 2 := by
  have hr  := hf.restrictScalars ℝ
  have hn  := pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  have ht := (hr.hasFDerivAt.norm_sq.log hn).const_mul (-(1 / 2))
  have heq : (fun w => -(1 / 2 : ℝ) * Real.log (‖f w‖ ^ 2)) =
      (fun w => -Real.log ‖f w‖) := by
    funext w
    rw [Real.log_pow]
    ring
  rw [heq] at ht
  have hh := congrArg (fun A : ℂ →L[ℝ] ℝ => A v) ht.fderiv
  have hfv : fderiv ℝ f z v = deriv f z * v := by
    rw [hf.fderiv_restrictScalars ℝ]
    change fderiv ℂ f z v = _
    exact fderiv_eq_deriv_mul
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul, hfv] at hh
  calc
    _ = -(1 / 2) * ((‖f z‖ ^ 2)⁻¹ * (2 * ⟪f z, deriv f z * v⟫_ℝ)) := by
      simpa only [two_smul, two_mul] using hh
    _ = _ := by ring

private theorem norm_fderiv_neg_log_norm_holomorphic_le :
    ‖fderiv ℝ (fun w => -Real.log ‖f w‖) z v‖ ≤
      ‖deriv f z‖ * ‖v‖ / ‖f z‖ := by
  have hn  := norm_pos_iff.mpr hne
  rw [fderiv_neg_log_norm_holomorphic hf hne, norm_div, norm_neg,
    Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (‖f z‖ * ‖deriv f z * v‖) / ‖f z‖ ^ 2 :=
      div_le_div_of_nonneg_right (norm_inner_le_norm _ _) (sq_nonneg _)
    _ = _ := by rw [norm_mul]; field_simp

end


private theorem disk_mobius_norm_sq_difference (a b : ℂ) :
    ‖1 - star a * b‖ ^ 2 - ‖b - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
  simp  [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

private theorem disk_mobius_denominator_and_norm {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    1 - star a * b ≠ 0 ∧ ‖(b - a) / (1 - star a * b)‖ < 1 := by
  have ha2 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hb2 : 0 < 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  have hh := disk_mobius_norm_sq_difference a b
  have hprod := mul_pos ha2 hb2
  have hsq : ‖b - a‖ ^ 2 < ‖1 - star a * b‖ ^ 2 := by linarith
  have hnorm  :=
    (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hd  := (norm_nonneg _).trans_lt hnorm
  refine ⟨norm_ne_zero_iff.mp hd.ne', ?_⟩
  rw [norm_div]
  exact (div_lt_one hd).mpr hnorm

private theorem disk_mobius_norm_defect {a b : ℂ} 
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hbound : ‖(b - a) / (1 - star a * b)‖ ≤ t) :
    (1 - ‖a‖) ^ 2 / 2 * (1 - t) ≤ 1 - ‖b‖ := by
  let d  := ‖1 - star a * b‖
  have hdpos  := norm_pos_iff.mpr (disk_mobius_denominator_and_norm ha hb).1
  have hnle : ‖b - a‖ ≤ t * d := by
    rw [norm_div] at hbound
    exact (div_le_iff₀ hdpos).mp hbound
  have hn2 : ‖b - a‖ ^ 2 ≤ t ^ 2 * d ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht0 hdpos.le)).mpr hnle
  have hlow : 1 - ‖a‖ ≤ d := by
    have ht := norm_sub_norm_le 1 (star a * b)
    rw [norm_one, norm_mul, norm_star] at ht
    have hp : ‖a‖ * ‖b‖ ≤ ‖a‖ := by
      bound
    linarith
  have ht2 : t ^ 2 ≤ t := by
    nlinarith
  have ht2one  := ht2.trans ht1
  have hsq  :=
    (sq_le_sq₀ (sub_nonneg.mpr ha.le) hdpos.le).mpr hlow
  have hmul := mul_le_mul_of_nonneg_right hsq (sub_nonneg.mpr ht2one)
  have hid := disk_mobius_norm_sq_difference a b
  have hb2 : 0 ≤ 1 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  have hup : (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) ≤ 1 - ‖b‖ ^ 2 := by
    simp_all
  have hlast : (1 - ‖a‖) ^ 2 * (1 - t) ≤ (1 - ‖a‖) ^ 2 * (1 - t ^ 2) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left ht2 1) (sq_nonneg _)
  have hfirst : (1 - ‖a‖) ^ 2 * (1 - t ^ 2) ≤ 1 - ‖b‖ ^ 2 := by
    linarith
  have htwo : 1 - ‖b‖ ^ 2 ≤ 2 * (1 - ‖b‖) := by nlinarith [sq_nonneg (1 - ‖b‖)]
  linarith

section ActualMap

variable {Ω } (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F )
    (hF : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk) (himage : F '' unitDisk = Ω)

-- These physical hypotheses occur in proofs of the inverse and Green
-- identities even when they do not occur in the displayed conclusion.
include hb hS hsc hF hinj himage

local notation "G" => riemannMappingClosedExtension F
local notation "J" => riemannMappingClosedInverse F

omit hb hS hsc hF hinj in
theorem riemannMapping_pole_mem : F 0 ∈ Ω := by
  aesop

theorem riemannMappingClosedInverse_mem_right  (hw : w ∈ closure Ω) :
    J w ∈ closedUnitDisk ∧ G (J w) = w := by
  have hwim : w ∈ G '' closedUnitDisk := by
    rw [riemannMappingClosedExtension_closed_image hb hS.isLipschitzDomain hsc F hF hinj himage]
    exact hw
  exact Function.invFunOn_pos hwim

theorem riemannMappingClosedInverse_left  (hz : z ∈ closedUnitDisk) :
    J (G z) = z := (have hx := Function.invFunOn_pos (Exists.intro z ⟨hz, rfl⟩);
  riemannMappingClosedExtension_injOn hb (IsSmoothDomain.isLipschitzDomain hS) hsc F hF hinj himage hx.left hz hx.right)

theorem riemannMappingClosedInverse_left_interior  (hz : z ∈ unitDisk) :
    J (F z) = z := by
  rw [← riemannMappingClosedExtension_eqOn F hF hz]
  exact riemannMappingClosedInverse_left hb hS hsc F hF hinj himage (ball_subset_closedBall hz)

theorem riemannMappingClosedInverse_zero : J (F 0) = 0 :=
  riemannMappingClosedInverse_left_interior hb hS hsc F hF hinj himage (mem_ball_self zero_lt_one)

/-- The actual physical inverse is continuous on the whole physical
closure, derived from the genuine closed-disk homeomorphism. -/
theorem riemannMappingClosedInverse_continuousOn : ContinuousOn J (closure Ω) := by
  obtain ⟨e, he⟩ := exists_riemannMapping_closedDisk_homeomorph
    hb hS.isLipschitzDomain hsc F hF hinj himage
  have hJe (w : closure Ω) : J w = (e.symm w : ℂ) := by
    have hG : G (e.symm w) = (w : ℂ) := by
      rw [← he (e.symm w), e.apply_symm_apply]
    grind only [riemannMappingClosedInverse_left]
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_subtype_val.comp e.symm.continuous).congr (fun w => (hJe w).symm)

theorem riemannMappingClosedInverse_injOn : InjOn J (closure Ω) := by
  intro w hw v hv he
  grind only [riemannMappingClosedInverse_mem_right]

section
variable {w } (hw : w ∈ Ω)

include w hw in
theorem riemannMappingClosedInverse_mem_disk :
    J w ∈ unitDisk := by
  have hj := riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage (subset_closure hw)
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
  grind [riemannMappingClosedInverse_left_interior, PolyaNeumann.riemannMappingClosedInverse]

theorem riemannMappingClosedInverse_image : J '' Ω = unitDisk := by
  grind [riemannMappingClosedInverse_mem_disk, riemannMappingClosedInverse_left_interior, PolyaNeumann.riemannMappingClosedInverse]

theorem riemannMappingClosedInverse_nonzero  (hw : w ∈ closure Ω) (hne : w ≠ F 0) :
    J w ≠ 0 := by
  intro hj0
  have he := (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage hw).2
  rw [hj0, riemannMappingClosedExtension_eqOn F hF (mem_ball_self zero_lt_one)] at he
  exact hne he.symm

theorem riemannMappingClosedInverse_norm_frontier  (hw : w ∈ frontier Ω) : ‖J w‖ = 1 := by
  have hj := riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage (frontier_subset_closure hw)
  apply le_antisymm (mem_closedBall_zero_iff.mp hj.1)
  apply le_of_not_gt
  intro hn
  have hwΩ : w ∈ Ω := by
    rw [← hj.2]
    exact (riemannMappingClosedExtension_mem_domain_iff
      hb hS.isLipschitzDomain hsc F hF hinj himage hj.1).mpr (mem_ball_zero_iff.mpr hn)
  rw [hS.1.1.frontier_eq] at hw
  exact hw.2 hwΩ

include w hw in
theorem riemannMappingClosedInverse_deriv_nonzero : deriv J w ≠ 0 :=
  RiemannInterior.deriv_ne_zero_of_injOn hS.1.1
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage)
    ((riemannMappingClosedInverse_injOn hb hS hsc F hF hinj himage).mono subset_closure) hw

/-- The genuine physical inverse has finite conformal energy, even
before any boundary derivative regularity has been proved. -/
theorem riemannMappingClosedInverse_deriv_sq_integrable :
    IntegrableOn (fun w => ‖deriv J w‖ ^ 2) Ω := by
  have hc : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (J '' Ω) := by
    simp_all [riemannMappingClosedInverse_image]
  simpa   using localConformal_integrable_weight hS.1.1
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage)
    ((riemannMappingClosedInverse_injOn hb hS hsc F hF hinj himage).mono subset_closure) hc

/-- The actual Green function has zero boundary values. -/
theorem riemannMappingGreen_frontier  (hw : w ∈ frontier Ω) : riemannMappingGreen F w = 0 := by
  rw [riemannMappingGreen, riemannMappingClosedInverse_norm_frontier hb hS hsc F hF hinj himage hw,
    Real.log_one, neg_zero]

theorem riemannMappingGreen_continuousOn :
    ContinuousOn (riemannMappingGreen F) (closure Ω \ {F 0}) := (ContinuousOn.neg (ContinuousOn.log (ContinuousOn.norm (ContinuousOn.mono (riemannMappingClosedInverse_continuousOn hb hS hsc F hF hinj himage) diff_subset)) fun x hw => norm_ne_zero_iff.mpr (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage hw.left hw.right)))

/-- The genuine physical Green function is harmonic away from its
actual interior pole. This is local interior analyticity, and does not
claim smoothness up to the physical boundary. -/
theorem riemannMappingGreen_harmonicOnNhd :
    HarmonicOnNhd (riemannMappingGreen F) (Ω \ {F 0}) := by
  intro w hw
  have hj  :=
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).analyticOnNhd
      hS.1.1 w hw.1
  have ha := hj.harmonicAt_log_norm
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage (subset_closure hw.1) hw.2)
  have he : (-1 : ℝ) • (fun x : ℂ => Real.log ‖J x‖) = riemannMappingGreen F := by
    ext <;> simp_all [riemannMappingGreen]
  have hh := ha.const_smul (c := (-1))
  rw [he] at hh
  exact hh

include w hw in
/-- The actual physical Green derivative, derived by the real chain
rule. This identity is asserted only at actual interior points. -/
theorem riemannMappingGreen_fderiv (hne : w ≠ F 0) v :
    fderiv ℝ (riemannMappingGreen F) w v = -⟪J w, deriv J w * v⟫_ℝ / ‖J w‖ ^ 2 := (fderiv_neg_log_norm_holomorphic (DifferentiableOn.differentiableAt (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage) (IsOpen.mem_nhds hS.left.left hw)) (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage (subset_closure hw) hne) v)

/-- The actual inverse and the Schwarz lemma give a quantitative
Green lower barrier on every genuine interior ball. Boundary
differentiability and a PDE Hopf lemma are not inputs. -/
theorem exists_riemannMappingGreen_ball_lower_barrier  
    (hR : 0 < R) (hball : ball v R ⊆ Ω) :
    ∃ A : ℝ, 0 < A ∧ ∀ w ∈ ball v R, w ≠ F 0 →
      A * (R - ‖w - v‖) ≤ riemannMappingGreen F w := by
  let a  := J v
  have hv  := hball (mem_ball_self hR)
  have ha  := mem_ball_zero_iff.mp
    (riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage hv)
  let M  := fun w => (J w - a) / (1 - star a * J w)
  have hJb  :=
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).mono hball
  have hM : DifferentiableOn ℂ M (ball v R) := by
    have hconst : DifferentiableOn ℂ (fun _ : ℂ => (1 : ℂ)) (ball v R) :=
      differentiableOn_const 1
    have haconst : DifferentiableOn ℂ (fun _ : ℂ => star a) (ball v R) :=
      differentiableOn_const (star a)
    apply (hJb.sub_const a).div (hconst.sub (haconst.mul hJb))
    intro w hw
    exact (disk_mobius_denominator_and_norm ha (mem_ball_zero_iff.mp
      (riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage (hball hw)))).1
  have hM0 : M v = 0 := by dsimp [M, a]; rw [sub_self, zero_div]
  have hmaps : MapsTo M (ball v R) (closedBall (M v) 1) := by
    rw [hM0]
    intro w hw
    exact mem_closedBall_zero_iff.mpr
      (disk_mobius_denominator_and_norm ha (mem_ball_zero_iff.mp
        (riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage (hball hw)))).2.le
  let A  := (1 - ‖a‖) ^ 2 / (2 * R)
  have hA : 0 < A := div_pos (sq_pos_of_pos (sub_pos.mpr ha)) (by positivity)
  refine ⟨A, hA, ?_⟩
  intro w hw hne
  have hn  := mem_ball_zero_iff.mp
    (riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage (hball hw))
  have hd : ‖w - v‖ < R := by simpa only [mem_ball, dist_eq_norm] using hw
  have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball hM hmaps hw
  rw [hM0, dist_zero_right, dist_eq_norm] at hschwarz
  have hbound : ‖(J w - a) / (1 - star a * J w)‖ ≤ ‖w - v‖ / R := by
    grind
  have hdefect := disk_mobius_norm_defect ha hn (div_nonneg (norm_nonneg _) hR.le)
    ((div_lt_one hR).mpr hd).le hbound
  have hJe  := norm_pos_iff.mpr
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage (subset_closure (hball hw)) hne)
  have hlog := Real.log_le_sub_one_of_pos hJe
  have halg : A * (R - ‖w - v‖) = (1 - ‖a‖) ^ 2 / 2 * (1 - ‖w - v‖ / R) := by
    dsimp [A]
    field_simp [hR.ne']
  grind only [riemannMappingGreen]

/-- The actual quotient removes the inverse's simple zero at the pole
by the complex removable-singularity theorem. -/
theorem riemannMappingInversePoleQuotient_differentiableOn :
    DifferentiableOn ℂ (riemannMappingInversePoleQuotient F) Ω := (id ((differentiableOn_dslope (IsOpen.mem_nhds hS.left.left (riemannMapping_pole_mem F himage))).mpr (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage)))

theorem riemannMappingInversePoleQuotient_continuousOn :
    ContinuousOn (riemannMappingInversePoleQuotient F) (closure Ω) := (id ((continuousOn_dslope (mem_of_superset (IsOpen.mem_nhds hS.left.left (riemannMapping_pole_mem F himage)) subset_closure)).mpr ⟨riemannMappingClosedInverse_continuousOn hb hS hsc F hF hinj himage, DifferentiableOn.differentiableAt (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage) (IsOpen.mem_nhds hS.left.left (riemannMapping_pole_mem F himage))⟩))

theorem riemannMappingInversePoleQuotient_nonzero  (hw : w ∈ closure Ω) :
    riemannMappingInversePoleQuotient F w ≠ 0 := by
  by_cases he : w = F 0
  · subst w
    rw [riemannMappingInversePoleQuotient, dslope_same]
    grind only [riemannMappingClosedInverse_deriv_nonzero, riemannMapping_pole_mem]
  · rw [riemannMappingInversePoleQuotient, dslope_of_ne _ he, slope,
      riemannMappingClosedInverse_zero hb hS hsc F hF hinj himage,
      vsub_eq_sub, sub_zero, smul_eq_mul]
    grind only [riemannMappingClosedInverse_nonzero]

/-- The actual pole-subtracted harmonic function is continuous on the
whole physical closure, including at the pole. -/
theorem riemannMappingGreenCorrection_continuousOn :
    ContinuousOn (riemannMappingGreenCorrection F) (closure Ω) :=
  ((riemannMappingInversePoleQuotient_continuousOn hb hS hsc F hF hinj himage).norm.log
    (fun _ hw => norm_ne_zero_iff.mpr
      (riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage hw))).neg

/-- Removing the true logarithmic pole gives a genuine harmonic
function throughout the domain. No elliptic boundary theorem is used. -/
theorem riemannMappingGreenCorrection_harmonicOnNhd :
    HarmonicOnNhd (riemannMappingGreenCorrection F) Ω := by
  intro w hw
  have hq  :=
    (riemannMappingInversePoleQuotient_differentiableOn hb hS hsc F hF hinj himage).analyticOnNhd
      hS.1.1 w hw
  have ha := hq.harmonicAt_log_norm
    (riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage (subset_closure hw))
  have he : (-1 : ℝ) • (fun x : ℂ => Real.log ‖riemannMappingInversePoleQuotient F x‖) =
      riemannMappingGreenCorrection F := by
    aesop
  have hh := ha.const_smul (c := (-1))
  rw [he] at hh
  exact hh

theorem riemannMappingGreenCorrection_contDiffOn :
    RealSmoothOn (riemannMappingGreenCorrection F) Ω := (fun w hw =>
    have hne := riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage (subset_closure hw);
    ContDiffAt.contDiffWithinAt (ContDiffAt.neg (ContDiffAt.log (ContDiffAt.norm ℝ (AnalyticAt.contDiffAt (AnalyticAt.restrictScalars (DifferentiableOn.analyticOnNhd (riemannMappingInversePoleQuotient_differentiableOn hb hS hsc F hF hinj himage) hS.left.left w hw))) hne) (norm_ne_zero_iff.mpr hne))))

include w hw in
/-- The actual divided-difference derivative away from the physical
pole. Its numerator and both powers of the physical distance are kept
explicit for the finite-energy estimate. -/
theorem riemannMappingInversePoleQuotient_deriv (hne : w ≠ F 0) :
    deriv (riemannMappingInversePoleQuotient F) w =
      (deriv J w * (w - F 0) - J w) / (w - F 0) ^ 2 := by
  have heq : riemannMappingInversePoleQuotient F =ᶠ[𝓝 w]
      (fun z => J z / (z - F 0)) := by
    filter_upwards [eventually_ne_nhds hne] with z hz
    rw [riemannMappingInversePoleQuotient, dslope_of_ne _ hz, slope,
      riemannMappingClosedInverse_zero hb hS hsc F hF hinj himage,
      vsub_eq_sub, sub_zero, smul_eq_mul]
    simp  [div_eq_mul_inv, mul_comm]
  rw [heq.deriv_eq]
  have hdj  :=
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).differentiableAt
      (hS.1.1.mem_nhds hw)
  have hj := hdj.hasDerivAt
  have h := (hj.div ((hasDerivAt_id w).sub_const (F 0)) (sub_ne_zero.mpr hne)).deriv
  simp   at h
  exact h

/-- The actual pole quotient has an L² derivative on the whole
physical domain. The removable pole is handled on a genuine compact
interior ball; outside it only the previously proved inverse energy
and the bounded values of the closed inverse are used. -/
theorem riemannMappingInversePoleQuotient_deriv_memLp :
    MemLp (deriv (riemannMappingInversePoleQuotient F)) 2 (volume.restrict Ω) := by
  let Q := riemannMappingInversePoleQuotient F
  have hQ := riemannMappingInversePoleQuotient_differentiableOn hb hS hsc F hF hinj himage
  have hQc  := (hQ.deriv hS.1.1).continuousOn
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hS.1.1.mem_nhds (riemannMapping_pole_mem F himage))
  have hDbounded  :=
    ((isCompact_closedBall (F 0) r).image_of_continuousOn (hQc.mono hball)).isBounded
  obtain ⟨B, hBpos, hB⟩ := hDbounded.subset_ball_lt 0 0
  have hlocal w (hw : w ∈ closedBall (F 0) r) : ‖deriv Q w‖ ≤ B := by
    have hh := hB (mem_image_of_mem (deriv Q) hw)
    exact (show ‖deriv Q w‖ < B by simp_all).le
  have hJm : MemLp (deriv J) 2 (volume.restrict Ω) := by
    have hJc  :=
      ((riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).deriv
        hS.1.1).continuousOn
    apply (memLp_two_iff_integrable_sq_norm
      (hJc.aestronglyMeasurable hS.1.1.measurableSet)).mpr
    exact riemannMappingClosedInverse_deriv_sq_integrable hb hS hsc F hF hinj himage
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hb.measure_lt_top⟩
  have hmajor : MemLp (fun w => r⁻¹ * ‖deriv J w‖ + (B + r⁻¹ ^ 2)) 2
      (volume.restrict Ω) :=
    (hJm.norm.const_mul r⁻¹).add (memLp_const (B + r⁻¹ ^ 2))
  apply hmajor.mono' (hQc.aestronglyMeasurable hS.1.1.measurableSet)
  filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
  by_cases hwball : w ∈ closedBall (F 0) r
  · have hp : 0 ≤ r⁻¹ * ‖deriv J w‖ + r⁻¹ ^ 2 := by positivity
    grind
  · have hdist : r ≤ ‖w - F 0‖ := by
      have hh : r < dist w (F 0) := lt_of_not_ge hwball
      have hh' : r < ‖w - F 0‖ := by simpa only [dist_eq_norm] using hh
      exact hh'.le
    have hdpos  := hr.trans_le hdist
    have hne  := sub_ne_zero.mp (norm_ne_zero_iff.mp hdpos.ne')
    have hJn  := mem_closedBall_zero_iff.mp
      (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage (subset_closure hw)).1
    have hstep : ‖deriv Q w‖ ≤ ‖deriv J w‖ / r + 1 / r ^ 2 := by
      rw [riemannMappingInversePoleQuotient_deriv hb hS hsc F hF hinj himage hw hne,
        norm_div, norm_pow]
      calc
        _ ≤ (‖deriv J w * (w - F 0)‖ + ‖J w‖) / ‖w - F 0‖ ^ 2 :=
          div_le_div_of_nonneg_right (norm_sub_le _ _) (sq_nonneg _)
        _ = ‖deriv J w‖ / ‖w - F 0‖ + ‖J w‖ / ‖w - F 0‖ ^ 2 := by
          rw [norm_mul]
          field_simp [hdpos.ne']
        _ ≤ ‖deriv J w‖ / r + 1 / r ^ 2 := add_le_add
          (div_le_div_of_nonneg_left (norm_nonneg _) hr hdist)
          ((div_le_div_of_nonneg_right hJn (sq_nonneg _)).trans
            (div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hr)
              ((sq_le_sq₀ hr.le hdpos.le).mpr hdist)))
    have heq : ‖deriv J w‖ / r + 1 / r ^ 2 = r⁻¹ * ‖deriv J w‖ + r⁻¹ ^ 2 := by
      ring
    linarith

/-- The actual pole quotient has a strictly positive modulus bound on
the entire physical closure, including the removable pole. -/
theorem exists_riemannMappingInversePoleQuotient_norm_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ closure Ω, c ≤ ‖riemannMappingInversePoleQuotient F w‖ :=
  hb.isCompact_closure.exists_forall_le'
    (riemannMappingInversePoleQuotient_continuousOn hb hS hsc F hF hinj himage).norm
    (fun _ hw => norm_pos_iff.mpr
      (riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage hw))

/-- Every genuine real coordinate derivative of the constructed
harmonic correction belongs to L². This is an energy conclusion, not
a boundary smoothness assumption. -/
theorem riemannMappingGreenCorrection_realGradient_memLp i :
    MemLp (fun w => fderiv ℝ (riemannMappingGreenCorrection F) w (coordDir i)) 2
      (volume.restrict Ω) := by
  obtain ⟨c, hc, hcn⟩ := exists_riemannMappingInversePoleQuotient_norm_lower_bound
    hb hS hsc F hF hinj himage
  have hQm := riemannMappingInversePoleQuotient_deriv_memLp hb hS hsc F hF hinj himage
  have hmajor := hQm.norm.const_mul c⁻¹
  have hcont : ContinuousOn (fun w => fderiv ℝ (riemannMappingGreenCorrection F) w (coordDir i)) Ω :=
    ((riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage).continuousOn_fderiv_of_isOpen
      hS.1.1 (by simp)).clm_apply continuousOn_const
  apply hmajor.mono' (hcont.aestronglyMeasurable hS.1.1.measurableSet)
  filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
  have hQ := (riemannMappingInversePoleQuotient_differentiableOn hb hS hsc F hF hinj himage).differentiableAt
    (hS.1.1.mem_nhds hw)
  have hne := riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage (subset_closure hw)
  calc
    _ ≤ ‖deriv (riemannMappingInversePoleQuotient F) w‖ * ‖coordDir i‖ /
        ‖riemannMappingInversePoleQuotient F w‖ :=
      norm_fderiv_neg_log_norm_holomorphic_le hQ hne _
    _ ≤ ‖deriv (riemannMappingInversePoleQuotient F) w‖ / c := by
      rw [norm_coordDir, mul_one]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hc (hcn w (subset_closure hw))
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- The true harmonic correction also has an L² value class because
it is continuous on the actual compact physical closure. -/
theorem riemannMappingGreenCorrection_value_memLp :
    MemLp (riemannMappingGreenCorrection F) 2 (volume.restrict Ω) := by
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by simpa   using hb.measure_lt_top⟩
  have hcont := riemannMappingGreenCorrection_continuousOn hb hS hsc F hF hinj himage
  have hbounded  :=
    (hb.isCompact_closure.image_of_continuousOn hcont).isBounded
  obtain ⟨B, _, hB⟩ := hbounded.subset_ball_lt 0 0
  apply MemLp.of_bound ((hcont.mono subset_closure).aestronglyMeasurable hS.1.1.measurableSet) B
  filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
  exact (show ‖riemannMappingGreenCorrection F w‖ < B by
    simpa   using hB
      (mem_image_of_mem (riemannMappingGreenCorrection F) (subset_closure hw))).le

include w hw in
private theorem riemannMappingGreenCorrection_complex_fderiv v :
    fderiv ℝ (fun z => (riemannMappingGreenCorrection F z : ℂ)) w v =
      (fderiv ℝ (riemannMappingGreenCorrection F) w v : ℂ) := by
  have hd  :=
    ((riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage).differentiableOn
      (by simp)).differentiableAt (hS.1.1.mem_nhds hw)
  change fderiv ℝ (Complex.ofRealCLM ∘ riemannMappingGreenCorrection F) w v = _
  rw [fderiv_comp w Complex.ofRealCLM.differentiableAt hd]
  simp  

end


private theorem riemannMappingGreenCorrection_complex_value_memLp :
    MemLp (fun w => (riemannMappingGreenCorrection F w : ℂ)) 2 (volume.restrict Ω) := by
  have hm := riemannMappingGreenCorrection_value_memLp hb hS hsc F hF hinj himage
  have hc  :=
    Complex.ofRealCLM.continuous.comp_continuousOn
      ((riemannMappingGreenCorrection_continuousOn hb hS hsc F hF hinj himage).mono subset_closure)
  apply hm.congr_norm (hc.aestronglyMeasurable hS.1.1.measurableSet)
  simp_all

private theorem riemannMappingGreenCorrection_complex_gradient_memLp i :
    MemLp (fun w => fderiv ℝ (fun z => (riemannMappingGreenCorrection F z : ℂ)) w (coordDir i)) 2
      (volume.restrict Ω) := by
  have hs : RealSmoothOn (fun z => (riemannMappingGreenCorrection F z : ℂ)) Ω :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage)
  have hc := (hs.continuousOn_fderiv_of_isOpen hS.1.1 (by simp)).clm_apply
    (show ContinuousOn (fun _ : ℂ => coordDir i) Ω from continuousOn_const)
  have hm := riemannMappingGreenCorrection_realGradient_memLp hb hS hsc F hF hinj himage i
  apply hm.congr_norm (hc.aestronglyMeasurable hS.1.1.measurableSet)
  filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
  rw [riemannMappingGreenCorrection_complex_fderiv hb hS hsc F hF hinj himage hw]
  simp  

/-- The pole-subtracted physical Green function is an actual weak
H¹ vector, represented by its constructed harmonic solution and its
true real derivatives. No boundary elliptic regularity is an input. -/
theorem exists_riemannMappingGreenCorrectionH1 :
    ∃ u : NeumannH1 Ω,
      (h1Value Ω u : PlaneMap) =ᵐ[volume.restrict Ω]
        (fun w => (riemannMappingGreenCorrection F w : ℂ)) ∧
      ∀ i : Coord, (h1Gradient Ω i u : PlaneMap) =ᵐ[volume.restrict Ω]
        (fun w => (fderiv ℝ (riemannMappingGreenCorrection F) w (coordDir i) : ℂ)) := by
  have hu := riemannMappingGreenCorrection_complex_value_memLp hb hS hsc F hF hinj himage
  have hg := riemannMappingGreenCorrection_complex_gradient_memLp hb hS hsc F hF hinj himage
  have hs : RealSmoothOn (fun z => (riemannMappingGreenCorrection F z : ℂ)) Ω :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage)
  have hweak := isWeakGradient_of_contDiffOn hS.1.1 hs hu hg
  refine ⟨h1Vector hweak, ?_, ?_⟩
  · exact hu.coeFn_toLp
  · intro i
    rw [h1Gradient_h1Vector]
    filter_upwards [(hg i).coeFn_toLp, ae_restrict_mem hS.1.1.measurableSet] with w hw hwΩ
    grind only [riemannMappingGreenCorrection_complex_fderiv, PolyaNeumann.riemannMappingGreenCorrection, PolyaNeumann.coordDir]

/-- The physical correction is exactly the Green function plus the
fundamental logarithmic singularity away from the actual pole. -/
theorem riemannMappingGreenCorrection_eq  (hw : w ∈ closure Ω) (hne : w ≠ F 0) :
    riemannMappingGreenCorrection F w = riemannMappingGreen F w + Real.log ‖w - F 0‖ := by
  have hnJ  := norm_ne_zero_iff.mpr
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage hw hne)
  have hnd  := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  rw [riemannMappingGreenCorrection, riemannMappingInversePoleQuotient,
    dslope_of_ne _ hne, slope, riemannMappingClosedInverse_zero hb hS hsc F hF hinj himage,
    vsub_eq_sub, sub_zero, smul_eq_mul, norm_mul, norm_inv, Real.log_mul (inv_ne_zero hnd) hnJ, Real.log_inv,
    riemannMappingGreen]
  ring

/-- The actual Dirichlet boundary data of the pole-subtracted harmonic
function are the smooth physical function `log ‖w - F 0‖`. -/
theorem riemannMappingGreenCorrection_frontier  (hw : w ∈ frontier Ω) :
    riemannMappingGreenCorrection F w = Real.log ‖w - F 0‖ := by
  have hne : w ≠ F 0 := by
    intro he
    rw [he, hS.1.1.frontier_eq] at hw
    measurability
  rw [riemannMappingGreenCorrection_eq hb hS hsc F hF hinj himage
    (frontier_subset_closure hw) hne,
    riemannMappingGreen_frontier hb hS hsc F hF hinj himage hw, zero_add]

omit hb hS hsc hF hinj himage in
/-- The actual physical Dirichlet data are smooth on an open
neighborhood of the entire frontier, because the pole is interior. -/
theorem riemannMappingGreenBoundaryData_contDiffOn :
    RealSmoothOn (fun w : ℂ => Real.log ‖w - F 0‖) {F 0}ᶜ := by
  intro w hw
  have hne  := sub_ne_zero.mpr hw
  exact (((contDiffAt_id.sub contDiffAt_const).norm ℝ hne).log
    (norm_ne_zero_iff.mpr hne)).contDiffWithinAt

/-- A genuine globally smooth, compactly supported physical test
function has exactly the pole-subtracted Green function's boundary
data. The cutoff extends already smooth logarithmic data near the
frontier, not the unknown Riemann-map boundary jets. -/
theorem exists_riemannMappingGreenCorrection_smooth_boundary_data :
    ∃ b : smoothTraceTests, ∀ w ∈ frontier Ω,
      riemannMappingGreenCorrection F w = (b w).re := by
  have hk  := hb.isCompact_closure.of_isClosed_subset
    isClosed_frontier frontier_subset_closure
  have hku : frontier Ω ⊆ ({F 0} : PlanarSet)ᶜ := by
    intro w hw he
    have hwe  := he
    rw [hwe, hS.1.1.frontier_eq] at hw
    measurability
  have hs : RealSmoothOn (fun w : ℂ => (Real.log ‖w - F 0‖ : ℂ)) {F 0}ᶜ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (riemannMappingGreenBoundaryData_contDiffOn F)
  obtain ⟨b, hbtest, hbe⟩ := exists_smooth_compact_extension hk isOpen_compl_singleton hku hs
  refine ⟨⟨b, hbtest⟩, ?_⟩
  intro w hw
  change riemannMappingGreenCorrection F w = (b w).re
  rw [(hbe w hw).self_of_nhds, Complex.ofReal_re]
  grind only [riemannMappingGreenCorrection_frontier]

end ActualMap

private theorem exists_quadratic_smooth_graph_bound 
    (hf : RealSmooth f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |x| ≤ 1 →
      |f x - f 0 - deriv f 0 * x| ≤ M * x ^ 2 := by
  have hf2 : ContDiff ℝ (1 + 1 : ℕ) f :=
    hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hd : ContDiff ℝ 1 (deriv f) := hf2.deriv'
  obtain ⟨K, hK⟩ := hd.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_Icc (-1) 1) isCompact_Icc
  refine ⟨K, K.coe_nonneg, ?_⟩
  intro x hx
  have hxI  := abs_le.mp hx
  have h0I : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hsub  := uIcc_subset_Icc h0I hxI
  have hsmall y (hy : y ∈ uIcc (0 : ℝ) x) : |y| ≤ |x| := by
    apply abs_le.mpr
    have hxlo := neg_abs_le x
    have hxhi := le_abs_self x
    rcases mem_uIcc.mp hy with hy | hy <;> constructor <;> linarith [abs_nonneg x]
  let g  := fun y => f y - f 0 - deriv f 0 * y
  have hg y : HasDerivAt g (deriv f y - deriv f 0) y := by
    have h := ((hf.differentiable (by simp) y).hasDerivAt.sub_const (f 0)).sub
        ((hasDerivAt_id y).const_mul (deriv f 0))
    simp   at h
    exact h
  have hb (y : ℝ) (hy : y ∈ uIcc (0 : ℝ) x) :
      ‖deriv g y‖ ≤ (K : ℝ) * |x| := by
    rw [(hg y).deriv]
    have hh := hK.dist_le_mul y (hsub hy) 0 h0I
    have hh' : ‖deriv f y - deriv f 0‖ ≤ (K : ℝ) * |y| := by
      measurability
    exact hh'.trans (mul_le_mul_of_nonneg_left (hsmall y hy) K.coe_nonneg)
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun y (_) => (hg y).differentiableAt) hb
    (convex_uIcc 0 x) left_mem_uIcc right_mem_uIcc
  simpa  [g, mul_assoc, ← pow_two, sq_abs] using hm

/-- The genuine smooth graph definition supplies an actual interior
tangent ball at each physical boundary point. This gives geometric
input for a Hopf barrier; it does not assume or assert a Hopf lemma. -/
theorem exists_smoothDomain_interior_tangent_ball  (hS : IsSmoothDomain Ω)
     (hp : p ∈ frontier Ω) :
    ∃ v : ℂ, ∃ R : ℝ, 0 < R ∧ ball v R ⊆ Ω ∧ p ∈ sphere v R := by
  obtain ⟨c, r, h, K, f, hc, hr, hh, hf, _, hf0, _, hgraph⟩ := hS.2 p hp
  obtain ⟨M, hM, hquad⟩ := exists_quadratic_smooth_graph_bound hf
  let a  := deriv f 0
  let n  := -a + Complex.I
  let C  := ‖n‖
  have hC : 0 < C := by
    apply norm_pos_iff.mpr
    intro he
    have him := congrArg Complex.im he
    norm_num [n] at him
  have hCsq : C ^ 2 = a ^ 2 + 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [n, Complex.normSq_apply, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.I_re, add_zero, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
      neg_zero, Complex.I_im, zero_add]
    ring
  let e  := min (min (r / (2 * C)) (h / (2 * C)))
    (min (1 / (2 * C)) (1 / (2 * (M + 1))))
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨ρ, hρ, hρe⟩ := exists_between he
  have hρr : 2 * ρ * C < r := by
    have ht := (lt_div_iff₀ (show 0 < 2 * C by positivity)).mp
      (lt_of_lt_of_le hρe ((min_le_left _ _).trans (min_le_left _ _)))
    nlinarith
  have hρh : 2 * ρ * C < h := by
    have ht := (lt_div_iff₀ (show 0 < 2 * C by positivity)).mp
      (lt_of_lt_of_le hρe ((min_le_left _ _).trans (min_le_right _ _)))
    nlinarith
  have hρ1 : 2 * ρ * C < 1 := by
    have ht := (lt_div_iff₀ (show 0 < 2 * C by positivity)).mp
      (lt_of_lt_of_le hρe ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith
  have hρM : 2 * ρ * M ≤ 1 := by
    have ht := (lt_div_iff₀ (show 0 < 2 * (M + 1) by positivity)).mp
      (lt_of_lt_of_le hρe ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith
  let v  := p + ρ * n / c
  let R  := ρ * C
  have hR  := mul_pos hρ hC
  have hvc : ‖v - p‖ = R := by
    simp only [v, add_sub_cancel_left, norm_div, norm_mul, hc, div_one,
      Complex.norm_real, Real.norm_of_nonneg hρ.le, R, C]
  have hcne  := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  refine ⟨v, R, hR, ?_, ?_⟩
  · intro w hw
    have hwR : ‖w - v‖ < R := by simpa only [mem_ball, dist_eq_norm] using hw
    have hwp : ‖w - p‖ < 2 * ρ * C := by
      calc
        _ ≤ ‖w - v‖ + ‖v - p‖ := norm_sub_le_norm_sub_add_norm_sub w v p
        _ < R + R := by rw [hvc]; linarith only [hwR]
        _ = _ := by dsimp [R]; ring
    let z  := c * (w - p)
    have hz : ‖z‖ = ‖w - p‖ := by dsimp [z]; rw [norm_mul, hc, one_mul]
    have hzr  := (Complex.abs_re_le_norm z).trans_lt (by rw [hz]; exact hwp.trans hρr)
    have hzh  := (Complex.abs_im_le_norm z).trans_lt (by rw [hz]; exact hwp.trans hρh)
    apply (hgraph w hzr hzh).mpr
    have hx1  :=
      ((Complex.abs_re_le_norm z).trans_lt (by rw [hz]; exact hwp.trans hρ1)).le
    have hfx : f z.re ≤ a * z.re + M * z.re ^ 2 := by
      have ht := (abs_le.mp (hquad z.re hx1)).2
      linarith
    have hball : ‖z - (ρ : ℂ) * n‖ < R := by
      have hzv : z - (ρ : ℂ) * n = c * (w - v) := by
        grind
      simp_all
    have hs : (z.re + ρ * a) ^ 2 + (z.im - ρ) ^ 2 < ρ ^ 2 * (a ^ 2 + 1) := by
      have ht := (sq_lt_sq₀ (norm_nonneg _) hR.le).mpr hball
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at ht
      have hre : (z - (ρ : ℂ) * n).re = z.re + ρ * a := by simp [n]
      have him : (z - (ρ : ℂ) * n).im = z.im - ρ := by simp [n]
      rw [hre, him] at ht
      have hRsq : R ^ 2 = ρ ^ 2 * (a ^ 2 + 1) := by dsimp [R]; rw [mul_pow, hCsq]
      rw [hRsq] at ht
      nlinarith
    have hprod := mul_nonneg (show 0 ≤ 1 - 2 * ρ * M by linarith) (sq_nonneg z.re)
    have hy : a * z.re + M * z.re ^ 2 < z.im := by
      by_contra hn
      have hny := le_of_not_gt hn
      have hmul := mul_le_mul_of_nonneg_left hny (show 0 ≤ 2 * ρ by positivity)
      nlinarith [sq_nonneg z.im]
    exact hfx.trans_lt hy
  · simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hvc

section
variable {Ω } (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω) (F ) (hF : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk) (himage : F '' unitDisk = Ω) {p } (hp : p ∈ frontier Ω)
include Ω hb hS hsc F hF hinj himage p hp

/-- Each actual physical frontier point has a strictly positive Green
lower barrier on a true tangent ball. Both the ball and the barrier
are derived from the original smooth domain and interior conformal
map; no boundary derivative or desired boundary regularity occurs in
the hypotheses. -/
theorem exists_riemannMappingGreen_boundary_lower_barrier :
    ∃ v : ℂ, ∃ R A : ℝ, 0 < R ∧ 0 < A ∧ ball v R ⊆ Ω ∧ p ∈ sphere v R ∧
      ∀ w ∈ ball v R, w ≠ F 0 → A * (R - ‖w - v‖) ≤ riemannMappingGreen F w := by
  grind only [exists_smoothDomain_interior_tangent_ball, exists_riemannMappingGreen_ball_lower_barrier]

/-- A genuine unit inward ray has a strictly positive Green slope
lower bound at every physical frontier point. The whole short ray
avoids the actual Green pole. This is a proved boundary estimate,
without any assumed existence of boundary derivatives. -/
theorem exists_riemannMappingGreen_inward_ray_lower :
    ∃ b : ℂ, ∃ δ A : ℝ, ‖b‖ = 1 ∧ 0 < δ ∧ 0 < A ∧
      ∀ t : ℝ, 0 < t → t < δ → p + (t : ℂ) * b ∈ Ω ∧
        p + (t : ℂ) * b ≠ F 0 ∧ A * t ≤ riemannMappingGreen F (p + (t : ℂ) * b) := by
  obtain ⟨v, R, A, hR, hA, hball, hpR, hbarrier⟩ :=
    exists_riemannMappingGreen_boundary_lower_barrier hb hS hsc F hF hinj himage hp
  have hvp : ‖v - p‖ = R := by simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hpR
  let b  := R⁻¹ * (v - p)
  have hb1 : ‖b‖ = 1 := by
    aesop
  have hpne : p ≠ F 0 := by
    intro he
    rw [he, hS.1.1.frontier_eq] at hp
    simp_all [riemannMapping_pole_mem]
  let δ  := min R (‖p - F 0‖ / 2)
  have hδ : 0 < δ := lt_min hR (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hpne)) (by norm_num))
  refine ⟨b, δ, A, hb1, hδ, hA, ?_⟩
  intro t ht htδ
  have htR  := lt_of_lt_of_le htδ (min_le_left _ _)
  have htP  := lt_of_lt_of_le htδ (min_le_right _ _)
  have htd  := (div_lt_one hR).mpr htR
  have hdist : ‖p + (t : ℂ) * b - v‖ = R - t := by
    have he : p + (t : ℂ) * b - v = ((t / R - 1 : ℝ) : ℂ) * (v - p) := by
      dsimp [b]
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr htd.le), hvp]
    field_simp [hR.ne']; ring
  have hwball : p + (t : ℂ) * b ∈ ball v R := by
    rw [mem_ball, dist_eq_norm, hdist]
    linarith
  have hwne : p + (t : ℂ) * b ≠ F 0 := by
    have hn : ‖p + (t : ℂ) * b - p‖ = t := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, hb1, mul_one]
    intro he
    rw [he, norm_sub_rev] at hn
    nlinarith
  refine ⟨hball hwball, hwne, ?_⟩
  have hh := hbarrier _ hwball hwne
  simp_all

end


end PolyaNeumann

end
