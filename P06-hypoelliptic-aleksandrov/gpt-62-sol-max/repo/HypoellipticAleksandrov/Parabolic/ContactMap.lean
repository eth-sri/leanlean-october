module

public import HypoellipticAleksandrov.Parabolic.Derivatives
import HypoellipticAleksandrov.Parabolic.EllipticityClosure
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Parabolic contact-map data

This module defines the affine velocity functions, slope--intercept wedge,
parabolic normal map, and measurable-sign-set candidate used in the smooth
parabolic ABP argument.  Coverage and Jacobian results belong to later modules.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Matrix

section
variable {d : ℕ} (y₀ : PDE.Vec d) (h : ℝ)
include y₀ h

/-- The affine velocity function with intercept `h`, slope `p`, and center `y₀`. -/
def affineVelocity (p : PDE.Vec d)
    (v : PDE.Vec d) : ℝ :=
  h + PDE.vecDot p (v - y₀)

/-- Evaluation of an affine velocity function. -/
@[simp] theorem affineVelocity_apply
    (p v : PDE.Vec d) :
    affineVelocity y₀ h p v = h + PDE.vecDot p (v - y₀) :=
  rfl

end

/-- The open slope--intercept wedge associated with a height `M`. -/
def slopeInterceptWedge (d : ℕ) (M : ℝ) : Set (TimeVelocity d) :=
  Set.Ioo (M / 2) (3 * M / 4) ×ˢ PDE.euclideanBall (0 : PDE.Vec d) (M / 4)

section
variable {d : ℕ}

/-- Membership in the slope--intercept wedge. -/
@[simp] theorem mem_slopeInterceptWedge_iff {M h : ℝ} {p : PDE.Vec d} :
    (h, p) ∈ slopeInterceptWedge d M ↔
      M / 2 < h ∧ h < 3 * M / 4 ∧ p ∈ PDE.euclideanBall (0 : PDE.Vec d) (M / 4) := by
  change (M / 2 < h ∧ h < 3 * M / 4) ∧ p ∈ PDE.euclideanBall (0 : PDE.Vec d) (M / 4) ↔
    M / 2 < h ∧ h < 3 * M / 4 ∧ p ∈ PDE.euclideanBall (0 : PDE.Vec d) (M / 4)
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hp⟩
    exact ⟨hlower, hupper, hp⟩
  · rintro ⟨hlower, hupper, hp⟩
    exact ⟨⟨hlower, hupper⟩, hp⟩

section
variable (u : TimeVelocity d → ℝ) (y₀ : PDE.Vec d)
include u y₀

/-- The parabolic normal map built from the velocity gradient of `u`. -/
noncomputable def parabolicNormalMap :
    TimeVelocity d → TimeVelocity d :=
  fun z ↦
    (u z - PDE.vecDot (velocityGradient u z) (z.2 - y₀), velocityGradient u z)

/-- Evaluation of the parabolic normal map. -/
@[simp] theorem parabolicNormalMap_apply (z : TimeVelocity d) :
    parabolicNormalMap u y₀ z =
      (u z - PDE.vecDot (velocityGradient u z) (z.2 - y₀), velocityGradient u z) :=
  rfl

end

/-- In the slope wedge an affine function is positive and below the chosen height. -/
theorem affineVelocity_bounds_of_wedge {d : ℕ} {y₀ p v : PDE.Vec d} {M R h : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hl : M / 2 < h) (hu : h < 3 * M / 4)
    (hp : p ∈ PDE.euclideanBall (0 : PDE.Vec d) (M / (4 * R)))
    (hv : PDE.vecEuclideanNorm (v - y₀) ≤ R) :
    0 < affineVelocity y₀ h p v ∧ affineVelocity y₀ h p v < M := by
  have hs : PDE.vecEuclideanNorm p < M / (4 * R) := by
    simpa using (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (x₀ := (0 : PDE.Vec d)) (x := p) (by positivity)).mp hp
  have hprod := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hv (PDE.vecEuclideanNorm_nonneg p))
    (mul_lt_mul_of_pos_right hs hR)
  have hc : M / (4 * R) * R = M / 4 := by field_simp
  rw [hc] at hprod
  have hd := abs_lt.mp ((PDE.abs_vecDot_le_vecEuclideanNorm_mul p (v - y₀)).trans_lt hprod)
  simp only [affineVelocity_apply]
  constructor <;> linarith [hd.1, hd.2]

/-- The normal map at an affine contact recovers the intercept and slope. -/
theorem parabolicNormalMap_eq_of_affineContact {d : ℕ} {u : TimeVelocity d → ℝ}
    {z : TimeVelocity d} {y₀ p : PDE.Vec d} {h : ℝ}
    (hu : DifferentiableAt ℝ u z) (he : u z = affineVelocity y₀ h p z.2)
    (hm : IsLocalMax (fun v => u (z.1, v) - affineVelocity y₀ h p v) z.2) :
    parabolicNormalMap u y₀ z = (h, p) := by
  rw [parabolicNormalMap_apply, velocityGradient_eq_of_spatial_localMax_affineContact hu hm,
    he, affineVelocity_apply, add_sub_cancel_right]

theorem zero_between_of_continuousOn_of_neg_pos {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b)) (ha : f a < 0) (hb : 0 < f b) :
    ∃ c ∈ Set.Ioo a b, f c = 0 := by
  obtain ⟨c, hc, he⟩ := intermediate_value_Icc hab.le hf ⟨ha.le, hb.le⟩
  exact ⟨c, ⟨lt_of_le_of_ne hc.1 (by rintro rfl; linarith),
    lt_of_le_of_ne hc.2 (by rintro rfl; linarith)⟩, he⟩

/-- Before the first contact time, the comparison is nonpositive on that time line. -/
theorem nonpos_at_or_before_firstContact {d : ℕ} {g : TimeVelocity d → ℝ}
    {K : Set (TimeVelocity d)} {z : TimeVelocity d} {t : ℝ}
    (hmin : ∀ q ∈ K ∩ {q | 0 ≤ g q}, z.1 ≤ q.1) (hzero : g z = 0)
    (ht : t ≤ z.1) (hK : (t, z.2) ∈ K) : g (t, z.2) ≤ 0 := by
  rcases ht.eq_or_lt with rfl | ht
  · exact hzero.le
  · exact le_of_not_ge fun h => (not_le_of_gt ht) (hmin _ ⟨hK, h⟩)

/-- The interior sign set on which the parabolic Jacobian has the required sign. -/
def parabolicSignSet (T : ℝ) (y₀ : PDE.Vec d) (u : TimeVelocity d → ℝ) :
    Set (TimeVelocity d) :=
  {z | z ∈ parabolicInterior T y₀ ∧ 0 < u z ∧
    0 ≤ timeDerivative u z ∧ (-velocityHessian u z).PosSemidef}

/-- Membership in the parabolic sign set. -/
@[simp] theorem mem_parabolicSignSet_iff {T : ℝ} {y₀ : PDE.Vec d}
    {u : TimeVelocity d → ℝ} {z : TimeVelocity d} :
    z ∈ parabolicSignSet T y₀ u ↔
      z ∈ parabolicInterior T y₀ ∧ 0 < u z ∧
        0 ≤ timeDerivative u z ∧ (-velocityHessian u z).PosSemidef :=
  Iff.rfl

end

section
variable {d : ℕ} {u : TimeVelocity d → ℝ} (hu : ContDiff ℝ 2 u)
include hu

/-- A globally `C²` scalar function has continuous time derivative. -/
theorem continuous_timeDerivative : Continuous (timeDerivative u) := by
  exact ((hu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

/-- A globally `C²` scalar function has continuous velocity Hessian. -/
theorem continuous_velocityHessian : Continuous (velocityHessian u) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun z : TimeVelocity d ↦
    fderiv ℝ (fderiv ℝ u) z (0, Pi.single i 1) (0, Pi.single j 1))
  have hdu :=
    hu.fderiv_right (m := 1) (by norm_num)
  exact (((hdu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const).continuous

/-- The parabolic sign set of a globally `C²` scalar function is measurable. -/
theorem measurableSet_parabolicSignSet (T : ℝ) (y₀ : PDE.Vec d) :
    MeasurableSet (parabolicSignSet T y₀ u) := by
  have htime : Continuous (timeDerivative u) := continuous_timeDerivative hu
  have hhess : Continuous (velocityHessian u) := continuous_velocityHessian hu
  have hpsd : MeasurableSet {z : TimeVelocity d | (-velocityHessian u z).PosSemidef} :=
    ((isClosed_posSemidef d).preimage hhess.neg).measurableSet
  rw [show parabolicSignSet T y₀ u =
      parabolicInterior T y₀ ∩ {z | 0 < u z} ∩ {z | 0 ≤ timeDerivative u z} ∩
        {z | (-velocityHessian u z).PosSemidef} by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, mem_parabolicSignSet_iff]
    constructor
    · rintro ⟨hinterior, hpositive, htime, hpsd⟩
      exact ⟨⟨⟨hinterior, hpositive⟩, htime⟩, hpsd⟩
    · rintro ⟨⟨⟨hinterior, hpositive⟩, htime⟩, hpsd⟩
      exact ⟨hinterior, hpositive, htime, hpsd⟩]
  exact (((measurableSet_parabolicInterior T y₀).inter
    (isOpen_lt continuous_const hu.continuous).measurableSet).inter
      (isClosed_le continuous_const htime).measurableSet).inter hpsd

end

end HypoellipticAleksandrov.Parabolic
