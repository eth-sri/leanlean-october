module

public import HypoellipticAleksandrov.Parabolic.ABP
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.Parabolic.KrylovCylinder
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine
import Mathlib.Analysis.Calculus.Deriv.Shift
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Geometry.EuclideanBall.Topology

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal MatrixOrder

/-- Reflection of a time--velocity point about the time slice `t = 1 / 2`. -/
def timeReflection {d : ℕ} (z : TimeVelocity d) : TimeVelocity d :=
  (1 - z.1, z.2)

/-- Pullback of a scalar field by the fixed time reflection. -/
def timeReflectedScalar {d : ℕ} (f : TimeVelocity d → ℝ) : TimeVelocity d → ℝ :=
  fun z => f (timeReflection z)

/-- Pullback of a curried coefficient field by the fixed time reflection. -/
def timeReflectedCoefficient {d : ℕ} (A : CoefficientField d) : CoefficientField d :=
  fun t v => A (1 - t) v

/-- Evaluation of a reflected scalar field. -/
@[simp] theorem timeReflectedScalar_apply {d : ℕ} (f : TimeVelocity d → ℝ)
    (z : TimeVelocity d) :
    timeReflectedScalar f z = f (timeReflection z) :=
  rfl

/-- Evaluation of a reflected coefficient field at a time--velocity pair. -/
@[simp] theorem coefficientAt_timeReflectedCoefficient {d : ℕ}
    (A : CoefficientField d) (z : TimeVelocity d) :
    coefficientAt (timeReflectedCoefficient A) z =
      coefficientAt A (timeReflection z) :=
  rfl


/-- Time reflection is continuous. -/
theorem continuous_timeReflection {d : ℕ} : Continuous (@timeReflection d) := by
  exact (continuous_const.sub continuous_fst).prodMk continuous_snd


/-- Reflection preserves product Lebesgue volume. -/
theorem timeReflection_measurePreserving {d : ℕ} :
    MeasurePreserving (@timeReflection d) (volume : Measure (TimeVelocity d)) volume := by
  let htime : MeasurePreserving (fun t : ℝ => 1 - t)
      (volume : Measure ℝ) volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      (measurePreserving_add_left (volume : Measure ℝ) 1).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hprod := htime.prod (MeasurePreserving.id (volume : Measure (PDE.Vec d)))
  rw [volume_timeVelocity_eq_prod d]
  change MeasurePreserving (fun p : ℝ × PDE.Vec d => (1 - p.1, p.2)) _ _
  simpa only [Prod.map_def, id_eq] using hprod

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open scoped Topology ENNReal


variable {d : ℕ}

/-- The reflect-and-rescale map `(t, y) ↦ (1 - R² t, v_* + R y)`. -/
def reflectScale (R : ℝ) (vStar : PDE.Vec d) (z : TimeVelocity d) : TimeVelocity d :=
  (1 - R ^ 2 * z.1, vStar + R • z.2)

/-- The reflect-and-rescale map is the time reflection of a parabolic affine map. -/
theorem reflectScale_eq (R : ℝ) (vStar : PDE.Vec d) :
    reflectScale R vStar = timeReflection ∘ parabolicAffine 0 vStar R := by
  funext z
  simp only [reflectScale, Function.comp_apply, timeReflection, parabolicAffine, zero_add]

/-- The reflect-and-rescale map is continuous. -/
theorem continuous_reflectScale (R : ℝ) (vStar : PDE.Vec d) :
    Continuous (reflectScale R vStar) := by
  unfold reflectScale
  fun_prop

/-- Reflection reverses the scalar time derivative. -/
theorem scalarTimeDerivative_timeReflectedScalar (V : TimeVelocity d → ℝ)
    (z : TimeVelocity d) :
    scalarTimeDerivative (timeReflectedScalar V) z =
      -scalarTimeDerivative V (timeReflection z) := by
  unfold scalarTimeDerivative timeReflectedScalar timeReflection
  exact deriv_comp_const_sub (f := fun r : ℝ => V (r, z.2)) (a := 1) (x := z.1)

/-- Reflection preserves the scalar spatial gradient. -/
theorem scalarSpatialGradient_timeReflectedScalar (V : TimeVelocity d → ℝ)
    (z : TimeVelocity d) :
    scalarSpatialGradient (timeReflectedScalar V) z =
      scalarSpatialGradient V (timeReflection z) :=
  rfl

/-- Reflection preserves the scalar spatial Hessian. -/
theorem scalarSpatialHessian_timeReflectedScalar (V : TimeVelocity d → ℝ)
    (z : TimeVelocity d) :
    scalarSpatialHessian (timeReflectedScalar V) z =
      scalarSpatialHessian V (timeReflection z) :=
  rfl



/-- The spatial gradient under a parabolic affine pullback. -/
theorem scalarSpatialGradient_parabolicAffine (u : TimeVelocity d → ℝ) (b : ℝ)
    (v : PDE.Vec d) (ρ : ℝ) (z : TimeVelocity d)
    (hu : DifferentiableAt ℝ (fun y : PDE.Vec d => u (b + ρ ^ 2 * z.1, y)) (v + ρ • z.2)) :
    scalarSpatialGradient (u ∘ parabolicAffine b v ρ) z =
      ρ • scalarSpatialGradient u (parabolicAffine b v ρ z)  := by
  have gradient_affine_aux (f : PDE.Vec d → ℝ) (ρ : ℝ) (x : PDE.Vec d) (hf : DifferentiableAt ℝ f (v + ρ • x)) :
      PDE.classicalGradient (fun y => f (v + ρ • y)) x =
      ρ • PDE.classicalGradient f (v + ρ • x) := by
    have ha : HasFDerivAt (fun y : PDE.Vec d => v + ρ • y)
        (ρ • ContinuousLinearMap.id ℝ (PDE.Vec d)) x := by
      simpa only [Pi.smul_def, id_eq] using! ((hasFDerivAt_id x).const_smul ρ).const_add v
    have hc := hf.hasFDerivAt.comp x ha
    ext i
    simp only [PDE.classicalGradient, Pi.smul_apply, smul_eq_mul]
    simp only [Function.comp_def] at hc
    rw [hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  exact gradient_affine_aux (fun y => u (b + ρ ^ 2 * z.1, y)) ρ z.2 hu

/-- `C^{1,2}` regularity and the derivative identities for `V ∘ reflectScale`. -/
theorem isScalarC12On_reflectScale {V : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)}
    (hD : IsOpen D) (hV : IsScalarC12On V D) {R : ℝ} (hR : 0 < R) (vStar : PDE.Vec d) :
    IsScalarC12On (fun z => V (reflectScale R vStar z)) (reflectScale R vStar ⁻¹' D) ∧
    ∀ z ∈ reflectScale R vStar ⁻¹' D,
      scalarTimeDerivative (fun w => V (reflectScale R vStar w)) z =
        -R ^ 2 * scalarTimeDerivative V (reflectScale R vStar z) ∧
      scalarSpatialGradient (fun w => V (reflectScale R vStar w)) z =
        R • scalarSpatialGradient V (reflectScale R vStar z) ∧
      scalarSpatialHessian (fun w => V (reflectScale R vStar w)) z =
        R ^ 2 • scalarSpatialHessian V (reflectScale R vStar z)  := by
  have isScalarC12On_timeReflectedScalar :
      IsScalarC12On (timeReflectedScalar V) (timeReflection ⁻¹' D) := by
    have hm : MapsTo (timeReflection (d := d)) (timeReflection ⁻¹' D) D := fun _ hz => hz
    have hc : ContinuousOn (timeReflection (d := d)) (timeReflection ⁻¹' D) :=
      continuous_timeReflection.continuousOn
    refine ⟨hV.continuousOn.comp hc hm, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      have h1 := hV.timeSlice_differentiableAt (z := timeReflection z) hz
      have h2 : DifferentiableAt ℝ (fun r : ℝ => 1 - r) z.1 := by fun_prop
      have h3 : DifferentiableAt ℝ (fun r : ℝ => V (r, z.2)) (1 - z.1) := h1
      exact h3.comp z.1 h2
    · intro z hz
      exact hV.spatialSlice_contDiffAt (z := timeReflection z) hz
    · refine ((hV.continuousOn_scalarTimeDerivative.comp hc hm).neg).congr ?_
      intro z _
      exact scalarTimeDerivative_timeReflectedScalar V z
    · exact hV.continuousOn_scalarSpatialGradient.comp hc hm
    · exact hV.continuousOn_scalarSpatialHessian.comp hc hm
  have hD' : IsOpen (timeReflection ⁻¹' D : Set (TimeVelocity d)) :=
    hD.preimage continuous_timeReflection
  have hV' := isScalarC12On_timeReflectedScalar
  have hfun : (fun z => V (reflectScale R vStar z)) =
      timeReflectedScalar V ∘ parabolicAffine 0 vStar R := by
    funext z
    simp only [Function.comp_apply, timeReflectedScalar_apply]
    exact congrArg V (congrFun (reflectScale_eq R vStar) z)
  have hpre : parabolicAffine 0 vStar R ⁻¹' (timeReflection ⁻¹' D) =
      reflectScale R vStar ⁻¹' D := by
    rw [reflectScale_eq, Set.preimage_comp]
  obtain ⟨hC, hform⟩ := KrylovEstimate.scalarC12On_affine_pullback hD'
    (timeReflectedScalar V) hV' 0 vStar hR
  rw [hpre] at hC hform
  rw [hfun]
  refine ⟨hC, ?_⟩
  intro z hz
  have hz' : z ∈ parabolicAffine 0 vStar R ⁻¹' (timeReflection ⁻¹' D) := by
    rw [hpre]; exact hz
  have hΦ : reflectScale R vStar z = timeReflection (parabolicAffine 0 vStar R z) :=
    congrFun (reflectScale_eq R vStar) z
  obtain ⟨ht, hh⟩ := hform z hz
  refine ⟨?_, ?_, ?_⟩
  · rw [ht, scalarTimeDerivative_timeReflectedScalar, hΦ]
    ring
  · have hslice := (hV'.spatialSlice_contDiffAt hz').differentiableAt (by norm_num)
    rw [scalarSpatialGradient_parabolicAffine _ 0 vStar R z hslice,
      scalarSpatialGradient_timeReflectedScalar, hΦ]
  · rw [hh, scalarSpatialHessian_timeReflectedScalar, hΦ]

/-- The scaled backward operator: `u_t - a : D² u = -R² (V_r + B : D² V)` at `reflectScale`. -/
theorem scaled_operator_eq {V : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)}
    (hD : IsOpen D) (hV : IsScalarC12On V D) {R : ℝ} (hR : 0 < R) (vStar : PDE.Vec d)
    (B : CoefficientField d) {z : TimeVelocity d} (hz : z ∈ reflectScale R vStar ⁻¹' D) :
    scalarTimeDerivative (fun w => V (reflectScale R vStar w)) z -
        matrixContraction (coefficientAt B (reflectScale R vStar z))
          (scalarSpatialHessian (fun w => V (reflectScale R vStar w)) z) =
      -R ^ 2 * (scalarTimeDerivative V (reflectScale R vStar z) +
        matrixContraction (coefficientAt B (reflectScale R vStar z))
          (scalarSpatialHessian V (reflectScale R vStar z))) := by
  obtain ⟨-, hform⟩ := isScalarC12On_reflectScale hD hV hR vStar
  obtain ⟨h1, -, h3⟩ := hform z hz
  rw [h1, h3, HypoellipticAleksandrov.matrixContraction_smul_right]
  ring



variable {d : ℕ}

/-- The scaled height `h = (1 - α) / R²` of the reflected cylinder. -/
def localHeight (α R : ℝ) : ℝ := (1 - α) / R ^ 2

theorem localHeight_pos {α R : ℝ} (hα : α < 1) (hR : 0 < R) : 0 < localHeight α R :=
  div_pos (sub_pos.mpr hα) (pow_pos hR 2)

theorem localHeight_le_one {α R : ℝ} (hα : 0 ≤ α) (hR : 1 ≤ R) : localHeight α R ≤ 1 := by
  unfold localHeight
  rw [div_le_one (by positivity)]
  nlinarith

theorem mul_localHeight {α R : ℝ} (hR : 0 < R) : R ^ 2 * localHeight α R = 1 - α := by
  unfold localHeight
  field_simp

/-- A closed Euclidean ball lies in the closure of the open ball of the same radius. -/
theorem euclideanClosedBall_subset_closure_euclideanBall {x : PDE.Vec d} {R : ℝ}
    (hR : 0 < R) : PDE.euclideanClosedBall x R ⊆ closure (PDE.euclideanBall x R) := by
  intro y hy
  have hpath : Tendsto (fun t : ℝ => t • (y - x) + x) (𝓝[<] 1) (𝓝 y) := by
    have h1 : Tendsto (fun t : ℝ => t • (y - x) + x) (𝓝 1) (𝓝 ((1 : ℝ) • (y - x) + x)) :=
      ((continuous_id.smul continuous_const).add continuous_const).tendsto 1
    simpa using h1.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hpath ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  change PDE.euclideanSqDist (t • (y - x) + x) x < R ^ 2
  rw [PDE.euclideanSqDist_affine_center]
  have hy' : PDE.euclideanSqDist y x ≤ R ^ 2 := hy
  have hs : PDE.euclideanSqDist (y - x) 0 = PDE.euclideanSqDist y x := by
    simp [PDE.euclideanSqDist]
  rw [hs]
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  have ht2 : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
  have hnn : 0 ≤ PDE.euclideanSqDist y x := PDE.vecNormSq_nonneg _
  nlinarith [sq_nonneg t]

/-- The open Euclidean ball is bounded. -/
theorem isBounded_euclideanBall (x : PDE.Vec d) {R : ℝ} (hR : 0 < R) :
    Bornology.IsBounded (PDE.euclideanBall x R) :=
  (Metric.isBounded_ball (x := x) (r := R)).subset (PDE.euclideanBall_subset_supBall hR)

section Cylinders

variable {α R : ℝ} {vStar : PDE.Vec d}


/-- The closed-ball part of the same correspondence. -/
theorem vStar_add_smul_mem_closedBall_iff (hR : 0 < R) (y : PDE.Vec d) :
    vStar + R • y ∈ PDE.euclideanClosedBall vStar R ↔
      y ∈ PDE.euclideanClosedBall (0 : PDE.Vec d) 1 := by
  rw [add_comm]
  exact PDE.affine_mem_euclideanClosedBall_iff_of_pos vStar y hR

/-- The Krylov cylinder is exactly the preimage of the source cylinder. -/
theorem mem_krylovCylinder_iff_reflectScale (hR : 0 < R) (z : TimeVelocity d) :
    z ∈ krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d) ↔
      reflectScale R vStar z ∈ scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)  := by
  have vStar_add_smul_mem_ball_iff (y : PDE.Vec d) :
      vStar + R • y ∈ PDE.euclideanBall vStar R ↔ y ∈ PDE.euclideanBall (0 : PDE.Vec d) 1 := by
    rw [add_comm]
    exact PDE.affine_mem_euclideanBall_iff_of_pos vStar y hR
  rcases z with ⟨t, y⟩
  rw [mem_krylovCylinder_iff]
  change _ ↔ (1 - R ^ 2 * t, vStar + R • y) ∈
    scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)
  rw [mem_scalarParabolicOpenCylinder_iff, vStar_add_smul_mem_ball_iff,
    sub_self]
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  have hh : R ^ 2 * localHeight α R = 1 - α := mul_localHeight hR
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, h2⟩ <;> nlinarith
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, h2⟩
    · by_contra hcon
      nlinarith
    · by_contra hcon
      nlinarith

/-- The closed Krylov cylinder maps into the closed source cylinder. -/
theorem krylovClosedCylinder_subset_preimage (hR : 0 < R) :
    krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d) ⊆
      reflectScale R vStar ⁻¹'
        scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R) := by
  rintro ⟨t, y⟩ ⟨⟨h0, h1⟩, hy⟩
  rw [sub_self] at h0
  change (1 - R ^ 2 * t, vStar + R • y) ∈
    scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R)
  rw [mem_scalarParabolicClosedCylinder_iff]
  have hh : R ^ 2 * localHeight α R = 1 - α := mul_localHeight hR
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  exact euclideanClosedBall_subset_closure_euclideanBall hR
    ((vStar_add_smul_mem_closedBall_iff hR y).mpr hy)

/-- The bottom and lateral Krylov faces map to the terminal and lateral faces. -/
theorem krylovParabolicBoundary_subset_preimage (hR : 0 < R) :
    krylovParabolicBoundary (localHeight α R) (localHeight α R) (0 : PDE.Vec d) ⊆
      reflectScale R vStar ⁻¹'
        (scalarParabolicTerminalFace 1 (PDE.euclideanBall vStar R) ∪
          scalarParabolicLateralFace α 1 (PDE.euclideanBall vStar R)) := by
  have hh : R ^ 2 * localHeight α R = 1 - α := mul_localHeight hR
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  rintro ⟨t, y⟩ hz
  change (1 - R ^ 2 * t, vStar + R • y) ∈
    scalarParabolicTerminalFace 1 (PDE.euclideanBall vStar R) ∪
      scalarParabolicLateralFace α 1 (PDE.euclideanBall vStar R)
  rcases hz with ⟨ht, hy⟩ | ⟨ht, hy⟩
  · have ht' : t = localHeight α R - localHeight α R := ht
    rw [sub_self] at ht'
    left
    rw [mem_scalarParabolicTerminalFace_iff]
    refine ⟨by rw [ht']; ring, ?_⟩
    exact euclideanClosedBall_subset_closure_euclideanBall hR
      ((vStar_add_smul_mem_closedBall_iff hR y).mpr hy)
  · obtain ⟨h0, h1⟩ := ht
    rw [sub_self] at h0
    right
    rw [mem_scalarParabolicLateralFace_iff]
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    rw [(PDE.isOpen_euclideanBall vStar R).frontier_eq]
    have hsph : vStar + R • y ∈ PDE.euclideanSphere vStar R := by
      change PDE.euclideanSqDist (vStar + R • y) vStar = R ^ 2
      rw [add_comm, PDE.euclideanSqDist_affine_center]
      have : PDE.euclideanSqDist y 0 = 1 ^ 2 := hy
      rw [this]
      ring
    refine ⟨euclideanClosedBall_subset_closure_euclideanBall hR (le_of_eq hsph), ?_⟩
    intro hlt
    have h1 : PDE.euclideanSqDist (vStar + R • y) vStar < R ^ 2 := hlt
    have h2 : PDE.euclideanSqDist (vStar + R • y) vStar = R ^ 2 := hsph
    exact lt_irrefl _ (h2 ▸ h1)

/-- The inverse of `reflectScale` on points of the source cylinder. -/
def reflectScaleInv (R : ℝ) (vStar : PDE.Vec d) (w : TimeVelocity d) : TimeVelocity d :=
  ((1 - w.1) / R ^ 2, R⁻¹ • (w.2 - vStar))


/-- A point of the source cylinder is the image of a point of the Krylov cylinder. -/
theorem exists_mem_krylovCylinder (hR : 0 < R) {w : TimeVelocity d}
    (hw : w ∈ scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) :
    ∃ z ∈ krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
      reflectScale R vStar z = w  := by
  have reflectScale_reflectScaleInv (w : TimeVelocity d) :
      reflectScale R vStar (reflectScaleInv R vStar w) = w := by
    rcases w with ⟨r, y⟩
    apply Prod.ext
    · change 1 - R ^ 2 * ((1 - r) / R ^ 2) = r
      field_simp
      ring
    · ext i
      change vStar i + R * (R⁻¹ * (y i - vStar i)) = y i
      field_simp
      ring
  refine ⟨reflectScaleInv R vStar w, ?_, reflectScale_reflectScaleInv w⟩
  rw [mem_krylovCylinder_iff_reflectScale hR (vStar := vStar) (α := α),
    reflectScale_reflectScaleInv]
  exact hw


/-- The image of the Krylov cylinder under the forward parabolic affine map. -/
theorem parabolicAffine_image_krylovCylinder (hR : 0 < R) :
    parabolicAffine 0 vStar R ''
        krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d) =
      timeReflection ⁻¹' scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)  := by
  have parabolicAffine_surjective {t₀ : ℝ} :
      Function.Surjective (parabolicAffine t₀ vStar R) := by
    rintro ⟨s, y⟩
    refine ⟨((s - t₀) / R ^ 2, R⁻¹ • (y - vStar)), ?_⟩
    apply Prod.ext
    · change t₀ + R ^ 2 * ((s - t₀) / R ^ 2) = s
      field_simp
      ring
    · ext i
      change vStar i + R * (R⁻¹ * (y i - vStar i)) = y i
      field_simp
      ring
  have hpre : krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d) =
      parabolicAffine 0 vStar R ⁻¹'
        (timeReflection ⁻¹' scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) := by
    ext z
    rw [mem_krylovCylinder_iff_reflectScale hR (vStar := vStar) (α := α), reflectScale_eq]
    rfl
  rw [hpre]
  exact Set.image_preimage_eq _ (parabolicAffine_surjective)

end Cylinders

section Norms

variable {α R : ℝ} {vStar : PDE.Vec d}

/-- Reflection of a measurable set preserves the restricted `L^{d+1}` extended norm. -/
theorem parabolicELpNormOn_timeReflectedScalar_preimage {F : TimeVelocity d → ℝ}
    (hF : Continuous F) {S : Set (TimeVelocity d)} (hS : MeasurableSet S) :
    parabolicELpNormOn d (timeReflectedScalar F) (timeReflection ⁻¹' S) =
      parabolicELpNormOn d F S := by
  unfold parabolicELpNormOn timeReflectedScalar
  exact eLpNorm_comp_measurePreserving hF.aestronglyMeasurable
    (timeReflection_measurePreserving.restrict_preimage hS)

/-- The source cylinder is measurable. -/
theorem measurableSet_sourceCylinder (α R : ℝ) (vStar : PDE.Vec d) :
    MeasurableSet (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) :=
  measurableSet_Ioo.prod (PDE.measurableSet_euclideanBall vStar R)

/-- The localized source `f(t, y) = R² F(1 - R² t, v_* + R y)`. -/
def localizedSource (R : ℝ) (vStar : PDE.Vec d) (F : TimeVelocity d → ℝ) :
    TimeVelocity d → ℝ :=
  fun z => R ^ 2 * F (reflectScale R vStar z)

theorem localizedSource_eq (R : ℝ) (vStar : PDE.Vec d) (F : TimeVelocity d → ℝ) :
    localizedSource R vStar F =
      fun z => R ^ 2 * timeReflectedScalar F (parabolicAffine 0 vStar R z) := by
  funext z
  unfold localizedSource
  rw [reflectScale_eq]
  rfl


/-- The real `L^{d+1}` norm of the localized source: Jacobian factor `R^(d/(d+1))`. -/
theorem parabolicLpNormOn_localizedSource (hR : 0 < R) {F : TimeVelocity d → ℝ}
    (hF : Continuous F) :
    parabolicLpNormOn d (localizedSource R vStar F)
        (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) =
      R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
        parabolicLpNormOn d F (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) := by
  rw [localizedSource_eq, parabolicLpNormOn_pullback 0 vStar hR,
    parabolicAffine_image_krylovCylinder hR]
  unfold parabolicLpNormOn
  rw [parabolicELpNormOn_timeReflectedScalar_preimage hF (measurableSet_sourceCylinder α R vStar)]

/-- The localized source is in `L^{d+1}` of the Krylov cylinder when `F` is in `L^{d+1}`. -/
theorem memLp_localizedSource (hR : 0 < R) {F : TimeVelocity d → ℝ}
    (hF : Continuous F) (hFp : MemLp F (parabolicExponent d) volume) :
    MemLp (localizedSource R vStar F) (parabolicExponent d)
      (volume.restrict
        (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)))  := by
  have parabolicELpNormOn_localizedSource :
      parabolicELpNormOn d (localizedSource R vStar F)
        (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) =
      ‖R ^ 2‖ₑ * (ENNReal.ofReal ((R ^ (d + 2))⁻¹) ^ (1 / parabolicExponent d).toReal) *
        parabolicELpNormOn d F (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) := by
    rw [localizedSource_eq, parabolicELpNormOn_pullback_raw 0 vStar hR,
      parabolicAffine_image_krylovCylinder hR,
      parabolicELpNormOn_timeReflectedScalar_preimage hF (measurableSet_sourceCylinder α R vStar)]
  change parabolicELpNormOn d (localizedSource R vStar F) _ < ⊤
  rw [parabolicELpNormOn_localizedSource]
  have hfin : parabolicELpNormOn d F
      (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) < ⊤ := by
    refine lt_of_le_of_lt ?_ hFp
    exact eLpNorm_mono_measure F Measure.restrict_le_self
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) hfin
  · exact ENNReal.coe_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top

end Norms

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

