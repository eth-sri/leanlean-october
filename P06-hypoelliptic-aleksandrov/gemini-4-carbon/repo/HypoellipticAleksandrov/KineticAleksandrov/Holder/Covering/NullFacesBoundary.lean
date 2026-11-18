module

public import HypoellipticAleksandrov.KineticAleksandrov.Geometry
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Mathlib.MeasureTheory.Measure.Prod
public import PDEFoundation.Ambient.HilbertVec
public import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Inflation

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
open Set MeasureTheory


/-- A complete kinetic time slice has zero Lebesgue measure. -/
theorem volume_time_face {d : ℕ} (t : ℝ) :
    volume {P : KineticPoint d | P.time = t} = 0 := by
  have hset : {P : KineticPoint d | P.time = t} =
      (KineticPoint.equivProd d) ⁻¹'
        ({t} ×ˢ (univ : Set (PDE.Vec d × PDE.Vec d))) := by
    ext P
    simp
    rfl
  rw [hset, (KineticPoint.measurePreserving_equivProd d).measure_preimage
    ((measurableSet_singleton t).prod MeasurableSet.univ).nullMeasurableSet]
  change (volume : Measure ℝ).prod volume ({t} ×ˢ univ) = 0
  rw [Measure.prod_prod]
  simp




/-- Positive-radius native Euclidean spheres have zero ordinary Lebesgue volume. -/
theorem volume_euclideanSphere {d : ℕ} (x : PDE.Vec d) {r : ℝ} (hr : 0 < r) :
    volume (PDE.euclideanSphere x r) = 0  := by
  have euclideanSphere_eq_hilbert_preimage :
      PDE.euclideanSphere x r = PDE.Vec.toHilbertVec ⁻¹'
      Metric.sphere x.toHilbertVec r := by
    ext y
    change PDE.vecNormSq (y-x) = r ^ 2 ↔ dist y.toHilbertVec x.toHilbertVec = r
    rw [dist_eq_norm, ← WithLp.toLp_sub]
    change PDE.vecNormSq (y-x) = r ^ 2 ↔ ‖(y-x).toHilbertVec‖ = r
    rw [← PDE.Vec.vecEuclideanNorm_eq_norm_toHilbertVec, ← PDE.vecEuclideanNorm_sq]
    constructor
    · intro h
      nlinarith only [h, PDE.vecEuclideanNorm_nonneg (y-x), hr]
    · intro h
      rw [h]
  rw [euclideanSphere_eq_hilbert_preimage]
  change volume (WithLp.toLp 2 ⁻¹' Metric.sphere x.toHilbertVec r) = 0
  rw [(PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    (Metric.isClosed_sphere.measurableSet.nullMeasurableSet)]
  exact Measure.addHaar_sphere_of_ne_zero volume x.toHilbertVec hr.ne'

/-- A complete kinetic velocity-sphere face is null, without bounding time or position. -/
theorem volume_velocity_sphere_face {d : ℕ} (v : PDE.Vec d) {r : ℝ} (hr : 0 < r) :
    volume {P : KineticPoint d | P.velocity ∈ PDE.euclideanSphere v r} = 0 := by
  let s := (univ : Set ℝ) ×ˢ
    ((univ : Set (PDE.Vec d)) ×ˢ PDE.euclideanSphere v r)
  have hs : MeasurableSet s := MeasurableSet.univ.prod
    (MeasurableSet.univ.prod (PDE.isClosed_euclideanSphere v r).measurableSet)
  have heq : {P : KineticPoint d | P.velocity ∈ PDE.euclideanSphere v r} =
      (KineticPoint.equivProd d) ⁻¹' s := by
    ext P
    simp [s]
    rfl
  rw [heq, (KineticPoint.measurePreserving_equivProd d).measure_preimage hs.nullMeasurableSet]
  simp [s, Measure.volume_eq_prod, Measure.prod_prod, volume_euclideanSphere v hr]

/-- A free-transport position sphere becomes a translated sphere on each time slice. -/
theorem position_sphere_slice {d : ℕ} (P : KineticPoint d) (t R : ℝ) (x : PDE.Vec d) :
    x-P.position-(t-P.time) • P.velocity ∈ PDE.euclideanSphere 0 R ↔
      x ∈ PDE.euclideanSphere (P.position+(t-P.time) • P.velocity) R := by
  have heq : x-P.position-(t-P.time) • P.velocity =
      x-(P.position+(t-P.time) • P.velocity) := by abel
  change PDE.vecNormSq ((x-P.position-(t-P.time) • P.velocity)-0) = R ^ 2 ↔ _
  rw [sub_zero, heq]
  rfl

/-- A complete free-transport position-sphere face is null. -/
theorem volume_position_sphere_face {d : ℕ} (P : KineticPoint d) {R : ℝ} (hR : 0 < R) :
    volume {X : KineticPoint d | relativePosition P X ∈ PDE.euclideanSphere 0 R} = 0 := by
  let s := (KineticPoint.equivProd d).symm ⁻¹'
    {X : KineticPoint d | relativePosition P X ∈ PDE.euclideanSphere 0 R}
  have hx : Continuous (relativePosition P) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  have hs : MeasurableSet s := ((PDE.isClosed_euclideanSphere 0 R).preimage hx).measurableSet
    |>.preimage (KineticPoint.measurable_equivProd_symm d)
  have hpre : (KineticPoint.equivProd d) ⁻¹' s =
      {X : KineticPoint d | relativePosition P X ∈ PDE.euclideanSphere 0 R} := by
    ext X
    simp [s, Equiv.symm_apply_apply]
  have hv := (KineticPoint.measurePreserving_equivProd d).measure_preimage hs.nullMeasurableSet
  rw [hpre] at hv
  rw [hv, Measure.volume_eq_prod, Measure.prod_apply hs]
  have hslice (t : ℝ) : Prod.mk t ⁻¹' s =
      PDE.euclideanSphere (P.position+(t-P.time) • P.velocity) R ×ˢ
        (univ : Set (PDE.Vec d)) := by
    ext z
    simp
    exact position_sphere_slice P t R z.1
  simp_rw [hslice, Measure.volume_eq_prod, Measure.prod_prod,
    volume_euclideanSphere _ hR, zero_mul]
  exact lintegral_zero



/-- The closure of a kinetic cylinder satisfies all four weak coordinate inequalities. -/
theorem closure_cylinder_bounds {d : ℕ} (P : KineticPoint d) (r : ℝ) :
    closure (backwardCylinder P r) ⊆ {X | P.time-r^2 ≤ X.time ∧ X.time ≤ P.time ∧
      PDE.vecNormSq (X.velocity-P.velocity) ≤ r^2 ∧
      PDE.vecNormSq (relativePosition P X) ≤ (r^3)^2} := by
  have hx : Continuous (relativePosition P) :=
    (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  apply closure_minimal
  · intro X hX
    have hp : PDE.vecNormSq (relativePosition P X) < (r^3)^2 := by
      simpa [PDE.euclideanBall, PDE.euclideanSqDist]
        using hX.2.2.2
    exact ⟨hX.1.le, hX.2.1.le, hX.2.2.1.le, hp.le⟩
  · exact (isClosed_le continuous_const continuous_time).inter
      ((isClosed_le continuous_time continuous_const).inter
        ((isClosed_le (PDE.continuous_vecNormSq.comp
          (continuous_velocity.sub continuous_const)) continuous_const).inter
          (isClosed_le (PDE.continuous_vecNormSq.comp hx) continuous_const)))

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

