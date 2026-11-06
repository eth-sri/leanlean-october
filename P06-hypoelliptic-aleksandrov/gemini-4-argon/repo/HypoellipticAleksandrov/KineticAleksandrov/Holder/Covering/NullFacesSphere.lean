module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.NullFaces
public import PDEFoundation.Ambient.HilbertVec
public import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-! # Null Euclidean sphere faces in native kinetic coordinates

The internal Hilbert realization is used only through its proved Euclidean norm and
measure-preserving coordinate conversion.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/- A native Euclidean sphere is the coordinate preimage of the internal Hilbert sphere. -/
theorem volume_euclideanSphere {d } (x : PDE.Vec d) {r } (hr : 0 < r) :
    volume (PDE.euclideanSphere x r) = 0 := by
  have _h_inl_11 : PDE.euclideanSphere x r = PDE.Vec.toHilbertVec ⁻¹'
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

    /- Positive-radius native Euclidean spheres have zero ordinary Lebesgue volume. -/
  rw [_h_inl_11]
  change volume (WithLp.toLp 2 ⁻¹' Metric.sphere x.toHilbertVec r) = 0
  rw [(PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    (Metric.isClosed_sphere.measurableSet.nullMeasurableSet)]
  exact Measure.addHaar_sphere_of_ne_zero volume x.toHilbertVec hr.ne'

/- A complete kinetic velocity-sphere face is null, without bounding time or position. -/
theorem volume_velocity_sphere_face {d } (v : PDE.Vec d) {r } (hr : 0 < r) :
    volume {P : KineticPoint d | P.velocity ∈ PDE.euclideanSphere v r} = 0 := by
  let s := (univ : Set ℝ) ×ˢ
    ((univ : Set (PDE.Vec d)) ×ˢ PDE.euclideanSphere v r)
  have hs : MeasurableSet s := MeasurableSet.univ.prod
    (MeasurableSet.univ.prod (PDE.isClosed_euclideanSphere v r).measurableSet)
  have heq : {P : KineticPoint d | P.velocity ∈ PDE.euclideanSphere v r} =
      (KineticPoint.equivProd d) ⁻¹' s := by
    ext P
    simp only [s, mem_preimage, mem_prod, mem_univ, true_and]
    rfl
  rw [heq, (KineticPoint.measurePreserving_equivProd d).measure_preimage hs.nullMeasurableSet]
  simp only [s, Measure.volume_eq_prod, Measure.prod_prod, volume_euclideanSphere v hr,
    mul_zero]

/- A free-transport position sphere becomes a translated sphere on each time slice. -/
theorem volume_position_sphere_face {d } (P : KineticPoint d) {R } (hR : 0 < R) :
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
    simp only [s, mem_preimage, Equiv.symm_apply_apply]
  have hv := (KineticPoint.measurePreserving_equivProd d).measure_preimage hs.nullMeasurableSet
  rw [hpre] at hv
  rw [hv, Measure.volume_eq_prod, Measure.prod_apply hs]
  have hslice (t : ℝ) : Prod.mk t ⁻¹' s =
      PDE.euclideanSphere (P.position+(t-P.time) • P.velocity) R ×ˢ
        (univ : Set (PDE.Vec d)) := by
    ext z
    simp only [s, mem_preimage, KineticPoint.equivProd, Equiv.coe_fn_symm_mk,
      mem_ofPred_eq, relativePosition, mem_prod, mem_univ, and_true]
    let x := z.1
    have heq : x-P.position-(t-P.time) • P.velocity =
        x-(P.position+(t-P.time) • P.velocity) := by abel
    change PDE.vecNormSq ((x-P.position-(t-P.time) • P.velocity)-0) = R ^ 2 ↔ _
    rw [sub_zero, heq]
    rfl
  simp_rw [hslice, Measure.volume_eq_prod, Measure.prod_prod,
    volume_euclideanSphere _ hR, zero_mul]
  exact lintegral_zero

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
