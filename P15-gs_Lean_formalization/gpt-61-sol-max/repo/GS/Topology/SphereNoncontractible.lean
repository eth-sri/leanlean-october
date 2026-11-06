import Mathlib.Tactic

import Mathlib.Tactic.Module
import GS.Topology.BrouwerBall
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith



/-!
# Sphere noncontractibility from the fixed point property of a closed ball

The radial map from the compact cylinder `[0,1] × sphere` to the closed ball
is a quotient map. A contraction of the sphere is constant on its fibres,
so it descends to a continuous retraction. The antipodal map composed with
that retraction has no fixed point.
-/



namespace GS.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev UnitNormSphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1
abbrev UnitNormBall (E : Type*) [NormedAddCommGroup E] := Metric.closedBall (0 : E) 1

def sphereConeMap : C(unitInterval × UnitNormSphere E, UnitNormBall E) where
  toFun p := ⟨(p.1 : ℝ) • (p.2 : E), by aesop (add norm [abs_of_nonneg,norm_smul])⟩
  continuous_toFun := by fun_prop

@[simp] theorem sphereConeMap_norm (p : unitInterval × UnitNormSphere E) :
    ‖(sphereConeMap p : E)‖ = (p.1 : ℝ) := by aesop (add norm [sphereConeMap,norm_smul])

theorem sphereConeMap_surjective (u : UnitNormSphere E) :
    Function.Surjective (sphereConeMap (E := E)) := by
  intro x
  by_cases hx : (x : E) = 0
  · aesop (add norm [sphereConeMap])
  · have hn := norm_ne_zero_iff.mpr hx
    let t : unitInterval := ⟨‖(x : E)‖, norm_nonneg _, by aesop⟩
    let v : UnitNormSphere E := ⟨‖(x : E)‖⁻¹ • (x : E), by simp_all [inv_mul_cancel₀,norm_smul]⟩
    refine ⟨(t, v), ?_⟩
    apply Subtype.ext
    simp [sphereConeMap, t, v, smul_smul, mul_inv_cancel₀ hn]

theorem homotopy_factors_sphereConeMap (u : UnitNormSphere E)
    (h : ContinuousMap.Homotopy (ContinuousMap.const _ u)
      (ContinuousMap.id (UnitNormSphere E))) :
    Function.FactorsThrough h.toContinuousMap (sphereConeMap (E := E)) := by
  intro a b hab
  have ht : a.1 = b.1 := by grind [sphereConeMap_norm]
  by_cases hz : (a.1 : ℝ) = 0
  · aesop
  · aesop (add norm [sphereConeMap])

def sphereInclusion : C(UnitNormSphere E, UnitNormBall E) :=
  ContinuousMap.inclusion Metric.sphere_subset_closedBall

theorem exists_sphere_retraction_of_nullhomotopic [ProperSpace E]
    (hc : (ContinuousMap.id (UnitNormSphere E)).Nullhomotopic) :
    ∃ r : C(UnitNormBall E, UnitNormSphere E), r.comp sphereInclusion = ContinuousMap.id _ := by
  obtain ⟨u, ⟨h⟩⟩ := hc
  have hq :=
    sphereConeMap.continuous.isClosedMap.isQuotientMap
      sphereConeMap.continuous (sphereConeMap_surjective u)
  let r := hq.lift h.symm.toContinuousMap (homotopy_factors_sphereConeMap u h.symm)
  refine ⟨r, ?_⟩
  apply ContinuousMap.ext
  intro v
  have he := ContinuousMap.congr_fun
    (hq.lift_comp h.symm.toContinuousMap (homotopy_factors_sphereConeMap u h.symm)) (1, v)
  change r (sphereInclusion v) = v
  have hi : sphereConeMap (1, v) = sphereInclusion v := by
    apply Subtype.ext
    
    exact one_smul _ _
  rw [← hi]
  exact he.trans (h.symm.map_one_left v)

theorem sphere_id_not_nullhomotopic_of_fixedPoint [ProperSpace E]
    (hfp : ∀ f : C(UnitNormBall E, UnitNormBall E), ∃ x, f x = x) :
    ¬ (ContinuousMap.id (UnitNormSphere E)).Nullhomotopic := by
  intro hc
  obtain ⟨r, hr⟩ := exists_sphere_retraction_of_nullhomotopic hc
  let f : C(UnitNormBall E, UnitNormBall E) := {
    toFun := fun x => ⟨-(r x : E), by aesop⟩,
    continuous_toFun := by fun_prop }
  obtain ⟨x, hx⟩ := hfp f
  have hxe : -(r x : E) = (x : E) := congrArg Subtype.val hx
  have hxn : ‖(x : E)‖ = 1 := by
    rw [← hxe, norm_neg]
    simpa using (r x).property
  let v : UnitNormSphere E := ⟨x, by simpa using hxn⟩
  have hrx : (r x : E) = (x : E) := by
    have hh := congrArg Subtype.val (ContinuousMap.congr_fun hr v)
    simpa [sphereInclusion, v, ContinuousMap.inclusion, Set.inclusion] using hh
  have hzero : (x : E) = 0 := by
    linear_combination (norm := module) (-1/2 : ℝ) • hxe - (1/2 : ℝ) • hrx
  simpa [hzero] using hxn

end GS.Topology
