module

public import GS.Topology.BrouwerBall
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

@[expose] public section



/-!
# Sphere noncontractibility from the fixed point property of a closed ball

The radial map from the compact cylinder `[0,1] × sphere` to the closed ball
is a quotient map. A contraction of the sphere is constant on its fibres,
so it descends to a continuous retraction. The antipodal map composed with
that retraction has no fixed point.
-/

noncomputable section


namespace GS.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def sphereConeMap : C(unitInterval × Metric.sphere (0 : E) 1, Metric.closedBall (0 : E) 1) where
  toFun p := ⟨(p.1 : ℝ) • (p.2 : E), by simpa [norm_smul, abs_of_nonneg p.1.2.1] using p.1.2.2⟩
  continuous_toFun := by fun_prop

theorem sphere_id_not_nullhomotopic : ¬ (ContinuousMap.id (Metric.sphere (0 : E) 1)).Nullhomotopic := by
  rintro ⟨u, ⟨h⟩⟩
  have hq : Topology.IsQuotientMap (sphereConeMap (E := E)) :=
    sphereConeMap.continuous.isClosedMap.isQuotientMap sphereConeMap.continuous fun x => by
      by_cases hx : (x : E) = 0
      · exact ⟨(0, u), Subtype.ext (by simp [sphereConeMap, hx])⟩
      · exact ⟨(⟨‖(x : E)‖, norm_nonneg _, mem_closedBall_zero_iff.1 x.2⟩, ⟨‖(x : E)‖⁻¹ • (x : E), by simp [norm_smul, hx]⟩),
          Subtype.ext (by simp [sphereConeMap, smul_smul, hx])⟩
  have hf : Function.FactorsThrough h.symm.toContinuousMap sphereConeMap := fun a b hab => by
    have hn := congrArg (fun z : Metric.closedBall (0 : E) 1 => ‖(z : E)‖) hab
    have he := congrArg Subtype.val hab
    simp [sphereConeMap, norm_smul, abs_of_nonneg a.1.2.1, abs_of_nonneg b.1.2.1] at hn he
    by_cases hz : (a.1 : ℝ) = 0
    · aesop
    aesop
  obtain ⟨x, hx⟩ := closedBall_fixedPoint (fun y => ⟨-(hq.lift _ hf y : E), by simp⟩) (by fun_prop)
  have hxe : -(hq.lift _ hf x : E) = x := congrArg Subtype.val hx
  let v : Metric.sphere (0 : E) 1 := ⟨x, by simp [← hxe]⟩
  have h1 := congrArg Subtype.val (ContinuousMap.congr_fun (hq.lift_comp _ hf) (1, v))
  simp only [ContinuousMap.comp_apply] at h1
  rw [show sphereConeMap (1, v) = x from Subtype.ext (by simp [sphereConeMap, v])] at h1
  have hn := mem_sphere_zero_iff_norm.1 (hq.lift _ hf x).2
  rw [h1] at hxe hn
  simp [v] at hxe hn
  rw [neg_eq_iff_add_eq_zero, ← two_smul ℝ] at hxe
  simp_all

end GS.Topology
