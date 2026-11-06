module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace FiniteChains.RelativeAttachment
open scoped unitInterval Topology Classical

universe u v
variable (E : Type u) [NormedAddCommGroup E]

abbrev ClosedUnitBall := {x : E // ‖x‖ ≤ 1}
abbrev UnitBoundary := {x : E // ‖x‖ = 1}

def unitBoundaryInclusion : C(UnitBoundary E, ClosedUnitBall E) :=
  ⟨fun x => ⟨x.val, x.property.le⟩, continuous_subtype_val.subtype_mk _⟩

abbrev BallCylinderBoundary :=
  {z : I × ClosedUnitBall E // z.1 = 0 ∨ ‖z.2.val‖ = 1}

variable {E}

def cylinderDenominator (z : I × ClosedUnitBall E) : ℝ :=
  max (2 - (z.1 : ℝ)) (2 * ‖z.2.val‖)

theorem cylinderDenominator_pos (z : I × ClosedUnitBall E) :
    0 < cylinderDenominator z := by
  have hle : 2 - (z.1 : ℝ) ≤ cylinderDenominator z := le_max_left _ _
  linarith [z.1.2.2]

theorem cylinderDenominator_le_two (z : I × ClosedUnitBall E) :
    cylinderDenominator z ≤ 2 :=
  max_le (by linarith [z.1.2.1]) (by linarith [z.2.2])

def cylinderScale (z : I × ClosedUnitBall E) : ℝ :=
  2 / cylinderDenominator z

theorem cylinderScale_nonneg (z : I × ClosedUnitBall E) :
    0 ≤ cylinderScale z :=
  div_nonneg (by norm_num) (cylinderDenominator_pos z).le

theorem cylinderScale_mul_denominator (z : I × ClosedUnitBall E) :
    cylinderScale z * cylinderDenominator z = 2 :=
  div_mul_cancel₀ _ (ne_of_gt (cylinderDenominator_pos z))

theorem cylinderScale_continuous :
    Continuous (cylinderScale : I × ClosedUnitBall E → ℝ) :=
  continuous_const.div (by unfold cylinderDenominator; fun_prop)
    fun z => ne_of_gt (cylinderDenominator_pos z)

def cylinderTime (z : I × ClosedUnitBall E) : I :=
  ⟨2 - cylinderScale z * (2 - (z.1 : ℝ)), by
    have hscale := cylinderScale_nonneg z
    have hmul := cylinderScale_mul_denominator z
    have hden : 2 - (z.1 : ℝ) ≤ cylinderDenominator z := le_max_left _ _
    have hbound := mul_le_mul_of_nonneg_left hden hscale
    refine ⟨by linarith, ?_⟩
    have hone : 1 ≤ cylinderScale z :=
      (le_div_iff₀ (cylinderDenominator_pos z)).mpr (by simpa only [one_mul] using cylinderDenominator_le_two z)
    have ht : 1 ≤ 2 - (z.1 : ℝ) := by linarith [z.1.2.2]
    linarith [mul_le_mul_of_nonneg_left ht hscale]⟩

theorem cylinderTime_continuous :
    Continuous (cylinderTime : I × ClosedUnitBall E → I) :=
  (continuous_const.sub (cylinderScale_continuous.mul
    (continuous_const.sub continuous_fst.subtype_val))).subtype_mk _

variable [NormedSpace ℝ E]

def cylinderPoint (z : I × ClosedUnitBall E) : ClosedUnitBall E :=
  ⟨cylinderScale z • z.2.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cylinderScale_nonneg z)]
    have hden : 2 * ‖z.2.val‖ ≤ cylinderDenominator z := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left hden (cylinderScale_nonneg z), cylinderScale_mul_denominator z]⟩

theorem cylinderPoint_continuous :
    Continuous (cylinderPoint : I × ClosedUnitBall E → ClosedUnitBall E) :=
  (cylinderScale_continuous.smul continuous_snd.subtype_val).subtype_mk _

theorem cylinderTime_or_point_boundary (z : I × ClosedUnitBall E) :
    cylinderTime z = 0 ∨ ‖(cylinderPoint z).val‖ = 1 := by
  by_cases h : 2 * ‖z.2.val‖ ≤ 2 - (z.1 : ℝ)
  · refine .inl (Subtype.ext ?_)
    have he := cylinderScale_mul_denominator z
    rw [cylinderDenominator, max_eq_left h] at he
    change 2 - cylinderScale z * (2 - (z.1 : ℝ)) = 0; linarith
  · refine .inr ?_
    have he := cylinderScale_mul_denominator z
    rw [cylinderDenominator, max_eq_right (le_of_not_ge h)] at he
    change ‖cylinderScale z • z.2.val‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cylinderScale_nonneg z)]; nlinarith

def ballCylinderRetraction : C(I × ClosedUnitBall E, BallCylinderBoundary E) :=
  ⟨fun z => ⟨(cylinderTime z, cylinderPoint z), cylinderTime_or_point_boundary z⟩,
    (cylinderTime_continuous.prodMk cylinderPoint_continuous).subtype_mk _⟩

theorem ballCylinderRetraction_fixed (z : BallCylinderBoundary E) :
    ballCylinderRetraction z.val = z := by
  have hs : cylinderScale z.val = 1 := by
    have hden : cylinderDenominator z.val = 2 := by
      refine le_antisymm (cylinderDenominator_le_two z.val) ?_
      rcases z.property with ht | hx
      · have h : 2 - (z.val.1 : ℝ) ≤ cylinderDenominator z.val := le_max_left _ _
        rw [ht] at h; change 2 - (0 : ℝ) ≤ cylinderDenominator z.val at h
        simpa only [sub_zero] using h
      · have h : 2 * ‖z.val.2.val‖ ≤ cylinderDenominator z.val := le_max_right _ _
        simpa only [hx, mul_one] using h
    simp [cylinderScale, hden]
  refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · change 2 - cylinderScale z.val * (2 - (z.val.1 : ℝ)) = (z.val.1 : ℝ)
    rw [hs]; ring
  · change cylinderScale z.val • z.val.2.val = z.val.2.val
    rw [hs, one_smul]

variable {Z : Type v} [TopologicalSpace Z]

def ballBoundaryPastingFun (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z)) (z : BallCylinderBoundary E) : Z :=
  if ht : z.val.1 = 0 then f z.val.2
  else H (z.val.1, ⟨z.val.2.val, z.property.resolve_left ht⟩)

omit [NormedSpace ℝ E] in
theorem ballBoundaryPastingFun_bottom (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z)) (z : BallCylinderBoundary E) (hz : z.val.1 = 0) :
    ballBoundaryPastingFun f H z = f z.val.2 := by
  simp only [ballBoundaryPastingFun]; rw [dite_eq_left hz]

omit [NormedSpace ℝ E] in
theorem ballBoundaryPastingFun_side (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z))
    (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x))
    (z : BallCylinderBoundary E) (hz : ‖z.val.2.val‖ = 1) :
    ballBoundaryPastingFun f H z = H (z.val.1, ⟨z.val.2.val, hz⟩) := by
  by_cases ht : z.val.1 = 0
  · rw [ballBoundaryPastingFun_bottom f H z ht, ht, h₀]; rfl
  · simp only [ballBoundaryPastingFun]; rw [dite_eq_right ht]

def ballHomotopyExtension (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z))
    (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x)) :
    C(I × ClosedUnitBall E, Z) :=
  (⟨ballBoundaryPastingFun f H, by
    let B : Set (BallCylinderBoundary E) := {z | z.val.1 = 0}
    let S : Set (BallCylinderBoundary E) := {z | ‖z.val.2.val‖ = 1}
    have hf : ContinuousOn (ballBoundaryPastingFun f H) B :=
      ((f.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn).congr
        fun z hz => ballBoundaryPastingFun_bottom f H z hz
    have hh : ContinuousOn (ballBoundaryPastingFun f H) S := by
      rw [continuousOn_iff_continuous_domRestrict]
      let k : C(S, I × UnitBoundary E) := ⟨fun z => (z.val.val.1, ⟨z.val.val.2.val, z.property⟩), by fun_prop⟩
      rw [show S.domRestrict (ballBoundaryPastingFun f H) = H ∘ k from
        funext fun z => ballBoundaryPastingFun_side f H h₀ z.val z.property]
      exact H.continuous.comp k.continuous
    rw [← continuousOn_univ, ← Set.eq_univ_of_forall fun z : BallCylinderBoundary E => z.property]
    exact hf.union_of_isClosed hh (isClosed_eq (by fun_prop) continuous_const)
      (isClosed_eq (by fun_prop) continuous_const)⟩ : C(BallCylinderBoundary E, Z)).comp
    ballCylinderRetraction

@[simp] theorem ballHomotopyExtension_zero (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z))
    (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x)) (x : ClosedUnitBall E) :
    ballHomotopyExtension f H h₀ (0, x) = f x := by
  change ballBoundaryPastingFun f H (ballCylinderRetraction (0, x)) = f x
  rw [ballCylinderRetraction_fixed (⟨(0, x), Or.inl rfl⟩ : BallCylinderBoundary E)]
  exact ballBoundaryPastingFun_bottom f H _ rfl

@[simp] theorem ballHomotopyExtension_boundary (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z))
    (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x))
    (t : I) (x : UnitBoundary E) :
    ballHomotopyExtension f H h₀ (t, unitBoundaryInclusion E x) = H (t, x) := by
  change ballBoundaryPastingFun f H
    (ballCylinderRetraction (t, unitBoundaryInclusion E x)) = H (t, x)
  rw [ballCylinderRetraction_fixed
    (⟨(t, unitBoundaryInclusion E x), Or.inr x.property⟩ : BallCylinderBoundary E)]
  exact ballBoundaryPastingFun_side f H h₀ _ x.property

end FiniteChains.RelativeAttachment
