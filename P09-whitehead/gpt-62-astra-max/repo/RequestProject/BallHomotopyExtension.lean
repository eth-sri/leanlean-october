module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Tactic

@[expose] public section

/-! An explicit homotopy extension for the boundary of a closed unit ball.
Projection away from `(2, 0)` retracts the cylinder onto its bottom and sides.
No homotopy extension hypothesis is assumed. -/

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

variable (z : I × ClosedUnitBall E)

def cylinderDenominator :=
  max (2 - (z.1 : ℝ)) (2 * ‖z.2.val‖)

theorem cylinderDenominator_pos :
    0 < cylinderDenominator z := by
  have h := z.1.2.2
  have hle : 2 - (z.1) ≤ cylinderDenominator z := le_max_left _ _
  linarith

theorem cylinderDenominator_le_two :
    cylinderDenominator z ≤ 2 := by
  apply max_le <;> grind

def cylinderScale :=
  2 / cylinderDenominator z

theorem cylinderScale_nonneg :
    0 ≤ cylinderScale z :=
  div_nonneg (by norm_num) (cylinderDenominator_pos z).le

theorem cylinderScale_mul_denominator :
    cylinderScale z * cylinderDenominator z = 2 :=
  div_mul_cancel₀ _ (ne_of_gt (cylinderDenominator_pos z))

theorem cylinderScale_one_le :
    1 ≤ cylinderScale z := by
  apply (le_div_iff₀ (cylinderDenominator_pos z)).mpr
  simpa only [one_mul] using cylinderDenominator_le_two z

theorem cylinderScale_continuous :
    Continuous (cylinderScale : I × ClosedUnitBall E → ℝ) := by
  apply continuous_const.div
  · unfold cylinderDenominator
    fun_prop
  · grind [cylinderDenominator_pos]

def cylinderTime (z : I × ClosedUnitBall E) : I :=
  ⟨2 - cylinderScale z * (2 - (z.1)), by
    have hscale := cylinderScale_nonneg z
    have hmul := cylinderScale_mul_denominator z
    have hden : 2 - (z.1) ≤ cylinderDenominator z := le_max_left _ _
    have hbound := mul_le_mul_of_nonneg_left hden hscale
    constructor
    · linarith
    · have hone := cylinderScale_one_le z
      have ht : 1 ≤ 2 - (z.1 : ℝ) := by linarith [z.1.2.2]
      have hlower := mul_le_mul_of_nonneg_left ht hscale
      linarith⟩

theorem cylinderTime_continuous :
    Continuous (cylinderTime : I × ClosedUnitBall E → I) :=
  (continuous_const.sub (cylinderScale_continuous.mul
    (continuous_const.sub continuous_fst.subtype_val))).subtype_mk _

variable [NormedSpace ℝ E]

def cylinderPoint (z : I × ClosedUnitBall E) : ClosedUnitBall E :=
  ⟨cylinderScale z • z.2.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cylinderScale_nonneg z)]
    have hden : 2 * ‖z.2.val‖ ≤ cylinderDenominator z := le_max_right _ _
    have hm := mul_le_mul_of_nonneg_left hden (cylinderScale_nonneg z)
    have he := cylinderScale_mul_denominator z
    nlinarith⟩

theorem cylinderPoint_continuous :
    Continuous (cylinderPoint : I × ClosedUnitBall E → ClosedUnitBall E) :=
  (cylinderScale_continuous.smul continuous_snd.subtype_val).subtype_mk _

theorem cylinderTime_or_point_boundary (z : I × ClosedUnitBall E) :
    cylinderTime z = 0 ∨ ‖(cylinderPoint z).val‖ = 1 := by
  by_cases h : 2 * ‖z.2.val‖ ≤ 2 - (z.1)
  · left
    apply Subtype.ext
    have he := cylinderScale_mul_denominator z
    rw [cylinderDenominator, max_eq_left h] at he
    change 2 - cylinderScale z * (2 - (z.1)) = 0
    linarith
  · right
    have he := cylinderScale_mul_denominator z
    rw [cylinderDenominator, max_eq_right (le_of_not_ge h)] at he
    change ‖cylinderScale z • z.2.val‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cylinderScale_nonneg z)]
    nlinarith

/-- The actual cylinder retraction, valid for every real normed vector space. -/
def ballCylinderRetraction : C(I × ClosedUnitBall E, BallCylinderBoundary E) :=
  ⟨fun z => ⟨(cylinderTime z, cylinderPoint z), cylinderTime_or_point_boundary z⟩,
    (cylinderTime_continuous.prodMk cylinderPoint_continuous).subtype_mk _⟩

omit [NormedSpace ℝ E] in
theorem cylinderScale_eq_one (z : I × ClosedUnitBall E)
    (hz : z.1 = 0 ∨ ‖z.2.val‖ = 1) : cylinderScale z = 1 := by
  have hden : cylinderDenominator z = 2 := by
    apply le_antisymm (cylinderDenominator_le_two z)
    rcases hz with ht | hx
    · have h : 2 - (z.1) ≤ cylinderDenominator z := le_max_left _ _
      simp_all
    · have h : 2 * ‖z.2.val‖ ≤ cylinderDenominator z := le_max_right _ _
      simp_all
  simp [cylinderScale, hden, div_self]

theorem ballCylinderRetraction_fixed (z : BallCylinderBoundary E) :
    ballCylinderRetraction z.val = z := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change 2 - cylinderScale z.val * (2 - (z.val.1)) = (z.val.1)
    rw [cylinderScale_eq_one z.val z.property]
    ring
  · apply Subtype.ext
    change cylinderScale z.val • z.val.2.val = z.val.2.val
    rw [cylinderScale_eq_one z.val z.property, one_smul]

variable {Z : Type v} [TopologicalSpace Z]

variable (f : C(ClosedUnitBall E, Z)) (H : C(I × UnitBoundary E, Z))

variable (z : BallCylinderBoundary E)

def ballBoundaryPastingFun :=
  if ht : z.val.1 = 0 then f z.val.2
  else H (z.val.1, ⟨z.val.2.val, z.property.resolve_left ht⟩)

omit [NormedSpace ℝ E] in
theorem ballBoundaryPastingFun_bottom (hz : z.val.1 = 0) :
    ballBoundaryPastingFun f H z = f z.val.2 := by
  simp_all [ballBoundaryPastingFun, dite_eq_left]

variable (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x))
include h₀

omit [NormedSpace ℝ E] in
theorem ballBoundaryPastingFun_side
    (z : BallCylinderBoundary E) (hz : ‖z.val.2.val‖ = 1) :
    ballBoundaryPastingFun f H z = H (z.val.1, ⟨z.val.2.val, hz⟩) := by
  by_cases ht : z.val.1 = 0
  · rw [ballBoundaryPastingFun_bottom f H z ht, ht, h₀]
    rfl
  · simp_all [ballBoundaryPastingFun, dite_eq_right]

/-- The supplied disk map and its boundary homotopy paste continuously on
the closed bottom and side of the cylinder. -/
def ballBoundaryPasting :
    C(BallCylinderBoundary E, Z) where
  toFun := ballBoundaryPastingFun f H
  continuous_toFun := by
    let B : Set (BallCylinderBoundary E) := {z | z.val.1 = 0}
    let S : Set (BallCylinderBoundary E) := {z | ‖z.val.2.val‖ = 1}
    have hB : IsClosed B := isClosed_eq (by fun_prop) continuous_const
    have hS : IsClosed S := isClosed_eq (by fun_prop) continuous_const
    have hcover : B ∪ S = Set.univ := by
      apply Set.eq_univ_of_forall
      grind
    have hf : ContinuousOn (ballBoundaryPastingFun f H) B := by
      apply ((f.continuous.comp (continuous_snd.comp continuous_subtype_val)).continuousOn).congr
      apply ballBoundaryPastingFun_bottom
    have hh : ContinuousOn (ballBoundaryPastingFun f H) S := by
      rw [continuousOn_iff_continuous_domRestrict]
      let k : C(S, I × UnitBoundary E) := {
        toFun := fun z => (z.val.val.1, ⟨z.val.val.2.val, z.property⟩)
        continuous_toFun := by fun_prop }
      have he : S.domRestrict (ballBoundaryPastingFun f H) = H ∘ k := by
        funext z
        apply ballBoundaryPastingFun_side <;> assumption
      rw [he]
      exact H.continuous.comp k.continuous
    rw [← continuousOn_univ, ← hcover]
    apply hf.union_of_isClosed <;> assumption

/-- Explicit homotopy extension across a closed disk. -/
def ballHomotopyExtension :=
  (ballBoundaryPasting f H h₀).comp ballCylinderRetraction

@[simp] theorem ballHomotopyExtension_zero (x : ClosedUnitBall E) :
    ballHomotopyExtension f H h₀ (0, x) = f x := by
  change ballBoundaryPasting f H h₀ _ = f x
  rw [ballCylinderRetraction_fixed (⟨(0, x), Or.inl rfl⟩)]
  exact ballBoundaryPastingFun_bottom f H _ rfl

@[simp] theorem ballHomotopyExtension_boundary
    (t : I) (x : UnitBoundary E) :
    ballHomotopyExtension f H h₀ (t, unitBoundaryInclusion E x) = H (t, x) := by
  change ballBoundaryPasting f H h₀
    _ = H _
  rw [ballCylinderRetraction_fixed
    (⟨(t, unitBoundaryInclusion E x), Or.inr x.property⟩)]
  exact ballBoundaryPastingFun_side f H h₀ _ x.property

end FiniteChains.RelativeAttachment
