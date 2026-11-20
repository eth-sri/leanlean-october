module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Homotopy.Basic
public import RequestProject.CylinderPasting
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
  CylinderSubspace ({0} : Set I) {x : ClosedUnitBall E | ‖x.val‖ = 1}

variable {E}

def cylinderDenominator (z : I × ClosedUnitBall E) : ℝ :=
  max (2 - (z.1)) (2 * ‖z.2.val‖)

theorem cylinderDenominator_pos (z : I × ClosedUnitBall E) :
    0 < cylinderDenominator z := by
  have h := z.1.2.2
  have hle : 2 - (z.1 : ℝ) ≤ cylinderDenominator z := le_max_left _ _
  linarith

theorem cylinderDenominator_le_two (z : I × ClosedUnitBall E) :
    cylinderDenominator z ≤ 2 := by
  apply max_le
  · grind
  · grind

def cylinderScale (z : I × ClosedUnitBall E) : ℝ :=
  2 / cylinderDenominator z

theorem cylinderScale_nonneg (z : I × ClosedUnitBall E) :
    0 ≤ cylinderScale z :=
  div_nonneg (by norm_num) (cylinderDenominator_pos z).le

theorem cylinderScale_mul_denominator (z : I × ClosedUnitBall E) :
    cylinderScale z * cylinderDenominator z = 2 :=
  div_mul_cancel₀ _ (ne_of_gt (cylinderDenominator_pos z))

theorem cylinderScale_one_le (z : I × ClosedUnitBall E) :
    1 ≤ cylinderScale z := by
  apply (le_div_iff₀ (cylinderDenominator_pos z)).mpr
  simpa only [one_mul] using cylinderDenominator_le_two z

theorem cylinderScale_continuous :
    Continuous (cylinderScale : I × ClosedUnitBall E → ℝ) := by
  apply continuous_const.div
  · unfold cylinderDenominator
    fun_prop
  · exact fun z => ne_of_gt (cylinderDenominator_pos z)

def cylinderTime (z : I × ClosedUnitBall E) : I :=
  ⟨2 - cylinderScale z * (2 - (z.1)), by
    have hscale := cylinderScale_nonneg z
    have hmul := cylinderScale_mul_denominator z
    have hden : 2 - (z.1 : ℝ) ≤ cylinderDenominator z := le_max_left _ _
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
    · have h : 2 - (z.1 : ℝ) ≤ cylinderDenominator z := le_max_left _ _
      simp_all
    · have h : 2 * ‖z.2.val‖ ≤ cylinderDenominator z := le_max_right _ _
      simp_all
  simp [cylinderScale, hden]

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

/-- Paste the disk map and its boundary homotopy on the bottom and side. -/
def ballBoundaryPasting (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z))
    (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x)) :
    C(BallCylinderBoundary E, Z) :=
  cylinderPasting (T := {0}) (S := {x : ClosedUnitBall E | ‖x.val‖ = 1})
    ⟨fun z => f z.2, f.continuous.comp continuous_snd⟩
    ⟨fun z => H (z.1, ⟨z.2.val.val, z.2.property⟩), by fun_prop⟩
    isClosed_singleton (isClosed_eq (by fun_prop) continuous_const) (by
      rintro ⟨t, ht⟩ x
      change t = 0 at ht
      subst t
      exact (h₀ ⟨x.val.val, x.property⟩).symm)

/-- Explicit homotopy extension across a closed disk. -/
def ballHomotopyExtension (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z))
    (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x)) :
    C(I × ClosedUnitBall E, Z) :=
  (ballBoundaryPasting f H h₀).comp ballCylinderRetraction

@[simp] theorem ballHomotopyExtension_zero (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z))
    (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x)) (x : ClosedUnitBall E) :
    ballHomotopyExtension f H h₀ (0, x) = f x := by
  change ballBoundaryPasting f H h₀ (ballCylinderRetraction (0, x)) = f x
  rw [ballCylinderRetraction_fixed ⟨(0, x), Or.inl rfl⟩]
  unfold ballBoundaryPasting
  rw [cylinderPasting_slice _ (Set.mem_singleton 0)]
  rfl

@[simp] theorem ballHomotopyExtension_boundary (f : C(ClosedUnitBall E, Z))
    (H : C(I × UnitBoundary E, Z))
    (h₀ : ∀ x, H (0, x) = f (unitBoundaryInclusion E x))
    (t : I) (x : UnitBoundary E) :
    ballHomotopyExtension f H h₀ (t, unitBoundaryInclusion E x) = H (t, x) := by
  change ballBoundaryPasting f H h₀
    (ballCylinderRetraction (t, unitBoundaryInclusion E x)) = H (t, x)
  rw [ballCylinderRetraction_fixed
    ⟨(t, unitBoundaryInclusion E x), Or.inr x.property⟩]
  unfold ballBoundaryPasting
  apply cylinderPasting_side
  exact x.property

end FiniteChains.RelativeAttachment
