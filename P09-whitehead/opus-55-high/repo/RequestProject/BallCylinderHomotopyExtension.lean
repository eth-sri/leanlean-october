import RequestProject.AttachmentHomotopyExtension
import Mathlib.Analysis.Normed.Group.Constructions


/-! Homotopy extension on the entire boundary of `I × D`, including both
ends. The cylinder is the unit ball for the product supremum norm. -/

noncomputable section

namespace FiniteChains.RelativeAttachment
open scoped unitInterval

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev FullBallCylinderBoundary :=
  {z : I × ClosedUnitBall E // z.1 = 0 ∨ z.1 = 1 ∨ ‖z.2.val‖ = 1}

def ballCylinderForward (z : ClosedUnitBall (ℝ × E)) : I × ClosedUnitBall E :=
  (⟨(z.val.1 + 1) / 2, by
    have h : |z.val.1| ≤ 1 := by
      aesop
    grind⟩,
   ⟨z.val.2, (norm_snd_le z.val).trans z.property⟩)

def ballCylinderInverse (z : I × ClosedUnitBall E) : ClosedUnitBall (ℝ × E) :=
  ⟨(2 * (z.1 : ℝ) - 1, z.2.val), by
    rw [Prod.norm_mk, Real.norm_eq_abs]
    grind⟩

/-- The cylinder is literally a ball in the product norm, after rescaling
its interval coordinate from `[-1,1]` to `[0,1]`. -/
def ballCylinderHomeomorph : ClosedUnitBall (ℝ × E) ≃ₜ I × ClosedUnitBall E where
  toFun := ballCylinderForward E
  invFun := ballCylinderInverse E
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change 2 * ((z.val.1 + 1) / 2) - 1 = z.val.1
      ring
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change ((2 * (z.1 : ℝ) - 1) + 1) / 2 = (z.1 : ℝ)
      ring
    · rfl
  continuous_toFun := by
    unfold ballCylinderForward
    fun_prop
  continuous_invFun := by
    unfold ballCylinderInverse
    fun_prop

omit [NormedSpace ℝ E] in
theorem ballCylinderForward_boundary (z : UnitBoundary (ℝ × E)) :
    (ballCylinderHomeomorph E (unitBoundaryInclusion (ℝ × E) z)).1 = 0 ∨
    (ballCylinderHomeomorph E (unitBoundaryInclusion (ℝ × E) z)).1 = 1 ∨
    ‖(ballCylinderHomeomorph E (unitBoundaryInclusion (ℝ × E) z)).2.val‖ = 1 := by
  have he : max |z.val.1| ‖z.val.2‖ = 1 := by
    aesop
  by_cases hs : ‖z.val.2‖ = 1
  · tauto
  by_cases hz : 0 ≤ z.val.1
  · right
    left
    apply Subtype.ext
    change (z.val.1 + 1) / 2 = (1 : ℝ)
    grind
  · left
    apply Subtype.ext
    change (z.val.1 + 1) / 2 = (0 : ℝ)
    grind

omit [NormedSpace ℝ E] in
theorem ballCylinderInverse_boundary (z : FullBallCylinderBoundary E) :
    ‖((ballCylinderHomeomorph E).symm z.val).val‖ = 1 := by
  apply le_antisymm (by grind)
  change 1 ≤ max ‖2 * (z.val.1 : ℝ) - 1‖ ‖z.val.2.val‖
  rcases z.property with hz | hz | hz
  · simp_all
  · have ht : ‖2 * (z.val.1 : ℝ) - 1‖ = 1 := by norm_num [hz]
    simp_all
  simp_all

/-- The sphere for the product norm is exactly the union of the two ends
and the side boundary of the disk cylinder. -/
def ballCylinderBoundaryHomeomorph : UnitBoundary (ℝ × E) ≃ₜ FullBallCylinderBoundary E where
  toFun z := ⟨ballCylinderHomeomorph E (unitBoundaryInclusion (ℝ × E) z),
    ballCylinderForward_boundary E z⟩
  invFun z := ⟨((ballCylinderHomeomorph E).symm z.val).val,
    ballCylinderInverse_boundary E z⟩
  left_inv z := by
    aesop
  right_inv z := by
    apply Subtype.ext
    exact (ballCylinderHomeomorph E).apply_symm_apply z.val
  continuous_toFun :=
    ((ballCylinderHomeomorph E).continuous.comp
      (unitBoundaryInclusion (ℝ × E)).continuous).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp
      ((ballCylinderHomeomorph E).symm.continuous.comp continuous_subtype_val)).subtype_mk _

/-- Relative homotopy extension that also keeps both endpoint disk maps
fixed. This is the geometric input for cancelling a boundary backtrack. -/
theorem fullBallCylinderBoundary_hasHomotopyExtension :
    HasHomotopyExtension (Subtype.val : FullBallCylinderBoundary E → I × ClosedUnitBall E) :=
  (unitBoundary_hasHomotopyExtension _).homeomorph
    (ballCylinderBoundaryHomeomorph E) _ Subtype.val
    (by aesop)
