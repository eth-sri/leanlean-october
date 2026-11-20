module

public import RequestProject.SquareSideQuotient
public import RequestProject.ClassicalCWOneCellCellularization

@[expose] public section

/-! Affine coordinates identify the actual sup-norm disk boundary with
the square boundary, and the one-dimensional disk with the unit interval. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped Topology unitInterval Classical

section

variable {n : ℕ} (x : Fin n → ℝ)
include n

theorem norm_coordinate_bounds
    (hx : ‖x‖ ≤ 1) (i : Fin n) : -1 ≤ x i ∧ x i ≤ 1 := abs_le.mp ((Real.norm_eq_abs (x i)) ▸ (norm_le_pi_norm x i).trans hx)

theorem norm_one_coordinate (hx : ‖x‖ = 1) :
    ∃ i, x i = 1 ∨ x i = -1 := by
  by_contra! h
  have hl : ‖x‖ < 1 := (pi_norm_lt_iff zero_lt_one).mpr (fun i => by
    have hu := (norm_le_pi_norm x i).trans hx.le
    grind [Real.norm_eq_abs])
  simp_all

end

def unitBoundarySquareHomeomorph : UnitBoundary (Fin 2 → ℝ) ≃ₜ SquareBoundary where
  toFun x := ⟨fun i => ⟨(x.val i + 1) / 2, by
      have hi := norm_coordinate_bounds x.val x.property.le i
      constructor <;> linarith⟩, by
    obtain ⟨i, hi | hi⟩ := norm_one_coordinate x.val x.property
    · exact ⟨i, Or.inr (Subtype.ext (by simp [hi]))⟩
    · exact ⟨i, Or.inl (Subtype.ext (by simp [hi]))⟩⟩
  invFun x := ⟨fun i => 2 * (x.val i) - 1, by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      grind [Real.norm_eq_abs]
    · obtain ⟨i, hi | hi⟩ := x.property
      · have h := norm_le_pi_norm (fun j => 2 * (x.val j : ℝ) - 1) i
        simp_all
      · have h := norm_le_pi_norm (fun j => 2 * (x.val j : ℝ) - 1) i
        norm_num only [hi, Set.Icc.coe_one, mul_one, show 2 - 1 = 1 by norm_num,
          norm_one] at h
        exact h⟩
  left_inv x := by
    ring
  right_inv x := by
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const).div_const 2
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_const.mul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val))).sub
        continuous_const

def oneBallIntervalHomeomorph : ClosedUnitBall (Fin 1 → ℝ) ≃ₜ I where
  toFun x := ⟨(x.val 0 + 1) / 2, by
    have hi := norm_coordinate_bounds x.val x.property 0
    constructor <;> linarith⟩
  invFun t := ⟨fun _ => 2 * t - 1, by
    rw [pi_norm_const, Real.norm_eq_abs] <;> grind⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    ring
  right_inv t := by
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2
  continuous_invFun := by
    fun_prop

def oneBoundaryPoint (b : Bool) : UnitBoundary (Fin 1 → ℝ) :=
  ⟨fun _ => if b then 1 else -1, by aesop⟩

theorem oneBoundary_eq (a : UnitBoundary (Fin 1 → ℝ)) :
    a = oneBoundaryPoint false ∨ a = oneBoundaryPoint true := by
  obtain ⟨i, hi | hi⟩ := norm_one_coordinate a.val a.property
  · apply Or.inr
    apply Subtype.ext
    funext j
    have hj : j = i := Subsingleton.elim _ _
    aesop
  · apply Or.inl
    apply Subtype.ext
    funext j
    have hj : j = i := Subsingleton.elim _ _
    aesop

@[simp] theorem oneBallIntervalHomeomorph_boundary (b : Bool) :
    oneBallIntervalHomeomorph (unitBoundaryInclusion _ (oneBoundaryPoint b)) =
      boolEndpoint b := by
  cases b <;> norm_num [oneBallIntervalHomeomorph, unitBoundaryInclusion,
    oneBoundaryPoint, boolEndpoint]

end FiniteChains.RelativeAttachment
