import RequestProject.SquareSideQuotient
import RequestProject.ClassicalCWOneCellCellularization


/-! Affine coordinates identify the actual sup-norm disk boundary with
the square boundary, and the one-dimensional disk with the unit interval. -/

noncomputable section
namespace FiniteChains.RelativeAttachment
open scoped Topology unitInterval Classical

theorem norm_coordinate_bounds (x : Fin n → ℝ)
    (hx : ‖x‖ ≤ 1) i : -1 ≤ x i ∧ x i ≤ 1 := by
  have hi := (Real.norm_eq_abs _) ▸ (norm_le_pi_norm x i).trans hx
  exact abs_le.mp hi

theorem norm_one_coordinate (x : Fin n → ℝ) (hx : ‖x‖ = 1) :
    ∃ i, x i = 1 ∨ x i = -1 := by
  by_contra! h
  have hl := (pi_norm_lt_iff zero_lt_one).mpr (fun i => by
    have hu := (norm_le_pi_norm x i).trans hx.le
    apply lt_of_le_of_ne hu
    intro he
    have hi := (abs_eq zero_le_one).mp
      (by omega)
    simp_all)
  simp_all

def unitBoundarySquareHomeomorph : UnitBoundary (Fin 2 → ℝ) ≃ₜ SquareBoundary where
  toFun x := ⟨fun i => ⟨(x.val i + 1) / 2, by
      have hi := norm_coordinate_bounds x.val x.property.le i
      grind⟩, by
    obtain ⟨i, hi | hi⟩ := norm_one_coordinate x.val x.property
    · exact ⟨i, Or.inr (Subtype.ext (by simp_all))⟩
    · exact ⟨i, Or.inl (Subtype.ext (by simp_all))⟩⟩
  invFun x := ⟨fun i => 2 * (x.val i : ℝ) - 1, by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      grind [Real.norm_eq_abs]
    · obtain ⟨i, hi | hi⟩ := x.property
      · have h := norm_le_pi_norm (fun j => 2 * (x.val j : ℝ) - 1) i
        simp_all
      · have h := norm_le_pi_norm (fun j => 2 * (x.val j : ℝ) - 1) i
        simp_all [hi, Set.Icc.coe_one, mul_one, show (2 : ℝ) - 1 = 1 by norm_num, norm_one]⟩
  left_inv x := by
    apply Subtype.ext
    grind
  right_inv x := by
    simp
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
    grind⟩
  invFun t := ⟨fun _ => 2 * (t : ℝ) - 1, by
    rw [pi_norm_const, Real.norm_eq_abs]
    grind⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    grind
  right_inv t := by
    simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2
  continuous_invFun := by
    fun_prop

def oneBoundaryPoint (b : Bool) : UnitBoundary (Fin 1 → ℝ) :=
  ⟨fun _ => if b then 1 else -1, by aesop⟩

theorem oneBoundary_eq a :
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

@[simp] theorem oneBallIntervalHomeomorph_boundary b :
    oneBallIntervalHomeomorph (unitBoundaryInclusion _ (oneBoundaryPoint b)) =
      boolEndpoint b := by
  apply Subtype.ext
  cases b <;> norm_num [oneBallIntervalHomeomorph, unitBoundaryInclusion,
    oneBoundaryPoint, boolEndpoint]
