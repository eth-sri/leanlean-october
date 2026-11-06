import Mathlib.Tactic

import RequestProject.HomeomorphContinuousMap
import RequestProject.TopologicalCoverPi2
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Tactic

/-! A moving constant boundary can be made stationary by an explicit square collar.
The construction uses no local contractibility or cofibration hypothesis on the target. -/

noncomputable section

namespace Whitehead
open scoped unitInterval Topology

abbrev Square := Fin 2 → I

def squareOrigin : Square := fun _ => 0

theorem squareOrigin_boundary : squareOrigin ∈ Cube.boundary (Fin 2) :=
  ⟨0, Or.inl rfl⟩

variable (z : Square)
/-- Distance from the nearest face of the square, in its standard coordinates. -/
def squareDepth   :=
  min (min (z 0 : ℝ) (1 - z 0)) (min (z 1 : ℝ) (1 - z 1))

theorem squareDepth_nonneg  : 0 ≤ squareDepth z := le_min (le_min (z 0).2.1 (sub_nonneg.mpr (z 0).2.2))
    (le_min (z 1).2.1 (sub_nonneg.mpr (z 1).2.2))

theorem squareDepth_le_coordinate  (i : Fin 2) :
    squareDepth z ≤ (z i : ℝ) := by
  fin_cases i
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)

theorem squareDepth_le_complement  (i : Fin 2) :
    squareDepth z ≤ 1 - (z i : ℝ) := by
  fin_cases i
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem squareDepth_boundary  (hz : z ∈ Cube.boundary (Fin 2)) :
    squareDepth z = 0 := by
  apply le_antisymm _ (squareDepth_nonneg z)
  obtain ⟨i, hi | hi⟩ := hz
  · simpa [hi, Set.Icc.coe_zero] using squareDepth_le_coordinate z i
  · simpa [hi, Set.Icc.coe_one, sub_self] using squareDepth_le_complement z i

theorem squareDepth_coordinate  :
    ∃ i : Fin 2, squareDepth z = (z i : ℝ) ∨ squareDepth z = 1 - (z i : ℝ) := by
  have hmin (a b : ℝ) : min a b = a ∨ min a b = b := by
    grind
  rcases hmin (min (z 0 : ℝ) (1 - z 0)) (min (z 1 : ℝ) (1 - z 1)) with h | h
  · exact ⟨0, (hmin (z 0 : ℝ) (1 - z 0)).imp (h.trans ·) (h.trans ·)⟩
  · exact ⟨1, (hmin (z 1 : ℝ) (1 - z 1)).imp (h.trans ·) (h.trans ·)⟩

theorem squareDepth_continuous : Continuous squareDepth := by
  unfold squareDepth
  fun_prop

variable (s : I)
theorem squareCollarDenom_pos  : 0 < 1 - (s : ℝ) / 2 := by
  have hs := s.2.2
  linarith

variable (z : Square)
/-- The inner square expands to the whole square; points in the collar hit its boundary. -/
def squareCollarExpand    := fun i =>
  Set.projIcc 0 1 zero_le_one (((z i : ℝ) - (s : ℝ) / 4) / (1 - (s : ℝ) / 2))

theorem squareCollarExpand_continuous :
    Continuous (fun sz : I × Square => squareCollarExpand sz.1 sz.2) := by
  apply continuous_pi
  intro i
  apply continuous_projIcc.comp
  exact ((((continuous_apply i).comp continuous_snd).subtype_val.sub
    (continuous_fst.subtype_val.div_const 4)).div
    (continuous_const.sub (continuous_fst.subtype_val.div_const 2))
    (fun sz => ne_of_gt (squareCollarDenom_pos sz.1)))

theorem squareCollarExpand_zero  : squareCollarExpand 0 z = z := by
  funext i
  simp_all [squareCollarExpand]

theorem squareCollarExpand_boundary  
    (hz : squareDepth z ≤ (s : ℝ) / 4) :
    squareCollarExpand s z ∈ Cube.boundary (Fin 2) := by
  obtain ⟨i, hi | hi⟩ := squareDepth_coordinate z
  · refine ⟨i, Or.inl ?_⟩
    apply projIcc_eq_zero.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · exact (squareCollarDenom_pos s).le
  · refine ⟨i, Or.inr ?_⟩
    apply projIcc_eq_one.mpr
    apply (le_div_iff₀ (squareCollarDenom_pos s)).mpr
    linarith

/-- Time stops at the collar, whose boundary is always at time zero. -/
def squareCollarTime   : I :=
  ⟨min (s : ℝ) (4 * squareDepth z),
    le_min s.2.1 (mul_nonneg (by norm_num) (squareDepth_nonneg z)),
    (min_le_left _ _).trans s.2.2⟩

theorem squareCollarTime_continuous :
    Continuous (fun sz : I × Square => squareCollarTime sz.1 sz.2) :=
  (continuous_fst.subtype_val.min
    (continuous_const.mul (squareDepth_continuous.comp continuous_snd))).subtype_mk _

theorem squareCollarTime_zero  : squareCollarTime 0 z = 0 := by
  apply Subtype.ext
  exact min_eq_left (mul_nonneg (by norm_num) (squareDepth_nonneg z))

theorem squareCollarTime_boundary  
    (hz : z ∈ Cube.boundary (Fin 2)) : squareCollarTime s z = 0 := by
  aesop (add simp [squareCollarTime, squareDepth_boundary])

/-- Constant boundary values are allowed to depend on homotopy time. -/
def SquareConstantBoundary {X : Type*} [TopologicalSpace X] (f : C((Fin 2 → I), X))  :=
  ∀ z ∈ Cube.boundary (Fin 2), f z = f (fun _ => 0)

/-- A null homotopy with moving but constant boundary gives a based null homotopy.
The first stage inserts a collar. The second contracts the resulting radial path. -/
theorem genLoop_null_of_movingBoundary {X : Type*} [TopologicalSpace X] {x y : X}
    (p : GenLoop (Fin 2) X x)
    (H : ContinuousMap.HomotopyWith p.val (ContinuousMap.const _ y) SquareConstantBoundary) :
    GenLoop.Homotopic p GenLoop.const := by
  let z₀  := squareOrigin
  have hz₀  := squareOrigin_boundary
  let h  := H.toContinuousMap.comp
    ⟨fun t => (t, z₀), continuous_id.prodMk continuous_const⟩
  have hzero : h 0 = x := (H.apply_zero z₀).trans (GenLoop.boundary p z₀ hz₀)
  let r : C((Fin 2 → I), I) :=
    ⟨squareCollarTime 1, squareCollarTime_continuous.comp
      (continuous_const.prodMk continuous_id)⟩
  let q : GenLoop (Fin 2) X x := ⟨h.comp r, fun z hz => by
    aesop (add simp [Whitehead.squareCollarTime_boundary])⟩
  have hfirst : GenLoop.Homotopic p q := by
    refine ⟨{
      toFun := fun sz => H (squareCollarTime sz.1 sz.2,
        squareCollarExpand sz.1 sz.2)
      continuous_toFun := H.continuous.comp
        (squareCollarTime_continuous.prodMk squareCollarExpand_continuous)
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · simp_all [squareCollarTime_zero, squareCollarExpand_zero]
    · intro z
      change H (squareCollarTime 1 z, squareCollarExpand 1 z) =
        H (squareCollarTime 1 z, z₀)
      by_cases hd : 1 ≤ 4 * squareDepth z
      · simp_all [squareCollarTime]
      · apply H.prop
        apply squareCollarExpand_boundary
        
        change squareDepth z ≤ (1 : ℝ) / 4
        linarith
    · intro s z hz
      change H (squareCollarTime s z, squareCollarExpand s z) = p z
      rw [squareCollarTime_boundary s z hz, H.apply_zero, GenLoop.boundary p z hz]
      exact GenLoop.boundary p _ (squareCollarExpand_boundary s z (by
        grind [squareDepth_boundary]))
  have hsecond : GenLoop.Homotopic q GenLoop.const := by
    refine ⟨{
      toFun := fun sz => h (unitInterval.symm sz.1 * r sz.2)
      continuous_toFun := h.continuous.comp (by
        fun_prop)
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · aesop
    · simp_all
    aesop (add simp [Whitehead.squareCollarTime_boundary])
  exact hfirst.trans hsecond

end Whitehead
