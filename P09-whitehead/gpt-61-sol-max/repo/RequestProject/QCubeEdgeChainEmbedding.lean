import Mathlib.Tactic

import RequestProject.QCubeEdgeSubdivision

/-! Faithful subdivision of finite chains on actual one-dimensional quotient cubes. -/
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

abbrev QEdge (A : CommRel V) := {c : QCube A // c.spx.card = 1}

variable (c : QEdge A)
noncomputable def qEdgeDirection   :=
  Classical.choose (Finset.card_eq_one.mp c.2)

section
omit [DecidableEq V]
theorem qEdge_free_direction (c : QEdge A) : c.1.spx = {qEdgeDirection c} :=
  Classical.choose_spec (Finset.card_eq_one.mp c.2)

abbrev qEdge_direction_unique (c : QEdge A) (v : V) (hs : c.1.spx = {v})  :=
  Finset.singleton_inj.mp ((qEdge_free_direction c).symm.trans hs)
end

noncomputable def qEdgeSubdivision   :=
  oneCubeSubdivision c.1 (qEdgeDirection c) (qEdge_free_direction c)

theorem qEdgeSubdivision_eq  (v : V) (hs : c.1.spx = {v}) :
    qEdgeSubdivision c = oneCubeSubdivision c.1 v hs := by
  have he := qEdge_direction_unique c v hs
  subst v
  rfl

noncomputable def qEdgeChainSubdivision : (QEdge A →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ qEdgeSubdivision

abbrev qEdgeSubdivision_ne_zero   :=
  cubeEdgeSubdivision_ne_zero c.1 (qEdgeDirection c) (by rw [qEdge_free_direction]; simp)

theorem qEdgeChainSubdivision_filter_top (r : QEdge A →₀ ℤ) (c : QEdge A) :
    (qEdgeChainSubdivision r).filter
      (fun e : (strictOrderCx (QCube A)).E => e.1.2 = c.1) = r c • qEdgeSubdivision c := by
  classical
  induction r using Finsupp.induction_linear with
  | zero => simp [Finsupp.filter_zero]
  | add r s hr hs => simp_all [add_smul]
  | single d n =>
      aesop (add simp [qEdgeChainSubdivision, cubeEdgeSubdivision_filter_tgt, qEdgeSubdivision, oneCubeSubdivision])

theorem qEdgeChainSubdivision_injective : Function.Injective (qEdgeChainSubdivision (A := A)) := by
  intro r s h
  have hz : qEdgeChainSubdivision (r - s) = 0 := by rw [map_sub, h, sub_self]
  have hr : r - s = 0 := by
    ext c
    have he := congrArg (Finsupp.filter
      (fun e : (strictOrderCx (QCube A)).E => e.1.2 = c.1)) hz
    rw [qEdgeChainSubdivision_filter_top, Finsupp.filter_zero] at he
    exact (smul_eq_zero.mp he).resolve_right (qEdgeSubdivision_ne_zero c)
  exact sub_eq_zero.mp hr

end FiniteChains.Davis
