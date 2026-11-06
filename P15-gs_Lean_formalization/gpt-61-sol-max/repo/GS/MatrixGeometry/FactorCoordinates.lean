import Mathlib.Tactic
import GS.MatrixGeometry.Base

import GS.MatrixGeometry.Differential
import GS.OverlapGeometry.FactorChartOpen


set_option backward.isDefEq.respectTransparency false
/-!
# Product coordinates on the genuine shared factor group

The existing single-factor charts have full generator-space targets.  Their
product reconstruction is therefore open in the inherited factor topology.
This module also records its ambient differential and the differentiated
coordinate inverse; no orbit atlas is assumed.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.MatrixBase
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  {s right left : Pattern 𝕜 n}

variable (Q : Factor s) (g : Factors right left) (P : KMat 𝕜 n)

variable (v : Generator s)

/-- The actual matrix formula for the inverse of a shared factor chart. -/
def matrixReconstruct  : KMat 𝕜 n :=
  Factor.matrix (reconstruct Q v)

@[simp] theorem matrixReconstruct_zero :
    matrixReconstruct Q 0 = Factor.matrix Q := by simp_all [reconstruct_zero,matrixReconstruct]

theorem matrixReconstruct_smooth :
    ContDiff ℝ ⊤ (matrixReconstruct Q) := reconstruct_matrix_smooth Q

@[simp] theorem factorCoordinates_matrixReconstruct  :
    factorCoordinates Q (matrixReconstruct Q v) = v :=
  factorCoordinates_reconstruct Q v

/-- Differentiate the concrete total inverse chart, not an assigned tangent map. -/
theorem matrixReconstruct_fderiv_zero  :
    fderiv ℝ (matrixReconstruct Q) 0 v =
      (-2 : ℝ) • (Factor.matrix Q * v.val) := by
  have hi := ((matrixReconstruct_smooth Q).differentiable (by simp) 0).hasFDerivAt
  have hl  := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact (hi.comp_hasDerivAt_of_eq 0 hl (by simp)).unique
    (reconstruct_line_hasDerivAt_zero Q v)

/-- The ambient coordinate extension is a left inverse of the actual inverse-
chart derivative at every generator, not only at the chart centre. -/
theorem coordinateDerivative_reconstruct  :
    (fderiv ℝ (factorCoordinates Q) (matrixReconstruct Q v)).comp
      (fderiv ℝ (matrixReconstruct Q) v) =
        ContinuousLinearMap.id ℝ (Generator s) := by
  rw [← fderiv_comp v
    ((factorCoordinates_smooth_at Q (matrixReconstruct Q v)
      (reconstruct_mem_source Q v)).differentiableAt (by simp))
    ((matrixReconstruct_smooth Q).differentiable (by simp) v)]
  simp only [Function.comp_def, factorCoordinates_matrixReconstruct]
  exact fderiv_id

/-- Source of the product of the existing single-factor charts. -/
def pairSource : Set (Factors right left) :=
  factorSource g.1 ×ˢ factorSource g.2

variable (X : MatrixOrbit right left P)

variable (v : PairGenerator right left)


def pairCoordinates (h : Factors right left) : PairGenerator right left :=
  (factorCoordinates g.1 (Factor.matrix h.1),
    factorCoordinates g.2 (Factor.matrix h.2))

theorem pairSource_open : IsOpen (pairSource g) :=
  (factorSource_open g.1).prod (factorSource_open g.2)

@[simp] theorem self_mem_pairSource : g ∈ pairSource g :=
  ⟨base_mem_factorSource g.1, base_mem_factorSource g.2⟩



theorem factorLift_pairCoordinates (h : Factors right left) (hh : h ∈ pairSource g) : factorLift g (pairCoordinates g h) = h := by
  apply Prod.ext
  · exact reconstruct_factorCoordinates g.1 h.1 hh.1
  · exact reconstruct_factorCoordinates g.2 h.2 hh.2



theorem reconstruct_isOpenMap : IsOpenMap (reconstruct Q) := by
  intro U hU
  exact (factorPartialChart Q).isOpen_image_symm_of_subset_target hU
    (by tauto)

/-- Positively dimensional stabilizers do not affect openness of reconstruction. -/
theorem factorLift_isOpenMap : IsOpenMap (factorLift g) :=
  (reconstruct_isOpenMap g.1).prodMap (reconstruct_isOpenMap g.2)

theorem factorLift_orbit_isOpenMap :
    IsOpenMap (fun v : PairGenerator right left =>
      orbitMapToOrbit right left P (factorLift g v)) :=
  (orbitMapToOrbit_isOpenMap P).comp (factorLift_isOpenMap g)

/-- Smooth linear action of any fixed shared factor pair on ambient matrices. -/
theorem fixed_action_smooth :
    ContDiff ℝ ⊤ (fun A : KMat 𝕜 n => g • A) := by
  change ContDiff ℝ ⊤ (fun A : KMat 𝕜 n => Factor.matrix g.1 * A * (Factor.matrix g.2)ᴴ)
  fun_prop

/-- A fixed representative is used only to centre a chart.  No continuity
of this choice function is asserted or used. -/
def preferredFactor  : Factors right left :=
  Classical.choose X.property

@[simp] theorem preferredFactor_spec  :
    orbitMapToOrbit right left P (preferredFactor P X) = X := by
  apply Subtype.ext
  exact Classical.choose_spec X.property

/-- A total matrix-orbit parametrization; only injectivity will be local. -/
def orbitInverse (g : Factors right left) (v : PairGenerator right left) := orbitMapToOrbit right left P (factorLift g v)



/-- Fixed group translation of the total factor chart. -/
theorem factorLift_eq_mul  :
    factorLift g v = g * factorLift (1 : Factors right left) v := by
  apply Prod.ext
  · change reconstruct g.1 v.1 = g.1 * reconstruct (1 : Factor left) v.1
    simp only [reconstruct, one_mul]
  · change reconstruct g.2 v.2 = g.2 * reconstruct (1 : Factor right) v.2
    simp only [reconstruct, one_mul]

/-- This identity is global in the coordinate model. -/
theorem orbitParam_eq_translate  :
    orbitParam g P v = g • orbitParam (1 : Factors right left) P v := by grind [orbitParam,factorLift_eq_mul,mul_smul]

end GS.MatrixGeometry
