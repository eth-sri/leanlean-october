
import GS.Fibres
import GS.CompactFibres
import GS.Shuffle
import GS.Projection
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
open GS.MatrixBase




/-!
# Original local parameterization (definitions and elementary identities)

This file follows the manuscript's original variables ell, r, c, z, u.
No claim of a smooth manifold structure is used to define the maps. The hard
analytic statements about normalization, fibres, and local coverage remain
explicit goals in Specifications.lean.

-/

noncomputable section
open Matrix
namespace GS

variable (Q₀ c : Mat q)

variable (t : ℝ)

def rotation  : Mat 2 :=
  !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

theorem continuous_rotation : Continuous rotation := by fun_prop [rotation]

theorem rotation_orthogonal  : Orthogonal (rotation t) := by
  constructor <;> ext i j <;> fin_cases i,j <;>
    simp [rotation,Matrix.mul_apply,Matrix.transpose_apply,
      Fin.sum_univ_succ] <;> nlinarith [Real.sin_sq_add_cos_sq t]

/-- Parameters use full skew matrices rather than choosing a basis of so(q).
The later identification with R^(q(q-1)/2) remains a named obligation. -/
abbrev OriginalParameters (q : ℕ) :=
  (Fin q → ℝ) × (Fin q → ℝ) × Mat q × Mat q × CircleVector

def originalK (q : ℕ) (η : ℝ) : Set (OriginalParameters q) :=
  {p | let (ell,r,c,z,u) := p
       (∀ i, |ell i| ≤ η) ∧ (∀ j, |r j| ≤ η) ∧
       (∀ j : Fin q, j.val=0 → r j=0) ∧
       IsSkew c ∧ IsSkew z ∧ cFrobSq c ≤ η^2 ∧ cFrobSq z ≤ η^2 ∧ OnCircle u}

def originalPsi  : Mat q := Q₀ * NormedSpace.exp c

open scoped Norms.Operator in
 theorem continuous_originalPsi : Continuous (originalPsi Q₀) :=
  continuous_const.mul NormedSpace.exp_continuous

/-- The exact matrix map f from the original fibre proof. -/
def originalF  (p : OriginalParameters q) : Mat (q*2) :=
  let (ell,r,c,z,u) := p
  let A := originalPsi Q₀ (c+z)
  let B := originalPsi Q₀ (c-z)
  fun i j =>
    let ri := finProdFinEquiv.symm i
    let rj := finProdFinEquiv.symm j
    (rotation (ell ri.1) * middleBlock (A ri.1 rj.1) (B ri.1 rj.1) u *
      rotation (r rj.1)) ri.2 rj.2

/-- Continuity of the actual matrix-valued parameter map, with its original
exponential definition and the matrix product topology. -/
theorem continuous_originalF  :
    Continuous (originalF Q₀) := by
  have hpsi := continuous_originalPsi Q₀
  have hrot := continuous_rotation
  have ht := continuous_T
  unfold originalF middleBlock
  fun_prop

/-- The exact quotient coordinates before choosing a basis of skew matrices. -/
def originalG (p : OriginalParameters q) :
    (Fin q → ℝ) × (Fin q → ℝ) × Mat q × Matrix (Fin 2) (Fin q × Fin q) ℝ :=
  let (ell,r,c,z,u) := p
  (ell,r,c,outer u (fun ij => z ij.1 ij.2))

/-- Continuity of the actual quotient-coordinate map in the manuscript. -/
theorem continuous_originalG (q : ℕ) : Continuous (@originalG q) := by
  unfold originalG outer
  fun_prop

/-- The full fibre relation of `originalG`, including the collapsed circle at
`z = 0`. Establishing the same relation for `originalF` is a separate task. -/
theorem originalG_fibres (ell r ell' r' : Fin q → ℝ) (c z c' w : Mat q) (u v : CircleVector)
    (hu : OnCircle u) (hv : OnCircle v) :
    originalG (ell,r,c,z,u) = originalG (ell',r',c',w,v) ↔
      ell = ell' ∧ r = r' ∧ c = c' ∧
        ((z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w)) := by aesop (add norm [outer_fibres,originalG,funext_iff])

/-- Perfect shuffle with the scalar row-major convention of the manuscript. -/
def scalarShuffle (k b : ℕ) : Equiv.Perm (Fin (k*b)) := (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin k) (Fin b))).trans
    (finProdFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.mul_comm b k))))

def localFamily (q : ℕ) : Set (Mat (q*2)) := let P := permMatrix (scalarShuffle q 2)
  {M | InA3Orth 2 q 2 P Pᵀ M}

def basePoint  : Mat (q*2) := fun i j =>
  let ri := finProdFinEquiv.symm i
  let rj := finProdFinEquiv.symm j
  Q₀ ri.1 rj.1 * (1 : Mat 2) ri.2 rj.2

/-- Exact local Euclidean-chart property in the induced topology.
The target may be any open Euclidean set; it is not restricted to round balls. -/
def EuclideanAtSubset {X : Type*} [TopologicalSpace X] (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ ∃ (U : Set X), IsOpen U ∧ x ∈ U ∧
    ∃ (d : ℕ) (V : Set (EuclideanSpace ℝ (Fin d))), IsOpen V ∧
      Nonempty (↥(S ∩ U) ≃ₜ ↥V)

end GS
