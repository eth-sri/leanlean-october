module

public import GS.Fibres
public import GS.CompactFibres
public import GS.Shuffle
public import GS.Projection
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


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

section
variable {n : ℕ} (A : Mat n)
/-- Matrix exponential by its series. The following lemmas identify it with
mathlib's exponential and establish convergence and continuity. -/
def matrixExp : Mat n :=
  ∑' k : ℕ, ((k.factorial : ℝ)⁻¹) • A^k

theorem matrixExp_eq_exp :
    matrixExp A = NormedSpace.exp A := by
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℝ)]
  rfl

theorem matrixExp_hasSum :
    HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • A^k) (matrixExp A) := by
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  rw [matrixExp_eq_exp]
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A

end

theorem continuous_matrixExp (n : ℕ) : Continuous (@matrixExp n) := by
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  rw [funext matrixExp_eq_exp]
  exact continuous_iff_continuousAt.mpr fun A => (NormedSpace.exp_analytic (𝕂 := ℝ) A).continuousAt

def rotation (t : ℝ) : Mat 2 :=
  !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

theorem continuous_rotation : Continuous rotation :=
  continuous_pi fun i => continuous_pi fun j => by fin_cases i <;> fin_cases j <;> simp [rotation] <;> fun_prop

theorem rotation_orthogonal (t : ℝ) : Orthogonal (rotation t) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotation,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] <;> nlinarith [Real.sin_sq_add_cos_sq t]

section
variable (q : ℕ)
/-- Parameters use full skew matrices rather than choosing a basis of so(q).
The later identification with R^(q(q-1)/2) remains a named obligation. -/
abbrev OriginalParameters :=
  (Fin q → ℝ) × (Fin q → ℝ) × Mat q × Mat q × CircleVector

def originalK (η : ℝ) : Set (OriginalParameters q) :=
  {p | let (ell,r,c,z,u) := p
       (∀ i, |ell i| ≤ η) ∧ (∀ j, |r j| ≤ η) ∧
       (∀ j : Fin q, j.val=0 → r j=0) ∧
       IsSkew c ∧ IsSkew z ∧ frobSq c ≤ η^2 ∧ frobSq z ≤ η^2 ∧ OnCircle u}

end

def originalPsi {q : ℕ} (Q₀ c : Mat q) : Mat q := Q₀ * matrixExp c

section
variable {q : ℕ} (Q₀ : Mat q)
theorem continuous_originalPsi :
    Continuous (originalPsi Q₀) :=
  continuous_const.mul (continuous_matrixExp q)

/-- The exact matrix map f from the original fibre proof. -/
def originalF (p : OriginalParameters q) : Mat (q*2) :=
  let (ell,r,c,z,u) := p
  let A := originalPsi Q₀ (c+z)
  let B := originalPsi Q₀ (c-z)
  fun i j =>
    let ri : Fin q × Fin 2 := finProdFinEquiv.symm i
    let rj : Fin q × Fin 2 := finProdFinEquiv.symm j
    (rotation (ell ri.1) * middleBlock (A ri.1 rj.1) (B ri.1 rj.1) u *
      rotation (r rj.1)) ri.2 rj.2

/-- Continuity of the actual matrix-valued parameter map, with its original
exponential definition and the matrix product topology. -/
theorem continuous_originalF :
    Continuous (originalF Q₀) := by
  have hpsi := continuous_originalPsi Q₀
  have hrot := continuous_rotation
  have ht := continuous_T
  unfold originalF middleBlock
  fun_prop

end

/-- The exact quotient coordinates before choosing a basis of skew matrices. -/
def originalG {q : ℕ} (p : OriginalParameters q) :
    (Fin q → ℝ) × (Fin q → ℝ) × Mat q × Matrix (Fin 2) (Fin q × Fin q) ℝ :=
  let (ell,r,c,z,u) := p
  (ell,r,c,outer u (fun ij => z ij.1 ij.2))

/-- Continuity of the actual quotient-coordinate map in the manuscript. -/
theorem continuous_originalG (q : ℕ) : Continuous (@originalG q) := by
  unfold originalG outer
  fun_prop

section
variable {q : ℕ}
/-- The full fibre relation of `originalG`, including the collapsed circle at
`z = 0`. Establishing the same relation for `originalF` is a separate task. -/
theorem originalG_fibres (ell r ell' r' : Fin q → ℝ) (c z c' w : Mat q) (u v : CircleVector)
    (hu : OnCircle u) (hv : OnCircle v) :
    originalG (ell,r,c,z,u) = originalG (ell',r',c',w,v) ↔
      ell = ell' ∧ r = r' ∧ c = c' ∧
        ((z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w)) := by
  simp [originalG, outer_fibres hu hv, funext_iff, ← Matrix.ext_iff]

end

/-- Perfect shuffle with the scalar row-major convention of the manuscript. -/
def scalarShuffle (k b : ℕ) : Equiv.Perm (Fin (k*b)) :=
  (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin k) (Fin b))).trans
    (finProdFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.mul_comm b k))))

def localFamily (q : ℕ) : Set (Mat (q*2)) :=
  let P := permMatrix (scalarShuffle q 2)
  {M | InA3Orth 2 q 2 P Pᵀ M}

def basePoint {q : ℕ} (Q₀ : Mat q) : Mat (q*2) := fun i j =>
  let ri : Fin q × Fin 2 := finProdFinEquiv.symm i
  let rj : Fin q × Fin 2 := finProdFinEquiv.symm j
  Q₀ ri.1 rj.1 * (1 : Mat 2) ri.2 rj.2

/-- Exact local Euclidean-chart property in the induced topology.
The target may be any open Euclidean set; it is not restricted to round balls. -/
def EuclideanAtSubset {X : Type*} [TopologicalSpace X] (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ ∃ (U : Set X), IsOpen U ∧ x ∈ U ∧
    ∃ (d : ℕ) (V : Set (EuclideanSpace ℝ (Fin d))), IsOpen V ∧
      Nonempty (↥(S ∩ U) ≃ₜ ↥V)

end GS
