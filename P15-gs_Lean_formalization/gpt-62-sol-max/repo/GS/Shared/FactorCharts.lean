module

public import GS.Shared.Factors
public import GS.Shared.Frobenius
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import GS.Shared.Directions

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

section

/-!
# A Cayley atlas on the actual shared factor group

The chart model is the concrete subspace of supported tied skew-Hermitian matrices.
The source uses the existing matrix topology, and its inverse is defined on
the entire model.  Transition functions are restrictions of rational ambient
matrix formulas.  This establishes the factor manifold, not yet the shared
matrix-orbit manifold or its tangent bundle.
-/

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
open scoped Topology Manifold
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : ℕ} {s : Pattern 𝕜 n}

/-- A total continuous linear extension of the shared chart coordinates. -/
def modelProjection (s : Pattern 𝕜 n) : M 𝕜 n →L[ℝ] Generator s :=
  (frobProjection (sharedSkewSpace s.size s.label)).codRestrict _ (frobProjection_mem _)

/-- Open neighbourhood of Q inside the inherited shared-factor topology. -/
def factorSource (Q : Factor s) : Set (Factor s) :=
  {U | admissible ((Factor.matrix Q)ᴴ * Factor.matrix U)}

def factorCoordinates (Q : Factor s) (A : M 𝕜 n) : Generator s :=
  modelProjection s (cayley ((Factor.matrix Q)ᴴ * A))

/-- All shared skew coordinates reconstruct valid shared unitary factors. -/
def reconstruct (Q : Factor s) (C : Generator s) : Factor s :=
  Q * Factor.ofMatrix (cayley C.val) (cayley_shared s.divides C.property)

@[simp] theorem reconstruct_matrix (Q : Factor s) (C : Generator s) :
    Factor.matrix (reconstruct Q C) = Factor.matrix Q * cayley C.val := rfl

@[simp] theorem base_mem_factorSource (Q : Factor s) : Q ∈ factorSource Q := by
  change admissible ((Factor.matrix Q)ᴴ * Factor.matrix Q)
  rw [(Factor.matrix_unitary Q).1]
  exact admissible_one

theorem centered_reconstruct (Q : Factor s) (C : Generator s) :
    (Factor.matrix Q)ᴴ * Factor.matrix (reconstruct Q C) = cayley C.val := by
  rw [reconstruct_matrix, (Factor.matrix_unitary Q).adjoint_mul_cancel]

@[simp] theorem factorCoordinates_reconstruct (Q : Factor s) (C : Generator s) :
    factorCoordinates Q (Factor.matrix (reconstruct Q C)) = C := by
  unfold factorCoordinates
  rw [centered_reconstruct,
    cayley_involutive C.val (admissible_of_isSkew C.val C.property.2.1)]
  exact Subtype.ext (frobProjection_of_mem _ _ C.property)

theorem reconstruct_factorCoordinates (Q U : Factor s) (hU : U ∈ factorSource Q) :
    reconstruct Q (factorCoordinates Q (Factor.matrix U)) = U := by
  apply Factor.matrix_injective
  have h := cayley_sharedSkew s.divides (shared_factor_mul s.divides
      (shared_factor_conjTranspose (Factor.matrix_shared Q)) (Factor.matrix_shared U)) hU
  rw [reconstruct_matrix, show (factorCoordinates Q (Factor.matrix U)).val = _ from
    frobProjection_of_mem _ _ h, cayley_involutive _ hU,
    (Factor.matrix_unitary Q).mul_adjoint_cancel]

@[simp] theorem reconstruct_zero (Q : Factor s) : reconstruct Q 0 = Q := by
  apply Factor.matrix_injective
  simp only [reconstruct_matrix, Submodule.coe_zero, cayley_zero, Matrix.mul_one]

theorem factorCoordinates_smooth_at (Q : Factor s) (A : M 𝕜 n)
    (hA : admissible ((Factor.matrix Q)ᴴ * A)) :
    ContDiffAt ℝ ⊤ (factorCoordinates Q) A :=
  (modelProjection s).contDiff.contDiffAt.comp A
    (smooth_cayley_comp_at (smooth_mul_at contDiffAt_const contDiffAt_id) hA)

/-- The actual matrix formula for the inverse of a shared factor chart. -/
def matrixReconstruct (Q : Factor s) (v : Generator s) : M 𝕜 n :=
  Factor.matrix (reconstruct Q v)

@[simp] theorem matrixReconstruct_zero (Q : Factor s) :
    matrixReconstruct Q 0 = Factor.matrix Q := by
  simp only [matrixReconstruct, reconstruct_zero]

@[fun_prop] theorem matrixReconstruct_smooth (Q : Factor s) :
    ContDiff ℝ ⊤ (matrixReconstruct Q) := by
  apply contDiff_iff_contDiffAt.mpr
  intro C
  exact smooth_mul_at contDiffAt_const
    (smooth_cayley_comp_at
      (sharedSkewSpace (𝕜 := 𝕜) (n := n) s.size s.label).subtypeL.contDiff.contDiffAt
      (admissible_of_isSkew C.val C.property.2.1))

@[fun_prop] theorem continuous_reconstruct (Q : Factor s) : Continuous (reconstruct Q) :=
  (matrixReconstruct_smooth Q).continuous.subtype_mk _

local notation "S" => sharedSkewSpace (𝕜 := 𝕜) (n := n) s.size s.label

theorem matrixReconstruct_hasFDerivAt_zero (Q : Factor s) :
    HasFDerivAt (matrixReconstruct Q) ((-2 : ℝ) • ((mulCLM (Factor.matrix Q)).comp (S).subtypeL)) 0 := by
  have h := cayley_hasFDerivAt_zero.comp (0 : Generator s) (S).subtypeL.hasFDerivAt
  exact ((mulCLM (Factor.matrix Q)).hasFDerivAt.comp 0 h).congr_fderiv (by aesop)

theorem matrixReconstruct_fderiv_zero (Q : Factor s) (v : Generator s) :
    fderiv ℝ (matrixReconstruct Q) 0 v = (-2 : ℝ) • (Factor.matrix Q * v.val) :=
  DFunLike.congr_fun (matrixReconstruct_hasFDerivAt_zero Q).fderiv v

/-- A total extension on each side, with an open source and full linear target. -/
def factorPartialChart (Q : Factor s) : OpenPartialHomeomorph (Factor s) (Generator s) where
  toFun U := factorCoordinates Q (Factor.matrix U)
  invFun := reconstruct Q
  source := factorSource Q
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' C _ := by
    change admissible ((Factor.matrix Q)ᴴ * Factor.matrix (reconstruct Q C))
    rw [centered_reconstruct]
    exact admissible_cayley _ (admissible_of_isSkew _ C.property.2.1)
  left_inv' U hU := reconstruct_factorCoordinates Q U hU
  right_inv' C _ := factorCoordinates_reconstruct Q C
  open_source := admissible_open.preimage (continuous_const.mul Factor.continuous_matrix)
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro U hU
    exact ((factorCoordinates_smooth_at Q (Factor.matrix U) hU).continuousAt.comp
      Factor.continuous_matrix.continuousAt).continuousWithinAt
  continuousOn_invFun := (continuous_reconstruct Q).continuousOn

end GS.Shared

end

section

/-!
# The actual shared orbit differential and its stabilizer kernel

Differentiate the concrete Cayley factor parametrization, retaining the -2
and +2 coefficients of the existing Cayley convention.  Its range is exactly
the point-based shared direction space.  At the identity, its entire kernel
integrates to the actual shared stabilizer; conversely every stabilizer element
in this Cayley chart comes from that kernel.

These are coordinate differentials of an actual smooth factor map.  No atlas
or manifold tangent space on its orbit image is introduced in this module.
-/

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
open scoped Topology Manifold
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : ℕ} {right left : Pattern 𝕜 n}

/-- Total reconstruction in the genuine shared product group. -/
def factorLift (g : Factors right left) (v : PairGenerator right left) :
    Factors right left := (reconstruct g.1 v.1, reconstruct g.2 v.2)

@[simp] theorem factorLift_zero (g : Factors right left) : factorLift g 0 = g := by
  simp [factorLift]

@[fun_prop] theorem continuous_factorLift (g : Factors right left) : Continuous (factorLift g) := by
  unfold factorLift
  fun_prop

/-- Matrix formula on the whole shared coordinate model. -/
def orbitParam (g : Factors right left) (P : M 𝕜 n) (v : PairGenerator right left) :
    M 𝕜 n := factorLift g v • P

@[simp] theorem orbitParam_zero (g : Factors right left) (P : M 𝕜 n) :
    orbitParam g P 0 = g • P := by simp only [orbitParam, factorLift_zero]

theorem orbitParam_smooth (g : Factors right left) :
    ContDiff ℝ ⊤ (fun p : M 𝕜 n × PairGenerator right left => orbitParam g p.1 p.2) := by
  change ContDiff ℝ ⊤ (fun p : M 𝕜 n × PairGenerator right left =>
    matrixReconstruct g.1 p.2.1 * p.1 * (matrixReconstruct g.2 p.2.2)ᴴ)
  fun_prop

theorem orbitParam_hasFDerivAt_zero (P : M 𝕜 n) :
    HasFDerivAt (orbitParam (1 : Factors right left) P) (orbitDerivative right left P) 0 := by
  let V := PairGenerator right left
  have hl := (matrixReconstruct_hasFDerivAt_zero (1 : Factor left)).comp (0 : V)
    (ContinuousLinearMap.fst ℝ (Generator left) (Generator right)).hasFDerivAt
  have hr := (matrixReconstruct_hasFDerivAt_zero (1 : Factor right)).comp (0 : V)
    (ContinuousLinearMap.snd ℝ (Generator left) (Generator right)).hasFDerivAt
  have h := mulCLM.hasFDerivAt_of_bilinear
    (mulCLM.hasFDerivAt_of_bilinear hl (hasFDerivAt_const P (0 : V)))
    (adjCLM.hasFDerivAt.comp 0 hr)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  let A := matrixReconstruct (1 : Factor left) 0
  let B := matrixReconstruct (1 : Factor right) 0
  change A * P * ((-2 : ℝ) • ((1 : M 𝕜 n) * v.2.val))ᴴ +
    (A * 0 + ((-2 : ℝ) • ((1 : M 𝕜 n) * v.1.val)) * P) * Bᴴ =
      (-2 : ℝ) • (v.1.val * P - P * v.2.val)
  simp [A, B, sub_eq_add_neg, add_comm,
    show v.2.valᴴ = -v.2.val from v.2.property.2.1]

/-- A Cayley step in a kernel direction stabilizes the carrier, at every scale. -/
theorem factorLift_stabilizes_of_kernel (P : M 𝕜 n) (v : PairGenerator right left)
    (hv : orbitDerivative right left P v = 0) :
    factorLift (1 : Factors right left) v • P = P := by
  rw [orbitDerivative_apply, smul_eq_zero] at hv
  have he := sub_eq_zero.mp (hv.resolve_left (by norm_num))
  have hA := admissible_of_isSkew v.1.val v.1.property.2.1
  have hB := admissible_of_isSkew v.2.val v.2.property.2.1
  change (1 * cayley v.1.val) * P * (1 * cayley v.2.val)ᴴ = P
  rw [Matrix.one_mul, Matrix.one_mul, cayley_intertwine _ _ _ hA hB he,
    Matrix.mul_assoc, ((cayley_unitary_iff _ hB).mpr v.2.property.2.1).2, Matrix.mul_one]

end GS.Shared

end
