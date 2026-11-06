import GS.MatrixGeometry.Base

import GS.MatrixGeometry.Factors
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace



/-!
# A Cayley atlas on the actual shared factor group

The chart model is the concrete subspace of supported tied skew-Hermitian matrices.
The source uses the existing matrix topology, and its inverse is defined on
the entire model.  Transition functions are restrictions of rational ambient
matrix formulas.  This establishes the factor manifold, not yet the shared
matrix-orbit manifold or its tangent bundle.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.MatrixBase
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  {s : Pattern 𝕜 n}
variable (Q : Factor s)

variable (C : Generator s)

variable (U : Factor s)

variable (A : KMat 𝕜 n)

/-- A total continuous linear extension of the shared chart coordinates. -/
def modelProjection (s : Pattern 𝕜 n) : KMat 𝕜 n →L[ℝ] Generator s :=
  (cFrobProjection (sharedSkewSpace s.size s.label)).codRestrict _ (cFrobProjection_mem _)


theorem modelProjection_val_of_mem (s : Pattern 𝕜 n) (A : KMat 𝕜 n)
    (hA : A ∈ sharedSkewSpace s.size s.label) : (modelProjection s A).val = A :=
  cFrobProjection_of_mem _ _ hA

@[simp] theorem modelProjection_inclusion  :
    modelProjection s C.val = C := by simp_all [modelProjection_val_of_mem,Subtype.ext]

/-- Open neighbourhood of Q inside the inherited shared-factor topology. -/
def factorSource  : Set (Factor s) :=
  {U | admissible ((Factor.matrix Q)ᴴ * Factor.matrix U)}

def factorCoordinates   : Generator s :=
  modelProjection s (cayley ((Factor.matrix Q)ᴴ * A))

/-- All shared skew coordinates reconstruct valid shared unitary factors. -/
def reconstruct   : Factor s :=
  Q * Factor.ofMatrix (cayley C.val) (cayley_shared s.positive s.divides C.property)

@[simp] theorem reconstruct_matrix   :
    Factor.matrix (reconstruct Q C) = Factor.matrix Q * cayley C.val := rfl

theorem factorSource_open  : IsOpen (factorSource Q) :=
  admissible_open.preimage
    (GS.MatrixBase.continuous_matrix_product continuous_const Factor.continuous_matrix)

@[simp] theorem base_mem_factorSource  : Q ∈ factorSource Q := by
  change admissible ((Factor.matrix Q)ᴴ * Factor.matrix Q)
  rw [(Factor.matrix_unitary Q).1]
  exact admissible_one

theorem centered_reconstruct   :
    (Factor.matrix Q)ᴴ * Factor.matrix (reconstruct Q C) = cayley C.val := by
  rw [reconstruct_matrix, ← Matrix.mul_assoc, (Factor.matrix_unitary Q).1,
    Matrix.one_mul]

theorem reconstruct_mem_source   :
    reconstruct Q C ∈ factorSource Q := by
  change admissible ((Factor.matrix Q)ᴴ * Factor.matrix (reconstruct Q C))
  rw [centered_reconstruct]
  exact admissible_cayley C.val (admissible_of_isSkew C.val C.property.2.1)

theorem centered_cayley_shared  (hU : U ∈ factorSource Q) :
    cayley ((Factor.matrix Q)ᴴ * Factor.matrix U) ∈ sharedSkewSpace s.size s.label :=
by
  have h := shared_factor_mul s.positive s.divides
    (shared_factor_conjTranspose (Factor.matrix_shared Q)) (Factor.matrix_shared U)
  have hm := cayley_mem_sharedMatrixSpace s.positive s.divides ⟨h.1,h.2.2⟩ hU
  exact ⟨hm.1,cayley_isSkew _ h.2.1 hU,hm.2⟩



@[simp] theorem factorCoordinates_reconstruct   :
    factorCoordinates Q (Factor.matrix (reconstruct Q C)) = C := by
  unfold factorCoordinates
  rw [centered_reconstruct,
    cayley_involutive C.val (admissible_of_isSkew C.val C.property.2.1)]
  exact modelProjection_inclusion C

theorem reconstruct_factorCoordinates  (hU : U ∈ factorSource Q) :
    reconstruct Q (factorCoordinates Q (Factor.matrix U)) = U := by
  apply Factor.matrix_injective
  rw [reconstruct_matrix, show (factorCoordinates Q (Factor.matrix U)).val = _ from
    modelProjection_val_of_mem s _ (centered_cayley_shared Q U hU), cayley_involutive _ hU,
    ← Matrix.mul_assoc, (Factor.matrix_unitary Q).2, Matrix.one_mul]

@[simp] theorem reconstruct_zero  : reconstruct Q 0 = Q := by
  apply Factor.matrix_injective
  simp only [reconstruct_matrix, Submodule.coe_zero, cayley_zero, Matrix.mul_one]



theorem factorCoordinates_smooth_at  
    (hA : admissible ((Factor.matrix Q)ᴴ * A)) :
    ContDiffAt ℝ ⊤ (factorCoordinates Q) A :=
  (modelProjection s).contDiff.contDiffAt.comp A
    (smooth_cayley_comp_at (smooth_mul_at contDiffAt_const contDiffAt_id) hA)

theorem reconstruct_matrix_smooth  :
    ContDiff ℝ ⊤ (fun C : Generator s => Factor.matrix (reconstruct Q C)) := by
  simp only [reconstruct_matrix]
  apply contDiff_iff_contDiffAt.mpr; intro C
  exact smooth_mul_at contDiffAt_const
    (smooth_cayley_comp_at (by fun_prop) (admissible_of_isSkew _ C.property.2.1))


@[fun_prop] theorem continuous_reconstruct  : Continuous (reconstruct Q) :=
  ((reconstruct_matrix_smooth Q).continuous.subtype_mk _).subtype_mk _

/-- A total extension on each side, with an open source and full linear target. -/
def factorPartialChart  : OpenPartialHomeomorph (Factor s) (Generator s) where
  toFun U := factorCoordinates Q (Factor.matrix U)
  invFun := reconstruct Q
  source := factorSource Q
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' C _ := reconstruct_mem_source Q C
  left_inv' U hU := reconstruct_factorCoordinates Q U hU
  right_inv' C _ := factorCoordinates_reconstruct Q C
  open_source := factorSource_open Q
  open_target := isOpen_univ
  continuousOn_toFun := by
    intro U hU
    exact ((factorCoordinates_smooth_at Q (Factor.matrix U) hU).continuousAt.comp
      Factor.continuous_matrix.continuousAt).continuousWithinAt
  continuousOn_invFun := (continuous_reconstruct Q).continuousOn


















end GS.MatrixGeometry
