module

public import GS.UnitarySharing.Factors
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A Cayley atlas on the actual shared factor group

The chart model is the concrete subspace of supported tied skew-Hermitian matrices.
The source uses the existing matrix topology, and its inverse is defined on
the entire model.  Transition functions are restrictions of rational ambient
matrix formulas.  This establishes the factor manifold, not yet the shared
matrix-orbit manifold or its tangent bundle.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open scoped Topology Manifold
namespace GS.UnitarySharing
variable {n : ℕ} {s : Pattern n}

/-- A total continuous linear extension of the shared chart coordinates. -/
def modelProjection (s : Pattern n) : CMat n →L[ℝ] Generator s :=
  ({ toFun := fun A => ⟨cFrobProjection (sharedSkewSpace s.size s.label) A,
        cFrobProjection_mem _ _⟩
     map_add' := by
       intro A B
       apply Subtype.ext
       exact map_add _ A B
     map_smul' := by
       intro a A
       apply Subtype.ext
       exact map_smul _ a A } : CMat n →ₗ[ℝ] Generator s).toContinuousLinearMap

theorem modelProjection_val_of_mem (s : Pattern n) (A : CMat n)
    (hA : A ∈ sharedSkewSpace s.size s.label) : (modelProjection s A).val = A :=
  cFrobProjection_of_mem _ _ hA

@[simp] theorem modelProjection_inclusion (C : Generator s) :
    modelProjection s C.val = C := by
  apply Subtype.ext
  exact modelProjection_val_of_mem s C.val C.property

/-- Open neighbourhood of Q inside the inherited shared-factor topology. -/
def factorSource (Q : Factor s) : Set (Factor s) :=
  {U | admissible ((Factor.matrix Q)ᴴ * Factor.matrix U)}

def factorCoordinates (Q : Factor s) (A : CMat n) : Generator s :=
  modelProjection s (cayley ((Factor.matrix Q)ᴴ * A))

/-- All shared skew coordinates reconstruct valid shared unitary factors. -/
def reconstruct (Q : Factor s) (C : Generator s) : Factor s :=
  Q * Factor.ofMatrix (cayley C.val) (cayley_shared s.positive s.divides C.property)

@[simp] theorem reconstruct_matrix (Q : Factor s) (C : Generator s) :
    Factor.matrix (reconstruct Q C) = Factor.matrix Q * cayley C.val := rfl

theorem factorSource_open (Q : Factor s) : IsOpen (factorSource Q) :=
  admissible_open.preimage
    (GS.UnitaryManifold.continuous_matrix_product continuous_const Factor.continuous_matrix)

@[simp] theorem base_mem_factorSource (Q : Factor s) : Q ∈ factorSource Q := by
  change admissible ((Factor.matrix Q)ᴴ * Factor.matrix Q)
  rw [(Factor.matrix_unitary Q).1]
  exact admissible_one

theorem centered_reconstruct (Q : Factor s) (C : Generator s) :
    (Factor.matrix Q)ᴴ * Factor.matrix (reconstruct Q C) = cayley C.val := by
  rw [reconstruct_matrix, ← Matrix.mul_assoc, (Factor.matrix_unitary Q).1,
    Matrix.one_mul]

theorem reconstruct_mem_source (Q : Factor s) (C : Generator s) :
    reconstruct Q C ∈ factorSource Q := by
  change admissible ((Factor.matrix Q)ᴴ * Factor.matrix (reconstruct Q C))
  rw [centered_reconstruct]
  exact admissible_cayley C.val (admissible_of_isSkew C.val C.property.2.1)

theorem centered_cayley_shared (Q U : Factor s) (hU : U ∈ factorSource Q) :
    cayley ((Factor.matrix Q)ᴴ * Factor.matrix U) ∈ sharedSkewSpace s.size s.label :=
  cayley_sharedSkew s.positive s.divides
    (shared_factor_mul s.positive s.divides
      (shared_factor_conjTranspose (Factor.matrix_shared Q)) (Factor.matrix_shared U)) hU

theorem factorCoordinates_val (Q U : Factor s) (hU : U ∈ factorSource Q) :
    (factorCoordinates Q (Factor.matrix U)).val =
      cayley ((Factor.matrix Q)ᴴ * Factor.matrix U) :=
  modelProjection_val_of_mem s _ (centered_cayley_shared Q U hU)

@[simp] theorem factorCoordinates_reconstruct (Q : Factor s) (C : Generator s) :
    factorCoordinates Q (Factor.matrix (reconstruct Q C)) = C := by
  unfold factorCoordinates
  rw [centered_reconstruct,
    cayley_involutive C.val (admissible_of_isSkew C.val C.property.2.1)]
  exact modelProjection_inclusion C

theorem reconstruct_factorCoordinates (Q U : Factor s) (hU : U ∈ factorSource Q) :
    reconstruct Q (factorCoordinates Q (Factor.matrix U)) = U := by
  apply Factor.matrix_injective
  rw [reconstruct_matrix, factorCoordinates_val Q U hU, cayley_involutive _ hU,
    ← Matrix.mul_assoc, (Factor.matrix_unitary Q).2, Matrix.one_mul]

@[simp] theorem reconstruct_zero (Q : Factor s) : reconstruct Q 0 = Q := by
  apply Factor.matrix_injective
  simp only [reconstruct_matrix, Submodule.coe_zero, cayley_zero, Matrix.mul_one]

theorem factorCoordinates_smooth_at (Q : Factor s) (A : CMat n)
    (hA : admissible ((Factor.matrix Q)ᴴ * A)) :
    ContDiffAt ℝ ⊤ (factorCoordinates Q) A :=
  (modelProjection s).contDiff.contDiffAt.comp A
    (smooth_cayley_comp_at (smooth_mul_at contDiffAt_const contDiffAt_id) hA)

theorem reconstruct_matrix_smooth (Q : Factor s) :
    ContDiff ℝ ⊤ (fun C : Generator s => Factor.matrix (reconstruct Q C)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro C
  exact smooth_mul_at contDiffAt_const
    (smooth_cayley_comp_at
      (sharedSkewSpace (n := n) s.size s.label).subtypeL.contDiff.contDiffAt
      (admissible_of_isSkew C.val C.property.2.1))

theorem continuous_reconstruct (Q : Factor s) : Continuous (reconstruct Q) :=
  ((reconstruct_matrix_smooth Q).continuous.subtype_mk _).subtype_mk _

/-- A total extension on each side, with an open source and full linear target. -/
def factorPartialChart (Q : Factor s) : OpenPartialHomeomorph (Factor s) (Generator s) where
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

end GS.UnitarySharing
