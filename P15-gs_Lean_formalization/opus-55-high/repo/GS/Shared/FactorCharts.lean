module

public import GS.Shared.Factors
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

@[expose] public section


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
open Matrix
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {s : Pattern 𝕜 n}

section
variable (s : Pattern 𝕜 n)
/-- A total continuous linear extension of the shared chart coordinates. -/
def modelProjection : 𝕄 →L[ℝ] Generator s :=
  ({ toFun := fun A => ⟨proj (sharedSkewSpace s.size s.label) A,
        proj_mem _ _⟩
     map_add' := by
       simp
     map_smul' := by
       simp } : 𝕄 →ₗ[ℝ] Generator s).toContinuousLinearMap


theorem modelProjection_val_of_mem (A : 𝕄)
    (hA : A ∈ sharedSkewSpace s.size s.label) : (modelProjection s A).val = A :=
  proj_of_mem _ _ hA

end

@[simp] theorem modelProjection_inclusion (C : Generator s) :
    modelProjection s C.val = C := by
  apply Subtype.ext
  exact modelProjection_val_of_mem s C.val C.property

section
variable (Q : Factor s)
/-- Open neighbourhood of Q inside the inherited shared-factor topology. -/
def factorSource : Set (Factor s) :=
  {U | admissible ((Factor.matrix Q)ᴴ * Factor.matrix U)}

def factorCoordinates (A : 𝕄) : Generator s :=
  modelProjection s (cayley ((Factor.matrix Q)ᴴ * A))

/-- All shared skew coordinates reconstruct valid shared unitary factors. -/
def reconstruct (C : Generator s) : Factor s :=
  Q * Factor.ofMatrix (cayley C.val) (cayley_shared s.positive s.divides C.property)

@[simp] theorem reconstruct_matrix (C : Generator s) :
    Factor.matrix (reconstruct Q C) = Factor.matrix Q * cayley C.val := rfl

theorem factorSource_open : IsOpen (factorSource Q) :=
  admissible_open.preimage
    (continuous_const.mul Factor.continuous_matrix)

@[simp] theorem base_mem_factorSource : Q ∈ factorSource Q := by
  change admissible ((Factor.matrix Q)ᴴ * Factor.matrix Q)
  rw [(Factor.matrix_unitary Q).1]
  exact admissible_one

theorem centered_reconstruct (C : Generator s) :
    (Factor.matrix Q)ᴴ * Factor.matrix (reconstruct Q C) = cayley C.val := by
  rw [reconstruct_matrix, ← Matrix.mul_assoc, (Factor.matrix_unitary Q).1,
    Matrix.one_mul]

theorem reconstruct_mem_source (C : Generator s) :
    reconstruct Q C ∈ factorSource Q := by
  change admissible ((Factor.matrix Q)ᴴ * Factor.matrix (reconstruct Q C))
  rw [centered_reconstruct]
  exact admissible_cayley (admissible_of_isSkew C.property.2.1)

end

section
variable (Q U : Factor s)
theorem centered_cayley_shared (hU : U ∈ factorSource Q) :
    cayley ((Factor.matrix Q)ᴴ * Factor.matrix U) ∈ sharedSkewSpace s.size s.label :=
  cayley_sharedSkew s.positive s.divides
    (shared_factor_mul s.positive s.divides
      (shared_factor_conjTranspose (Factor.matrix_shared Q)) (Factor.matrix_shared U)) hU

theorem factorCoordinates_val (hU : U ∈ factorSource Q) :
    (factorCoordinates Q (Factor.matrix U)).val =
      cayley ((Factor.matrix Q)ᴴ * Factor.matrix U) :=
  modelProjection_val_of_mem s _ (centered_cayley_shared Q U hU)

end

@[simp] theorem factorCoordinates_reconstruct (Q : Factor s) (C : Generator s) :
    factorCoordinates Q (Factor.matrix (reconstruct Q C)) = C := by
  unfold factorCoordinates
  rw [centered_reconstruct,
    cayley_involutive (admissible_of_isSkew C.property.2.1)]
  simp

theorem reconstruct_factorCoordinates (Q U : Factor s) (hU : U ∈ factorSource Q) :
    reconstruct Q (factorCoordinates Q (Factor.matrix U)) = U := by
  apply Factor.matrix_injective
  rw [reconstruct_matrix, factorCoordinates_val Q U hU, cayley_involutive hU,
    ← Matrix.mul_assoc, (Factor.matrix_unitary Q).2, Matrix.one_mul]

section
variable (Q : Factor s)
@[simp] theorem reconstruct_zero : reconstruct Q 0 = Q := by
  apply Factor.matrix_injective
  simp only [reconstruct_matrix, Submodule.coe_zero, cayley_zero, Matrix.mul_one]


theorem factorCoordinates_smooth_at (A : 𝕄)
    (hA : admissible ((Factor.matrix Q)ᴴ * A)) :
    ContDiffAt ℝ ⊤ (factorCoordinates Q) A :=
  (modelProjection s).contDiff.contDiffAt.comp A
    (smooth_cayley_comp_at (smooth_mul_at contDiffAt_const contDiffAt_id) hA)

theorem reconstruct_matrix_smooth :
    ContDiff ℝ ⊤ (fun C : Generator s => Factor.matrix (reconstruct Q C)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro C
  exact smooth_mul_at contDiffAt_const
    (smooth_cayley_comp_at
      (contDiff_val _).contDiffAt
      (admissible_of_isSkew C.property.2.1))

theorem continuous_reconstruct : Continuous (reconstruct Q) :=
  ((reconstruct_matrix_smooth Q).continuous.subtype_mk _).subtype_mk _

/-- A total extension on each side, with an open source and full linear target. -/
def factorPartialChart : OpenPartialHomeomorph (Factor s) (Generator s) where
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





end

section Source
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]



end Source





end GS.Shared
