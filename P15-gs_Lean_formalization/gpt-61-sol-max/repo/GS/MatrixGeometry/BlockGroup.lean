import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import GS.MatrixGeometry.Base
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
namespace GS.MatrixBase
variable {𝕜 : Type} [RCLike 𝕜]


variable (block : Fin n → ℕ)

/-- Unitary matrices with the manuscript's exact zero pattern. -/
abbrev BlockU (𝕜 : Type) [RCLike 𝕜] (block : Fin n → ℕ) :=
  {A : KMat 𝕜 n // CSupported block A ∧ Unitary A}

instance blockUGroup (block : Fin n → ℕ) : Group (BlockU 𝕜 block) where
  one := ⟨1, GS.MatrixBase.CSupported.one, GS.MatrixBase.Unitary.one⟩
  mul A B := ⟨A.val * B.val, A.property.1.mul B.property.1,
    A.property.2.mul B.property.2⟩
  inv A := ⟨A.valᴴ, A.property.1.conjTranspose, A.property.2.conjTranspose⟩
  mul_assoc A B C := Subtype.ext (Matrix.mul_assoc A.val B.val C.val)
  one_mul A := Subtype.ext (Matrix.one_mul A.val)
  mul_one A := Subtype.ext (Matrix.mul_one A.val)
  inv_mul_cancel A := Subtype.ext A.property.2.1





/-- Matrix multiplication is continuous for the inherited finite-product topology. -/
theorem continuous_matrix_product {X : Type*} [TopologicalSpace X]
    {A B : X → KMat 𝕜 n} (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => A x * B x) := by
  fun_prop

theorem continuous_matrix_conjTranspose {X : Type*} [TopologicalSpace X]
    {A : X → KMat 𝕜 n} (hA : Continuous A) :
    Continuous (fun x => (A x)ᴴ) := by
  fun_prop

instance blockUContinuousMul (block : Fin n → ℕ) :
    ContinuousMul (BlockU 𝕜 block) where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact continuous_matrix_product (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd)

instance blockUContinuousInv (block : Fin n → ℕ) :
    ContinuousInv (BlockU 𝕜 block) where
  continuous_inv := by
    apply Continuous.subtype_mk
    exact continuous_matrix_conjTranspose continuous_subtype_val

/-- The two verified continuity instances equip the actual block group with
mathlib's topological-group structure. -/
instance blockUTopologicalGroup (block : Fin n → ℕ) :
    IsTopologicalGroup (BlockU 𝕜 block) where

theorem closed_supported  :
    IsClosed {A : KMat 𝕜 n | CSupported block A} := by
  simp only [CSupported, Set.setOf_forall]
  repeat' (apply isClosed_iInter; intro)
  exact isClosed_eq (by fun_prop) continuous_const

theorem closed_unitary : IsClosed {A : KMat 𝕜 n | Unitary A} := isClosed_unitary

theorem compact_blockU_set :
    IsCompact {A : KMat 𝕜 n | CSupported block A ∧ Unitary A} := by
  apply (isCompact_closedBall (0 : KMat 𝕜 n) 1).of_isClosed_subset
    ((closed_supported block).inter closed_unitary)
  intro A hA
  simpa only [Metric.mem_closedBall,dist_zero_right] using
    entrywise_sup_norm_bound_of_unitary hA.2

instance blockUCompactSpace (block : Fin n → ℕ) : CompactSpace (BlockU 𝕜 block) :=
  isCompact_iff_compactSpace.mp (compact_blockU_set block)


end GS.MatrixBase
