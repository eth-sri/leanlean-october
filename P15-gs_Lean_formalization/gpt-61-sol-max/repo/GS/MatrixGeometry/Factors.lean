import GS.MatrixGeometry.Base

import GS.MatrixGeometry.Sharing




/-!
# Compact groups of repeated physical unitary blocks

`Pattern` records only the block size, its positivity/divisibility, and the
within-layer sharing labels.  `Factor` is a closed subgroup of the existing
block unitary group, with the inherited matrix topology.  In particular,
no group law or topology is imposed on a parametrized image by fiat.
-/

open Matrix GS.MatrixBase
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]

/-- A valid complete-block layout and arbitrary within-layer sharing labels.
Unused labels are allowed; different layers have independent patterns. -/
structure Pattern (𝕜 : Type) (n : ℕ) where
  size : ℕ
  positive : 0 < size
  divides : size ∣ n
  label : ℕ → ℕ

namespace Pattern

def block (s : Pattern 𝕜 n) (i : Fin n) : ℕ := i.val / s.size

/-- Actual entry equalities define a subgroup of the already constructed
block unitary group. -/
def subgroup (s : Pattern 𝕜 n) : Subgroup (GS.MatrixBase.BlockU 𝕜 s.block) where
  carrier := {A | TiedEntries s.size s.label A.val}
  one_mem' := TiedEntries.one s.size s.label
  mul_mem' := by
    intro A B hA hB
    exact TiedEntries.mul s.positive s.divides A.property.1 hA hB
  inv_mem' := by
    intro A hA
    exact hA.conjTranspose

theorem subgroup_isClosed (s : Pattern 𝕜 n) :
    IsClosed (s.subgroup : Set (GS.MatrixBase.BlockU 𝕜 s.block)) :=
  (isClosed_tiedEntries s.size s.label).preimage continuous_subtype_val

end Pattern

abbrev Factor (s : Pattern 𝕜 n) := ↥s.subgroup
abbrev Generator (s : Pattern 𝕜 n) := ↥(sharedSkewSpace (𝕜 := 𝕜) (n := n) s.size s.label)

namespace Factor
variable {s : Pattern 𝕜 n}

/-- The original finite matrix, through the two inherited subtypes. -/
def matrix (A : Factor s) : KMat 𝕜 n := A.val.val

@[simp] theorem matrix_inv {s : Pattern 𝕜 n} (Q : Factor s) :
    Factor.matrix Q⁻¹ = (Factor.matrix Q)ᴴ := rfl


@[simp] theorem matrix_one : matrix (1 : Factor s) = 1 := rfl



theorem matrix_shared (A : Factor s) : SharedUnitaryFactor s.size s.label (matrix A) :=
  ⟨A.val.property.1, A.val.property.2, A.property⟩

theorem matrix_unitary (A : Factor s) : GS.MatrixBase.Unitary (matrix A) := A.val.property.2

theorem matrix_injective : Function.Injective (matrix : Factor s → KMat 𝕜 n) := by
  intro A B h
  apply Subtype.ext
  exact Subtype.ext h

theorem continuous_matrix : Continuous (matrix : Factor s → KMat 𝕜 n) :=
  continuous_subtype_val.comp continuous_subtype_val

def ofMatrix (A : KMat 𝕜 n) (hA : SharedUnitaryFactor s.size s.label A) : Factor s :=
  ⟨⟨A, hA.1, hA.2.1⟩, hA.2.2⟩

end Factor

instance factorCompactSpace (s : Pattern 𝕜 n) : CompactSpace (Factor s) :=
  isCompact_iff_compactSpace.mp s.subgroup_isClosed.isCompact

/-- The two layers can use unrelated sharing maps and block sizes. -/
abbrev Factors (right left : Pattern 𝕜 n) := Factor left × Factor right

end GS.MatrixGeometry
