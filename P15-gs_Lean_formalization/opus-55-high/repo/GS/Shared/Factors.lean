module

public import GS.Shared.Algebra

@[expose] public section

/-! Compact groups of repeated physical unitary blocks. -/

noncomputable section
open Matrix
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- A valid complete-block layout and arbitrary within-layer sharing labels. -/
structure Pattern (𝕜 : Type*) (n : ℕ) where
  size : ℕ
  positive : 0 < size
  divides : size ∣ n
  label : ℕ → ℕ

section
variable (s : Pattern 𝕜 n)
/-- Entry equalities define a subgroup of the unitary group. -/
def Pattern.subgroup : Subgroup (unitaryGroup (Fin n) 𝕜) where
  carrier := {A | A.1 ∈ sharedMatrixSpace s.size s.label}
  one_mem' := one_mem_sharedMatrixSpace _ _
  mul_mem' := mul_mem_sharedMatrixSpace s.positive s.divides
  inv_mem' hA := ⟨hA.1.conjTranspose, hA.2.conjTranspose⟩

abbrev Factor := ↥s.subgroup
abbrev Generator := ↥(sharedSkewSpace (𝕜 := 𝕜) (n := n) s.size s.label)

end

namespace Factor
variable {s : Pattern 𝕜 n}

def matrix (A : Factor s) : 𝕄 := A.1.1

@[simp] theorem matrix_one : matrix (1 : Factor s) = 1 := rfl

section
variable (A : Factor s)
theorem matrix_unitary : Uni (matrix A) := uni_iff.2 A.1.2

theorem matrix_shared : SharedFactor s.size s.label (matrix A) :=
  ⟨A.2.1, A.matrix_unitary, A.2.2⟩

end

theorem matrix_injective : Function.Injective (matrix : Factor s → 𝕄) := fun _ _ h => by
  aesop

theorem continuous_matrix : Continuous (matrix : Factor s → 𝕄) :=
  continuous_subtype_val.comp continuous_subtype_val

section
variable (A : 𝕄) (hA : SharedFactor s.size s.label A)
def ofMatrix : Factor s :=
  ⟨⟨A, uni_iff.1 hA.2.1⟩, hA.1, hA.2.2⟩

@[simp] theorem matrix_ofMatrix :
    matrix (ofMatrix A hA) = A := rfl

end

end Factor

instance factorCompactSpace (s : Pattern 𝕜 n) : CompactSpace (Factor s) :=
  have h : IsCompact (unitaryGroup (Fin n) 𝕜 : Set 𝕄) :=
    (isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_closedBall (0 : 𝕜) 1).of_isClosed_subset
      (isClosed_unitary (R := 𝕄)) fun A h i j => by simpa using entry_norm_bound_of_unitary h i j
  have := isCompact_iff_compactSpace.mp h
  isCompact_iff_compactSpace.mp
    ((isClosed_sharedMatrixSpace s.size s.label).preimage continuous_subtype_val).isCompact

/-- The two layers can use unrelated sharing maps and block sizes. -/
abbrev Factors (right left : Pattern 𝕜 n) := Factor left × Factor right

end GS.Shared
