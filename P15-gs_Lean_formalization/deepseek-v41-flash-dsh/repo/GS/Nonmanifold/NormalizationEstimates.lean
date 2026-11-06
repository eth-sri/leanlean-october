module

public import GS.Continuation.ExponentialChart
public import GS.Continuation.ExponentialBasics

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Concrete steps toward uniform coverage of the original family

These estimates formalize the normalized scalar error and the integer cocycle
in the manuscript. The existence of all normalized representatives and small
skew logarithms is still a separate obligation; this file does not assume a
local-coverage or nonmanifold theorem under another name.
-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
open scoped BigOperators
namespace GS.Nonmanifold

/-- Orthogonality of exp H forces H to be skew on a symmetric injectivity domain.
Only local injectivity is used; existence of H is not asserted here. -/
theorem skew_of_exp_orthogonal {q : ℕ} (V : Set (Mat q))
    (hinj : Set.InjOn (@matrixExp q) V) (H : Mat q)
    (ht : Hᵀ ∈ V) (hn : -H ∈ V) (hH : Orthogonal (matrixExp H)) : IsSkew H := by
  apply hinj ht hn
  rw [matrixExp_transpose]
  calc
    (matrixExp H)ᵀ = (matrixExp H)ᵀ * (matrixExp H * matrixExp (-H)) := by
      rw [matrixExp_mul_neg, Matrix.mul_one]
    _ = matrixExp (-H) := by rw [← Matrix.mul_assoc, hH.1, Matrix.one_mul]

/-- The symmetric chart restriction is built explicitly from the existing
inverse-function-theorem result, rather than passed as an extra assumption. -/
theorem exists_open_exp_skew_detection (q : ℕ) :
    ∃ V : Set (Mat q), IsOpen V ∧ (0:Mat q) ∈ V ∧
      ∀ H ∈ V, Orthogonal (matrixExp H) → IsSkew H := by
  obtain ⟨U,hU,h0,hinj⟩ := exists_open_matrixExp_injective q
  let V : Set (Mat q) := (fun H : Mat q => Hᵀ) ⁻¹' U ∩
    (fun H : Mat q => -H) ⁻¹' U
  have hV : IsOpen V :=
    (hU.preimage (by fun_prop)).inter (hU.preimage (by fun_prop))
  refine ⟨V,hV,?_,?_⟩
  · exact ⟨by simpa using h0, by simpa using h0⟩
  · intro H hH ho
    exact skew_of_exp_orthogonal U hinj H hH.1 hH.2 ho

end GS.Nonmanifold
