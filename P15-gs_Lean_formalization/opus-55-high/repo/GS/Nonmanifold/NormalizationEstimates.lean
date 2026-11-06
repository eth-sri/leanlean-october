module

public import GS.Continuation.ExponentialChart
public import GS.Continuation.ExponentialBasics

@[expose] public section


/-!
# Concrete steps toward uniform coverage of the original family

These estimates formalize the normalized scalar error and the integer cocycle
in the manuscript. The existence of all normalized representatives and small
skew logarithms is still a separate obligation; this file does not assume a
local-coverage or nonmanifold theorem under another name.
-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
namespace GS.Nonmanifold

theorem exists_open_exp_skew_detection (q : ℕ) :
    ∃ V : Set (Mat q), IsOpen V ∧ (0:Mat q) ∈ V ∧
      ∀ H ∈ V, Orthogonal (matrixExp H) → IsSkew H := by
  obtain ⟨U,hU,h0,hinj⟩ := exists_open_matrixExp_injective q
  refine ⟨(·ᵀ) ⁻¹' U ∩ (-·) ⁻¹' U, (hU.preimage (by fun_prop)).inter (hU.preimage (by fun_prop)), by aesop, fun H hH ho => hinj hH.1 hH.2 ?_⟩
  rw [matrixExp_transpose, ← Matrix.mul_one (matrixExp H)ᵀ, ← matrixExp_mul_neg H, ← Matrix.mul_assoc, ho.1, Matrix.one_mul]

end GS.Nonmanifold
