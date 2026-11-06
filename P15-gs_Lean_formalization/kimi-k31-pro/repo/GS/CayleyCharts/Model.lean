module

public import GS.CayleyCharts.Algebra
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
namespace GS.CayleyCharts
variable {n : ℕ}

def modelSpace (block : Fin n → ℕ) : Submodule ℝ (Mat n) where
  carrier := {A | Supported block A ∧ GS.IsSkew A}
  zero_mem' := by constructor <;> simp [Supported, GS.IsSkew]
  add_mem' := by
    intro A B hA hB
    refine ⟨hA.1.add hB.1, ?_⟩
    change (A + B)ᵀ = -(A + B)
    rw [Matrix.transpose_add, hA.2, hB.2, neg_add]
  smul_mem' := by
    intro c A hA
    refine ⟨Supported.smul c hA.1, ?_⟩
    change (c • A)ᵀ = -(c • A)
    rw [Matrix.transpose_smul, show Aᵀ = -A from hA.2, smul_neg]

abbrev Model (block : Fin n → ℕ) := ↥(modelSpace block)

theorem admissible_model {block : Fin n → ℕ} (x : Model block) :
    admissible x.val := admissible_of_isSkew x.val x.property.2

def modelInclusion (block : Fin n → ℕ) : Model block →L[ℝ] Mat n :=
  (modelSpace block).subtypeL

end GS.CayleyCharts
