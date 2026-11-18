module

public import OAI.NumberTheory.DirichletL.Reflection.OriginalBranchSum
public import OAI.NumberTheory.DirichletL.Reflection.LiteralNormalized
public import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
public import OAI.NumberTheory.DirichletL.Reflection.CountBudget
public import OAI.NumberTheory.DirichletL.Reflection.FullEnergyBasic
public import OAI.NumberTheory.DirichletL.Reflection.ActualSizeCaps
public import OAI.NumberTheory.DirichletL.Reflection.GlobalEnergy
public import OAI.NumberTheory.DirichletL.Reflection.TupleMembers
public import OAI.NumberTheory.DirichletL.Reflection.CanonicalParameters
public import OAI.NumberTheory.DirichletL.Reflection.OriginalCellBounds
public import OAI.NumberTheory.DirichletL.Reflection.DyadCompletionEnergy
public import OAI.NumberTheory.DirichletL.Reflection.DyadBudget
public import OAI.NumberTheory.DirichletL.Reflection.MemberChoiceTransport
public import OAI.NumberTheory.DirichletL.Reflection.InactiveSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

lemma inactiveRows_mem {σ φ : Type*} [Fintype σ] [DecidableEq σ]
    (rows : Finset (Ideal Eis)) (lists : σ→Finset (Ideal Eis)) (T : Finset σ)
    (FF : φ→Ideal Eis) (b : ∀ i : {i // i∉T},lists i.val) (K : Ideal Eis) :
    K∈inactiveRowSet rows lists T FF b ↔ K∈rows ∧
      IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠FF j := by
  exact Finset.mem_filter

end
end SevenEighths.InverseReflectedPhase

end OAI
