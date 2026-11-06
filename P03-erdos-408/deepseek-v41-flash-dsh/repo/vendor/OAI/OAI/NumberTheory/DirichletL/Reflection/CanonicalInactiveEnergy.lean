module

public import OAI.NumberTheory.DirichletL.Reflection.CanonicalChoiceEnergy
public import OAI.NumberTheory.DirichletL.Reflection.InactiveSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff

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
