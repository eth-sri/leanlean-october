module

public import OAI.NumberTheory.DirichletL.Reflection.CanonicalChoiceEnergy
public import OAI.NumberTheory.DirichletL.Reflection.InactiveSource

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein
noncomputable section
universe v
variable {Nlevel : ActualEisensteinCubic.O}

lemma inactiveRows_mem {σ φ : Type*} [Fintype σ] [DecidableEq σ]
    (rows : Finset (Ideal ActualEisensteinCubic.O)) (lists : σ→Finset (Ideal ActualEisensteinCubic.O)) (T : Finset σ)
    (FF : φ→Ideal ActualEisensteinCubic.O) (b : ∀ i : {i // i∉T},lists i.val) (K : Ideal ActualEisensteinCubic.O) :
    K∈inactiveRowSet rows lists T FF b ↔ K∈rows ∧
      IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠FF j :=
  Finset.mem_filter

end
end SevenEighths.InverseReflectedPhase

end OAI
