module

public import OAI.NumberTheory.DirichletL.Reflection.Functions
public import OAI.NumberTheory.DirichletL.Reflection.Family

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
noncomputable section
noncomputable local instance sectorIndependentFinite (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] : Fintype (ActualEisensteinCubic.O ⧸ P) := Fintype.ofFinite _

theorem frozenCore_transport {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → ActualEisensteinCubic.O} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}) (c : ActualEisensteinCubic.O) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) :
    frozenCore (fun i => hp (f i)) (fun i => hg (f i)) c (fun i => j (f i)) F =
      frozenCore hp hg c j (F.image f) := by
  unfold frozenCore
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf F i,Finset.prod_image hf.injOn]

end
end SevenEighths.InverseReflectedPhase

end OAI
