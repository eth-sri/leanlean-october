module

public import OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailKernel

@[expose] public section

namespace OAI



open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson


theorem norm_tsum_of_finite_bound {α : Type*} (f : α→ℂ) (hf : Summable f)  B 
    (hb : ∀F : Finset α,‖∑h∈F,f h‖≤B) : ‖∑'h,f h‖≤B := le_of_tendsto hf.hasSum.norm (Filter.Eventually.of_forall hb)

end SevenEighths.InverseInitialHighFrequencyTail



end OAI
