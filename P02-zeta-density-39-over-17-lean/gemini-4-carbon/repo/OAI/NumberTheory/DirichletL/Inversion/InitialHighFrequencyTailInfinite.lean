module
public import OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailKernel

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O"=>ActualEisensteinCubic.O

theorem norm_tsum_of_finite_bound {α : Type*} (f : α→ℂ) (hf : Summable f) (B : ℝ)
    (hb : ∀F : Finset α,‖∑h∈F,f h‖≤B) : ‖∑'h,f h‖≤B := by
  exact le_of_tendsto hf.hasSum.norm (Filter.Eventually.of_forall hb)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
