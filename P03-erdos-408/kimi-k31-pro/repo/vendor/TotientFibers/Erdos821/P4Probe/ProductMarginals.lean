module

public import Erdos821.P4Probe.ProductAverages

@[expose] public section

open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

abbrev PartialSample (S : Finset ι) (α : ι → Type*) := ∀ i : {i // i ∈ S}, α i.val

def partialProductWeight (w : ∀ i, α i → ℝ) (S : Finset ι)
    (a : PartialSample S α) : ℝ := ∏ i, w i.val (a i)

omit [(i : ι) → Fintype (α i)] in
lemma productWeight_split (w : ∀ i, α i → ℝ) (S : Finset ι) (y : ProductSample α) :
    productWeight w y = partialProductWeight w S (fun i => y i.val) *
      productWeight (fun i : {i // i ∉ S} => w i.val) (fun i => y i.val) := by
  convert (Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)
    (fun i => w i (y i))).symm using 1 <;> congr! 2
  unfold partialProductWeight
  congr!

end
end Erdos821.P4Probe
