module
public import Mathlib.Tactic

public import Erdos821.P4Probe.FullProjection

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

def productAnova (w : ∀ i, α i → ℝ) (I S : Finset ι)
    (f : ProductSample α → ℂ) : ProductSample α → ℂ :=
  productFull w S (productAverage w (I \ S) f)

section
variable (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1) (I S : Finset ι) (i : ι) (hi : i ∉ I) (hS : S ⊆ I) (f : ProductSample α → ℂ)


include hsum in
lemma productAnova_empty    
      : productAnova w ∅ ∅ f = f := by
  rw [productAnova, Finset.sdiff_empty, productAverage_empty w hsum,
    productFull_empty w hsum]

include hsum hi hS in
lemma productAnova_insert_unselected  
         
          :
    productAnova w (insert i I) S f = productAverage w {i} (productAnova w I S f) := by
  have hiS : i ∉ S := fun h => hi (hS h)
  have hdiff : insert i I \ S = {i} ∪ (I \ S) := by
    grind
  have havg : productAverage w (insert i I \ S) f =
      productAverage w {i} (productAverage w (I \ S) f) := by
    funext x
    rw [productAverage_union w hsum {i} (I \ S), hdiff]
  unfold productAnova
  rw [havg, productFull_average_commute w hsum S {i}]

include hsum hi hS in
lemma productAnova_insert_selected  
         
          :
    productAnova w (insert i I) (insert i S) f =
      fun x => productAnova w I S f x - productAverage w {i} (productAnova w I S f) x := by
  have hiS : i ∉ S := fun h => hi (hS h)
  have hdiff : insert i I \ insert i S = I \ S := by
    grind
  unfold productAnova
  rw [hdiff, productFull_insert w hsum S i hiS]

include hsum in
lemma productAnova_energy    
        :
    (∑ S ∈ I.powerset, productSqNorm w (productAnova w I S f)) = productSqNorm w f := by
  induction I using Finset.induction_on with
  | empty =>
      simp only [Finset.powerset_empty, Finset.sum_singleton, productAnova_empty w hsum]
  | @insert i I hi hI =>
      rw [Finset.sum_powerset_insert hi, ← Finset.sum_add_distrib]
      trans ∑ S ∈ I.powerset, productSqNorm w (productAnova w I S f)
      · apply Finset.sum_congr rfl
        intro S hS
        rw [productAnova_insert_unselected w hsum I S i hi (Finset.mem_powerset.mp hS),
          productAnova_insert_selected w hsum I S i hi (Finset.mem_powerset.mp hS)]
        have he := productAverage_energy_split w hsum {i} (productAnova w I S f)
        linarith
      · exact hI

include hsum in
lemma productAnova_mean_zero  
         
    (hi : i ∈ S)  f  :
    productAverage w {i} (productAnova w I S f) = (fun _ => 0) :=
  productFull_mean_zero w hsum S i hi _

include hsum in
lemma productAnova_independent  
         
    (hi : i ∈ I) (hiS : i ∉ S)  f  :
    productAverage w {i} (productAnova w I S f) = productAnova w I S f := by
  have hin : i ∈ I \ S := Finset.mem_sdiff.mpr ⟨hi, hiS⟩
  have hu : {i} ∪ (I \ S) = I \ S := by
    apply Finset.union_eq_right.mpr
    simpa only [Finset.singleton_subset_iff] using hin
  unfold productAnova
  rw [← productFull_average_commute w hsum S {i}]
  congr 1
  funext x
  rw [productAverage_union w hsum {i} (I \ S), hu]

end

end
end Erdos821.P4Probe
