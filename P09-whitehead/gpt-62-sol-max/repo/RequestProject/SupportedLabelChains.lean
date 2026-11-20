module

public import RequestProject.CellComplex

@[expose] public section

/-! A finitely supported chain can be split by incidence labels.  The
boundary identity below requires homogeneity only at cells in its actual
support.  Thus it applies to a union of components inside a larger complex.
Unverified source. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb
universe u v w

theorem finsupp_filter_of_constant_label {I : Type u} {J : Type v}
    (label : I → J) (j : J) (c : I →₀ ℤ) (k : J)
    (hc : ∀ i, c i ≠ 0 → label i = j) :
    c.filter (fun i => label i = k) = if j = k then c else 0 := by
  ext i
  by_cases hj : j = k <;> by_cases hi : c i = 0 <;>
    simp [Finsupp.filter_apply, hj, hi, hc i]

/-- Filtering to one label leaves only coefficients allowed by that label. -/
theorem filter_supported {I : Type*} {p q r : I → Prop} [DecidablePred p]
    (c : I →₀ ℤ) (hc : ∀ i ∈ c.support, q i) (h : ∀ i, q i → p i → r i) :
    ∀ i, ¬ r i → c.filter p i = 0 := by
  intro i hi
  by_contra hn
  have hm := Finsupp.mem_support_iff.mpr hn
  rw [Finsupp.support_filter, Finset.mem_filter] at hm
  exact hi (h i (hc i hm.1) hm.2)

theorem supported_label_boundary {I : Type u} {J : Type v} {T : Type w}
    (d : (I →₀ ℤ) →ₗ[ℤ] (J →₀ ℤ)) (labelI : I → T) (labelJ : J → T)
    (old : I → Prop)
    (hd : ∀ i, old i → ∀ j, d (Finsupp.single i 1) j ≠ 0 → labelJ j = labelI i)
    (c : I →₀ ℤ) (hc : ∀ i ∈ c.support, old i) (k : T) :
    d (c.filter (fun i => labelI i = k)) = (d c).filter (fun j => labelJ j = k) := by
  rw [← c.sum_single]
  simp only [Finsupp.sum, Finsupp.filter_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hm (j : J) (hj : d (Finsupp.single i (c i)) j ≠ 0) : labelJ j = labelI i := by
    apply hd i (hc i hi) j
    contrapose! hj
    rw [← Finsupp.smul_single_one i (c i), map_smul]
    simp [hj]
  rw [finsupp_filter_of_constant_label labelJ (labelI i) _ k hm]
  by_cases hik : labelI i = k <;> simp [hik]

theorem finsupp_sum_label_filters {I : Type u} {J : Type v}
    (label : I → J) (c : I →₀ ℤ) :
    ∑ j ∈ c.support.image label, c.filter (fun i => label i = j) = c := by
  ext i
  by_cases hi : c i = 0
  · simp [Finsupp.filter_apply, hi]
  · have hm := Finset.mem_image_of_mem label (Finsupp.mem_support_iff.mpr hi)
    simp [Finsupp.finsetSum_apply, Finsupp.filter_apply, hm]

end FiniteChains.Comb
