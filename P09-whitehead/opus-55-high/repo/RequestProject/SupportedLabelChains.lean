import RequestProject.CellComplex


/-! A finitely supported chain can be split by incidence labels.  The
boundary identity below requires homogeneity only at cells in its actual
support.  Thus it applies to a union of components inside a larger complex.
Unverified source. -/

open scoped Classical
namespace FiniteChains.Comb

theorem finsupp_filter_of_constant_label {I : Type u} {J : Type v}
    (label : I → J) j (c : I →₀ ℤ) k
    (hc : ∀ i, c i ≠ 0 → label i = j) :
    c.filter (label · = k) = if j = k then c else 0 := by
  ext i
  by_cases hjk : j = k
  · subst k
    by_cases hi : c i = 0
    · simp [Finsupp.filter_apply, hi]
    simp_all
  · rw [if_neg hjk]
    by_cases hi : c i = 0
    · simp [Finsupp.filter_apply, hi]
    simp_all

theorem supported_label_boundary {I : Type u} {J : Type v} {T : Type w}
    (d : (I →₀ ℤ) →ₗ[ℤ] (J →₀ ℤ)) (labelI : I → T) (labelJ : J → T)
    (old : I → Prop)
    (hd : ∀ i, old i → ∀ j, d (Finsupp.single i 1) j ≠ 0 → labelJ j = labelI i)
    c (hc : ∀ i ∈ c.support, old i) k :
    d (c.filter (labelI · = k)) = (d c).filter (labelJ · = k) := by
  have hs (i : I) (hi : i ∈ c.support) :
      d ((Finsupp.single i (c i)).filter (labelI · = k)) =
        (d (Finsupp.single i (c i))).filter (labelJ · = k) := by
    have hm : ∀ j, d (Finsupp.single i (c i)) j ≠ 0 → labelJ j = labelI i := by
      intro j hj
      apply hd i (hc i hi) j
      intro hz
      apply hj
      have hsingle : Finsupp.single i (c i) = (c i) • Finsupp.single i (1) := by simp
      rw [hsingle, map_smul]
      simp [hz]
    rw [finsupp_filter_of_constant_label labelJ _ _ k hm]
    aesop
  calc
    d (c.filter (labelI · = k)) =
        d ((∑ i ∈ c.support, Finsupp.single i (c i)).filter (labelI · = k)) := by
          rw [show (∑ i ∈ c.support, Finsupp.single i (c i)) = c from c.sum_single]
    _ = ∑ i ∈ c.support,
        d ((Finsupp.single i (c i)).filter (labelI · = k)) := by
          rw [Finsupp.filter_sum, map_sum]
    _ = ∑ i ∈ c.support,
        (d (Finsupp.single i (c i))).filter (labelJ · = k) :=
          Finset.sum_congr rfl hs
    _ = (d c).filter (labelJ · = k) := by
          grind [← Finsupp.filter_sum, ← map_sum, show (∑ i ∈ c.support, Finsupp.single i (c i)) = c from c.sum_single]

theorem finsupp_sum_label_filters
    (label : I → J) (c : I →₀ ℤ) :
    ∑ j ∈ c.support.image label, c.filter (label · = j) = c := by
  ext i
  by_cases hi : c i = 0
  · simp [Finsupp.filter_apply, hi]
  · have hm : label i ∈ c.support.image label :=
      by grind
    simp [Finsupp.finset_sum_apply, Finsupp.filter_apply]
    simp_all
