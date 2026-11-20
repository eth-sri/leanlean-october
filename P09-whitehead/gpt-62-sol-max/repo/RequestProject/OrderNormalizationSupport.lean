module

public import RequestProject.OrderThreeNormalization

@[expose] public section

/-! Normalization preserves the actual vertex tuples in the support of finite chains. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem normalizeOrdChain2_support (z : OrdTri P →₀ ℤ) (t : StrictOrdTri P)
    (ht : t ∈ (normalizeOrdChain2 z).support) :
    ∃ a ∈ z.support, a.1 = t.1 := by
  rw [Finsupp.mem_support_iff] at ht
  exact ⟨(strictOrderIncl P).onF t, Finsupp.mem_support_iff.mpr ht, rfl⟩

/-- A surviving normalized simplex has the vertices of an image simplex from the support. -/
theorem normalizeOrdChain2_image_support {X : Complex2} (f : Hom X (orderCx P))
    (z : X.F →₀ ℤ) {t : StrictOrdTri P}
    (ht : t ∈ (normalizeOrdChain2 (chain2 f z)).support) :
    ∃ a ∈ z.support, (f.onF a).1 = t.1 := by
  classical
  obtain ⟨b, hb, he⟩ := normalizeOrdChain2_support _ _ ht
  change b ∈ (Finsupp.mapDomain f.onF z).support at hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hb)
  exact ⟨a, ha, he⟩

end FiniteChains.Comb
