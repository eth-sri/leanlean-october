module

public import RequestProject.OrderNerveOneDictionary
public import RequestProject.FinsuppBasis
public import RequestProject.OrderTwoMapPrism

@[expose] public section

/-! Genuine finite triangle fillings for two-leg order contractions in degree one. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

noncomputable def normalizedStrictChain1 (g : P → P) (hg : Monotone g) :
    (StrictOrdEdge P →₀ ℤ) →ₗ[ℤ] (StrictOrdEdge P →₀ ℤ) :=
  normalizeOrdChain1.comp ((chain1 (orderCxMap g hg)).comp (chain1 (strictOrderIncl P)))

theorem normalizedStrictChain1_single (g : P → P) (hg : Monotone g)
    (e : StrictOrdEdge P) (n : ℤ) :
    normalizedStrictChain1 g hg (Finsupp.single e n) =
      n • normalizeOrdEdge ⟨(g e.1.1, g e.1.2), hg e.2.le⟩ := by
  change normalizeOrdChain1 (Finsupp.mapDomain (orderCxMap g hg).onE
    (Finsupp.mapDomain (strictOrderIncl P).onE (Finsupp.single e n))) = _
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, normalizeOrdChain1_single]
  rfl

theorem normalizedStrictChain1_id (c : StrictOrdEdge P →₀ ℤ) :
    normalizedStrictChain1 id monotone_id c = c := by
  change normalizeOrdChain1 (Finsupp.mapDomain id (Finsupp.mapDomain (strictOrderIncl P).onE c)) = c
  rw [Finsupp.mapDomain_id, normalizeOrdChain1_inclusion]

theorem normalizedStrictChain1_zero_of_comparable_equal
    (g : P → P) (hg : Monotone g) (he : ∀ {a b : P}, a ≤ b → g a = g b)
    (c : StrictOrdEdge P →₀ ℤ) : normalizedStrictChain1 g hg c = 0 := by
  classical
  finsupp_basis c
  intro e
  rw [normalizedStrictChain1_single]
  simp [normalizeOrdEdge, he e.2.le]

theorem strict_oneCycle_comparable_boundary (g h : P → P)
    (hg : Monotone g) (hh : Monotone h) (hgh : ∀ x, g x ≤ h x)
    (c : StrictOrdEdge P →₀ ℤ) (hc : bdry1 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTri P →₀ ℤ,
      bdry2 (strictOrderCx P) y = normalizedStrictChain1 h hh c -
        normalizedStrictChain1 g hg c := by
  let w := chain1 (strictOrderIncl P) c
  have hw : bdry1 (orderCx P) w = 0 := by
    exact chain1_cycle _ hc
  refine ⟨normalizeOrdChain2 (ordMapPrism1 g h hg hh hgh w), ?_⟩
  rw [bdry2_normalizeOrdChain2, ordMapPrism_oneCycle g h hg hh hgh w hw, map_sub]
  rfl

theorem strict_oneCycle_boundary_of_roof_collapse (g h : P → P)
    (hg : Monotone g) (hh : Monotone h) (hgi : ∀ x, g x ≤ x)
    (hgh : ∀ x, g x ≤ h x) (he : ∀ {a b : P}, a ≤ b → h a = h b)
    (c : StrictOrdEdge P →₀ ℤ) (hc : bdry1 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) y = c := by
  obtain ⟨y, hy⟩ := strict_oneCycle_comparable_boundary g id hg monotone_id hgi c hc
  obtain ⟨z, hz⟩ := strict_oneCycle_comparable_boundary g h hg hh hgh c hc
  refine ⟨y - z, ?_⟩
  simp [hy, hz, normalizedStrictChain1_id, normalizedStrictChain1_zero_of_comparable_equal h hh he]

end FiniteChains.Comb
