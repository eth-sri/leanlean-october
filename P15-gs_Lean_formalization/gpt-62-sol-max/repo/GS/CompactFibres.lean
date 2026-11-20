module

public import Mathlib.Topology.Homeomorph.Lemmas

public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Topology
namespace GS

/-- Equal fibres of two continuous maps on a compact parameter space identify
 their ranges, with the inherited Hausdorff topologies. -/
theorem exists_homeomorph_ranges_of_same_fibres
    {K Y Z : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
    (f : K → Y) (g : K → Z) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ a b, f a = f b ↔ g a = g b) :
    ∃ h : range f ≃ₜ range g,
      ∀ k, h ⟨f k, ⟨k,rfl⟩⟩ = ⟨g k, ⟨k,rfl⟩⟩ := by
  let a : range f → range g := fun y => rangeFactorization g (Classical.choose y.property)
  have ha (k : K) : a (rangeFactorization f k) = rangeFactorization g k :=
    Subtype.ext ((hfg _ _).mp (Classical.choose_spec (rangeFactorization f k).property))
  let e := Equiv.ofBijective a ⟨by
    intro x y
    obtain ⟨k,rfl⟩ := rangeFactorization_surjective x
    obtain ⟨l,rfl⟩ := rangeFactorization_surjective y
    aesop, by
    rintro ⟨z,k,rfl⟩
    exact ⟨rangeFactorization f k, ha k⟩⟩
  have hc : Continuous a := (IsQuotientMap.of_surjective_continuous
    rangeFactorization_surjective hf.rangeFactorization).continuous_iff.mpr <| by
      simpa only [Function.comp_def, ha] using hg.rangeFactorization
  letI : CompactSpace (range f) := isCompact_iff_compactSpace.mp (isCompact_range hf)
  exact ⟨e.toHomeomorphOfContinuousClosed hc hc.isClosedMap, ha⟩

end GS
