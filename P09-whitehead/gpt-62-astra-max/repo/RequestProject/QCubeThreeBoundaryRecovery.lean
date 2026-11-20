module

public import RequestProject.QCubeCanonicalThreeBoundary
public import RequestProject.StrictThreeTopPartition

@[expose] public section

/-! Finite cubical recovery of actual strict three-boundaries in dimension three. -/
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qCube_three_boundary_reconstruction (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ r : QThreeCube A →₀ ℤ, qSquareChainSubdivision (qThreeCubicalBoundary r) = strictOrdBoundary3 y := by
  classical
  let S := y.support.image (fun t => t.1.2.2.2)
  have hc (c : QCube A) (hmem : c ∈ S) : c.spx.card = 3 := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hmem
    grind [qCube_tetrahedron_dimensions]
  let C : {c : QCube A // c ∈ S} → QThreeCube A := fun c => ⟨c.1, hc c.1 c.2⟩
  have hex (a : {c : QCube A // c ∈ S}) : ∃ k : ℤ,
      strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = a.1)) =
        k • qSquareChainSubdivision (qThreeCubicalFaceBoundary (C a)) := qCube_three_component_boundary_scalar (C a) y hy hb
  choose k hk using hex
  refine ⟨∑ a ∈ S.attach, Finsupp.single (C a) (k a), ?_⟩
  rw [map_sum, map_sum]
  simp only [qThreeCubicalBoundary, Finsupp.linearCombination_single, map_smul]
  have hp : strictOrdBoundary3 y = ∑ c ∈ S,
      strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c)) := by
    conv_lhs => rw [strictThreeChain_top_partition y]
    rw [map_sum]
  rw [hp, ← Finset.sum_attach S (fun c =>
    strictOrdBoundary3 _)]
  apply Finset.sum_congr rfl
  grind

end FiniteChains.Davis
