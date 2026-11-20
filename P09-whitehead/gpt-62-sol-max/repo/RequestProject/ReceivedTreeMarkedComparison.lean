module

public import RequestProject.ReceivedTreeMarkedChains
public import RequestProject.FinsuppBasis
public import RequestProject.ReceivedTreeComparison

@[expose] public section

/-! Geometric images of exact marked relative boundaries. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)
  {G : Type u} [Group G] (φ : PresGroup (treeRel T) →* G)
  (ψ : G →* Pi1 Y (f.onV T.root))
  (hψ : ψ.comp φ = (pi1Map f T.root).comp (SpanningTree.presToPi1 T))

theorem comparison_pathChain (g : G) {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) :
    chain1 (comparison T f φ ψ hψ) (pathChain (liftPath T φ p g)) =
      pathChain (uLiftPath (mapPath f p) (receiverVertex T f ψ g a)) := by
  change Finsupp.mapDomain (comparison T f φ ψ hψ).onE
    (pathChain (liftPath T φ p g)) = _
  erw [← pathChain_map (comparison T f φ ψ hψ)]
  exact congrArg pathChain (comparison_liftPath T f φ ψ hψ g hp)

variable {I : Type u}

/-- The translated marked paths in the actual path-class universal cover of Y. -/
noncomputable def geometricMarkedChainMap (p : I → Loop K T.root) :
    ((G × I) →₀ ℤ) →ₗ[ℤ] ((uCover Y (f.onV T.root)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain
    (uLiftPath (mapPath f (p x.2).1) (receiverVertex T f ψ x.1 T.root)))

theorem comparison_markedChainMap (p : I → Loop K T.root) (c : (G × I) →₀ ℤ) :
    chain1 (comparison T f φ ψ hψ) (markedChainMap T φ (fun i => (p i).1) c) =
      geometricMarkedChainMap T f ψ p c := by
  finsupp_basis c
  intro x
  obtain ⟨g, i⟩ := x
  erw [markedChainMap_single, map_smul, comparison_pathChain T f φ ψ hψ g (p i).2,
    geometricMarkedChainMap, Finsupp.linearCombination_single]

end FiniteChains.Comb.ReceivedTree
