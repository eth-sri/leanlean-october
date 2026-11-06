import RequestProject.ReceivedTreeMarkedChains
import RequestProject.ReceivedTreeComparison
import RequestProject.Tac


/-! Geometric images of exact marked relative boundaries. -/
bwd

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)
  {G : Type u} [Group G] (φ : PresGroup (treeRel T) →* G)
  (ψ : G →* Pi1 Y (f.onV T.root))
  (hψ : ψ.comp φ = (pi1Map f T.root).comp (SpanningTree.presToPi1 T))

theorem comparison_pathChain g {a b} {p}
    (hp : IsPathX K p a b) :
    chain1 (comparison T f φ ψ hψ) (pathChain (liftPath T φ p g)) =
      pathChain (uLiftPath (mapPath f p) (receiverVertex T f ψ g a)) := by
  change Finsupp.mapDomain (comparison T f φ ψ hψ).onE
    (pathChain (liftPath T φ p g)) = _
  rwd [← pathChain_map _]
  exact congrArg pathChain (comparison_liftPath T f φ ψ hψ g hp)

variable {I : Type u}

/-- The translated marked paths in the actual path-class universal cover of Y. -/
noncomputable def geometricMarkedChainMap (p : I → Loop K T.root) :
    ((G × I) →₀ ℤ) →ₗ[ℤ] ((uCover Y (f.onV T.root)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun x => pathChain
    (uLiftPath (mapPath f (p x.2).1) (receiverVertex T f ψ x.1 T.root)))

theorem comparison_markedChainMap p (c : (G × I) →₀ ℤ) :
    chain1 (comparison T f φ ψ hψ) (markedChainMap T φ (fun i => (p i).1) c) =
      geometricMarkedChainMap T f ψ p c := by
  induction c using Finsupp.induction_linear with
  | zero => rfl
  | add c d hc hd => simp_all
  | single x n =>
    cases' x with g i
    simp [markedChainMap_single, map_smul, comparison_pathChain T f φ ψ hψ g (p i).2, geometricMarkedChainMap, Finsupp.linearCombination_single]

variable [Fintype I] [DecidableEq (NonTree T)]

/-- The coordinate condition alone gives a genuine two-chain with exactly the
specified translated marked boundary in the geometric universal cover. The
receiver compatibility is explicit; injectivity is not inferred from it. -/
theorem comparison_relative_boundary p
    γ (c : (G × K.F) →₀ ℤ)
    (hc : ∀ z, cellCoefficient z.1 (bdry2 (cover T φ) c) =
      ∑ i, γ i * coefficientMap T φ (fox z (pathWord T (p i).1))) :
    bdry2 (uCover Y (f.onV T.root)) (chain2 (comparison T f φ ψ hψ) c) =
      geometricMarkedChainMap T f ψ p ((cellCoordinates I).symm γ) := by
  rwd [comparison_bdry2, bdry2_eq_markedChain_of_coordinates T φ p γ c hc]
  exact comparison_markedChainMap T f φ ψ hψ p _
