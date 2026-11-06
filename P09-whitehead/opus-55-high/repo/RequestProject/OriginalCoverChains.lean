import RequestProject.TopologicalCoverTreeChains
import RequestProject.OrderTriangleTreeComparison


/-! The unrestricted sufficiency direction of the original theorem:
an actual connected acyclic regular covering gives strict chains of
arbitrary positive length starting with the original CW cells.
Source assembled; final Lean verification remains outstanding. -/

noncomputable section
open scoped Classical
namespace Whitehead
open FiniteChains FiniteChains.Comb FiniteChains.ClassicalCW FiniteChains.PresModel

theorem hasChain_of_acyclicRegularCover K
    (h : HasAcyclicRegularCover K) n (hn : 1 ≤ n) : HasChain K n false := by
  let hP := presPos_isConnected _ (canonicalWords_ne_nil K)
  obtain ⟨T, -⟩ := SpanningTree.exists_of_isConnected
    (strictOrderCx_isConnected hP)
    (Classical.choice (by tauto))
  let e₀ := OrderTriangleWords.canonicalTreeDiskRealizationEquiv
    _ T (canonicalTreeGenerator K T) hP
  cases n with
  | zero => omega
  | succ n => exact hasChain_of_original_cover_tree_comparison K T e₀ h n
