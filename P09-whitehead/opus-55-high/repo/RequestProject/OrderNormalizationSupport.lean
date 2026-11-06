import RequestProject.OrderThreeNormalization
import RequestProject.Tac


/-! Normalization preserves the actual vertex tuples in the support of finite chains. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem normalizeOrdChain2_support z (t : StrictOrdTri P)
    (ht : t ∈ (normalizeOrdChain2 z).support) :
    ∃ a ∈ z.support, a.1 = t.1 := by
  classical
  obtain ⟨a, ha, hta⟩ := Finsupp.mem_support_finset_sum t ht
  have hn : normalizeOrdTriangle a t ≠ 0 := by
    simp_all
  unfold normalizeOrdTriangle at hn
  grind
