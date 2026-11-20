module

public import RequestProject.ReceivedTreeCover
public import RequestProject.UniversalTreeGauge

@[expose] public section

/-! Exact geometric reference paths for the cover over a receiving group. -/

noncomputable section

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)
  {G : Type u} [Group G] (φ : PresGroup (treeRel T) →* G)
  (ψ : G →* Pi1 Y (f.onV T.root))

variable (g : G) (a : K.V)

def receiverVertex :=
  deckV (ψ g) (mappedTreeReference T f a)

theorem receiverVertex_end :
    endV (receiverVertex T f ψ g a) = f.onV a := by
  rw [receiverVertex, endV_deckV, mappedTreeReference_end]

variable (hψ : ψ.comp φ = (pi1Map f T.root).comp (SpanningTree.presToPi1 T))

include hψ in
theorem receiver_word (w : FreeGroup _) :
    ψ (φ (QuotientGroup.mk w)) = pi1Map f T.root (SpanningTree.freeToPi1 T w) :=
  DFunLike.congr_fun hψ _

variable (g : G)

include hψ in
/-- The actual geometric endpoint changes by exactly the received tree word. -/
theorem receiverVertex_path {a b : K.V} {p : List _}
    (hp : IsPath K.src K.tgt p a b) :
    extendList (mapPath f p) (receiverVertex T f ψ g a) =
      receiverVertex T f ψ (g * wordValue T φ p) b := by
  unfold receiverVertex
  rw [extendList_deckV, mappedTreeReference_path T f hp, map_mul,
    deckV_mul, wordValue, receiver_word T f φ ψ hψ]

variable (e : K.E)

def receiverEdge : UE Y (f.onV T.root) :=
  ⟨(receiverVertex T f ψ g (K.src e), f.onE e), by
    rw [receiverVertex_end, f.src_onE]⟩

include hψ in
theorem receiverEdge_tgt :
    uTgt (receiverEdge T f ψ g e) =
      receiverVertex T f ψ (g * germValue T φ (e, true)) (K.tgt e) := by
  simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
    wordValue_cons, wordValue_nil, mul_one, receiverEdge, uTgt, germSrc, germTgt, if_true] using (receiverVertex_path T f φ ψ hψ g (isPath_single (X := K) (e, true)))

def receiverFace (t : K.F) : UF Y (f.onV T.root) :=
  ⟨(receiverVertex T f ψ g (K.base t), f.onF t), by
    rw [receiverVertex_end, f.base_onF]⟩

end FiniteChains.Comb.ReceivedTree
