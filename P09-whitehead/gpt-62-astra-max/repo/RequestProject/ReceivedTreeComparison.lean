module

public import RequestProject.ReceivedTreeGauge
public import RequestProject.CellularHomotopyChain


@[expose] public section

/-! A constructed cellular comparison, including the lifted attaching paths. -/

noncomputable section

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)
  {G : Type u} [Group G] (φ : PresGroup (treeRel T) →* G)
  (ψ : G →* Pi1 Y (f.onV T.root))
  (hψ : ψ.comp φ = (pi1Map f T.root).comp (SpanningTree.presToPi1 T))

def receiverGerm (e : (G × K.E) × Bool) :=
  (receiverEdge T f ψ e.1.1 e.1.2, e.2)

variable (g : G)

include hψ in
theorem comparison_liftGerm (e : K.E × Bool) :
    receiverGerm T f ψ (liftGerm T φ g e) =
      Comb.liftGerm (receiverVertex T f ψ g (germSrc K.src K.tgt e))
        (f.onE e.1, e.2) (by rw [receiverVertex_end, germSrc_onE]) := by
  obtain ⟨e, b⟩ := e
  cases b with
  | true => rfl
  | false =>
    have he : extend (f.onE e, false) (receiverVertex T f ψ g (K.tgt e)) =
        receiverVertex T f ψ (g * germValue T φ (e, false)) (K.src e) := by
      simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
        wordValue_cons, wordValue_nil, mul_one, germSrc, germTgt, Bool.false_eq_true, if_false] using (receiverVertex_path T f φ ψ hψ g (isPath_single (X := K) (e, false)))
    aesop

include hψ in
/-- Every actual lifted edge path has the claimed geometric image. -/
theorem comparison_liftPath {a b : K.V} {p : List _}
    (hp : IsPath K.src K.tgt p a b) :
    (liftPath T φ p g).map (receiverGerm T f ψ) =
      uLiftPath (mapPath f p) (receiverVertex T f ψ g a) := by
  induction p generalizing a g with
  | nil => rfl
  | cons e p ih =>
    obtain ⟨ha, hp⟩ := hp
    have he : extend (f.onE e.1, e.2)
        (receiverVertex T f ψ g (germSrc K.src K.tgt e)) =
        receiverVertex T f ψ (g * germValue T φ e) (germTgt K.src K.tgt e) := by
      simpa only [mapPath, List.map_cons, List.map_nil, extendList_cons, extendList_nil,
        wordValue_cons, wordValue_nil, mul_one, germSrc, germTgt, Bool.false_eq_true, if_false] using (receiverVertex_path T f φ ψ hψ g (isPath_single (X := K) e))
    change receiverGerm T f ψ _ :: _ =
      uLiftPath ((f.onE e.1, e.2) :: mapPath f p) _
    grind [uLiftPath_cons, comparison_liftGerm]

/-- The comparison is an actual cellular map, not a postulated chain map. -/
def comparison : Hom (cover T φ) (uCover Y (f.onV T.root)) where
  onV x := receiverVertex T f ψ x.1 x.2
  onE x := receiverEdge T f ψ x.1 x.2
  onF x := receiverFace T f ψ x.1 x.2
  src_onE _ := rfl
  tgt_onE x := receiverEdge_tgt T f φ ψ hψ x.1 x.2
  base_onF _ := rfl
  att_onF x := by
    change uLiftPath (Y.att (f.onF x.2)) _ =
      (liftPath T φ _ x.1).map _
    rw [f.att_onF]
    exact (comparison_liftPath T f φ ψ hψ x.1 (K.att_isLoop x.2)).symm

theorem comparison_bdry2 (c : (G × K.F) →₀ ℤ) :
    bdry2 _ (chain2 (comparison T f φ ψ hψ) c) =
      chain1 (comparison T f φ ψ hψ) (bdry2 (cover T φ) c) :=
  by apply bdry2_chain2

/-- For the receiving group pi1(Y), the compatibility triangle is an identity.
This gives the genuine comparison without an extra mathematical assumption. -/
def canonicalReceiver :=
  (pi1Map f T.root).comp (SpanningTree.presToPi1 T)

end FiniteChains.Comb.ReceivedTree
