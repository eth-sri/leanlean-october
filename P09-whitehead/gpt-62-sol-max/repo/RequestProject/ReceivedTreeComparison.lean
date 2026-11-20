module

public import RequestProject.ReceivedTreeGauge
public import RequestProject.CellularHomotopyChain
public import RequestProject.ComponentComplex

@[expose] public section

/-! A constructed cellular comparison, including the lifted attaching paths. -/

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
universe u
variable {K Y : Complex2.{u}} (T : SpanningTree K) (f : Hom K Y)
  {G : Type u} [Group G] (φ : PresGroup (treeRel T) →* G)
  (ψ : G →* Pi1 Y (f.onV T.root))
  (hψ : ψ.comp φ = (pi1Map f T.root).comp (SpanningTree.presToPi1 T))

noncomputable def receiverGerm (e : (G × K.E) × Bool) : UE Y (f.onV T.root) × Bool :=
  (receiverEdge T f ψ e.1.1 e.1.2, e.2)

include hψ in
/-- Every actual lifted edge path has the claimed geometric image. -/
theorem comparison_liftPath (g : G) {a b : K.V} {p : List (K.E × Bool)}
    (hp : IsPath K.src K.tgt p a b) :
    (liftPath T φ p g).map (receiverGerm T f ψ) =
      uLiftPath (mapPath f p) (receiverVertex T f ψ g a) := by
  have he := map_eq_uLiftPath (K := cover T φ) (fun x => receiverVertex T f ψ x.1 x.2)
    (fun x => receiverEdge T f ψ x.1 x.2) (fun _ => rfl)
    (fun x => receiverEdge_tgt T f φ ψ hψ x.1 x.2) (liftPath_isPath T φ hp g)
  change _ = uLiftPath ((liftPath T φ p g).map fun e => (f.onE e.1.2, e.2)) _ at he
  refine he.trans (congrArg (fun l => uLiftPath l _) ?_)
  simpa only [List.map_map, Function.comp_def, mapPath] using
    congrArg (List.map fun d : K.E × Bool => (f.onE d.1, d.2)) (liftPath_projection T φ p g)

/-- The comparison is an actual cellular map, not a postulated chain map. -/
noncomputable def comparison : Hom (cover T φ) (uCover Y (f.onV T.root)) where
  onV x := receiverVertex T f ψ x.1 x.2
  onE x := receiverEdge T f ψ x.1 x.2
  onF x := receiverFace T f ψ x.1 x.2
  src_onE _ := rfl
  tgt_onE x := receiverEdge_tgt T f φ ψ hψ x.1 x.2
  base_onF _ := rfl
  att_onF x := by
    change uLiftPath (Y.att (f.onF x.2)) (receiverVertex T f ψ x.1 (K.base x.2)) =
      (liftPath T φ (K.att x.2) x.1).map (receiverGerm T f ψ)
    rw [f.att_onF]
    exact (comparison_liftPath T f φ ψ hψ x.1 (K.att_isLoop x.2)).symm

theorem comparison_bdry2 (c : (G × K.F) →₀ ℤ) :
    bdry2 (uCover Y (f.onV T.root)) (chain2 (comparison T f φ ψ hψ) c) =
      chain1 (comparison T f φ ψ hψ) (bdry2 (cover T φ) c) :=
  bdry2_chain2 (comparison T f φ ψ hψ) c

/-- For the receiving group pi1(Y), the compatibility triangle is an identity.
This gives the genuine comparison without an extra mathematical assumption. -/
noncomputable def canonicalReceiver : PresGroup (treeRel T) →* Pi1 Y (f.onV T.root) :=
  (pi1Map f T.root).comp (SpanningTree.presToPi1 T)

end FiniteChains.Comb.ReceivedTree
