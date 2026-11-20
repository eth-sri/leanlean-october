module

public import RequestProject.OrderConeCoverVertices
public import RequestProject.FinsuppBasis
public import RequestProject.CombPi2

@[expose] public section

/-! Finite lifted cone fans with their exact cellular boundary. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]
  (f : P → Q) (hf : Monotone f) (c : Q) (hc : ∀ x, c ≤ f x)
  {o : Q} (k : UV (orderCx Q) o) (hk : endV k = c)

noncomputable def coneCoverFan :
    ((orderCx P).E →₀ ℤ) →ₗ[ℤ] ((uCover (orderCx Q) o).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e => Finsupp.single (coneCoverFace f hf c hc k hk e) 1)

noncomputable def coneCoverPath (p : List ((orderCx P).E × Bool)) :
    List ((uCover (orderCx Q) o).E × Bool) :=
  p.map (fun eb => (coneCoverSurfaceEdge f hf c hc k hk eb.1, eb.2))

/-- The radial contribution is the negative of the lifted vertex boundary. -/
theorem coneCoverFan_boundary (z : (orderCx P).E →₀ ℤ) :
    bdry2 _ (coneCoverFan f hf c hc k hk z) =
      Finsupp.mapDomain (coneCoverSurfaceEdge f hf c hc k hk) z -
        Finsupp.mapDomain (coneCoverRadialEdge f c hc k hk) (bdry1 (orderCx P) z) := by
  finsupp_basis z
  intro e
  rw [coneCoverFan, Finsupp.linearCombination_single, one_smul, coneCoverFace_boundary,
    bdry1_single, one_smul, Finsupp.mapDomain_sub, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  simp only [orderCx, chainCx]
  abel

/-- The fan follows the canonical actual lift of the included surface path. -/
theorem coneCoverPath_eq_lift {a b : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) :
    coneCoverPath f hf c hc k hk p =
      uLiftPath (mapPath (orderCxMap f hf) p) (coneCoverReference f c hc k a) :=
  map_eq_uLiftPath (K := orderCx P) (coneCoverReference f c hc k)
    (coneCoverSurfaceEdge f hf c hc k hk) (fun _ => rfl) (coneCoverReference_edge f hf c hc k hk) hp

/-- The explicit lifted fan fills the canonical universal-cover lift of any surface loop. -/
theorem coneCoverFan_loop_lift_boundary {a : P} {p : List ((orderCx P).E × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a a) :
    bdry2 _ (coneCoverFan f hf c hc k hk (pathChain p)) =
      pathChain (uLiftPath (mapPath (orderCxMap f hf) p) (coneCoverReference f c hc k a)) := by
  rw [coneCoverFan_boundary, bdry1_pathChain_of_isPath hp, sub_self, Finsupp.mapDomain_zero,
    sub_zero, ← pathChain_map_edges, ← coneCoverPath, coneCoverPath_eq_lift f hf c hc k hk hp]

/-- Forgetting the deck coordinate gives exactly the explicit ordinary cone fan. -/
theorem coneCoverFan_hurewicz (z : (orderCx P).E →₀ ℤ) :
    hurewicz (orderCx Q) o (coneCoverFan f hf c hc k hk z) = coneEdgeChain f hf c hc z := by
  finsupp_basis z
  intro e
  rw [coneCoverFan, coneEdgeChain, Finsupp.linearCombination_single,
    Finsupp.linearCombination_single, map_smul]
  congr 1
  change Finsupp.mapDomain (univProj (orderCx Q) o).onF
    (Finsupp.single (coneCoverFace f hf c hc k hk e) 1) =
      Finsupp.single (coneEdgeTriangle f hf c hc e) 1
  rw [Finsupp.mapDomain_single]
  rfl

end FiniteChains.Comb
