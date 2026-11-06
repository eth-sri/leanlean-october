import RequestProject.OrderConeCoverVertices
import RequestProject.CombPi2
import RequestProject.Tac
noncomputable section


/-! Finite lifted cone fans with their exact cellular boundary. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]
  (f : P → Q) (hf : Monotone f) (c : Q) (hc : ∀ x, c ≤ f x)
  {o : Q} (k : UV (orderCx Q) o) (hk : endV k = c)

def coneCoverFan :
    ((orderCx P).E →₀ ℤ) →ₗ[ℤ] ((uCover (orderCx Q) o).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ (fun e => Finsupp.single (coneCoverFace f hf c hc k hk e) 1)

def coneCoverPath (p : List ((orderCx P).E × Bool)) :=
  p.map (fun eb => (coneCoverSurfaceEdge f hf c hc k hk eb.1, eb.2))

/-- A lifted fan has the surface path boundary plus the initial radial edge minus the final one. -/
theorem coneCoverFan_path_boundary {a b : P} {p}
    (hp : IsPathX (orderCx P) p a b) :
    bdry2 _ (coneCoverFan f hf c hc k hk (pathChain p)) =
      pathChain (coneCoverPath f hf c hc k hk p) +
      Finsupp.single (coneCoverRadialEdge f c hc k hk a) 1 -
      Finsupp.single (coneCoverRadialEdge f c hc k hk b) 1 := by
  induction p generalizing a with
  | nil => aesop
  | cons eb p ih =>
      cases' hp with ha hp
      subst a
      rw [pathChain_cons, map_add, map_add, ih hp]
      cases' eb with e d
      cases d
      · have he := coneCoverFace_boundary f hf c hc k hk e
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [map_neg, map_neg]
        rw [coneCoverFan, Finsupp.linearCombination_single, one_smul, he]
        simp [coneCoverPath, pathChain_cons, germSrc, germTgt, orderCx]
        abel
      · have he := coneCoverFace_boundary f hf c hc k hk e
        simp [↓reduceIte]
        rw [coneCoverFan, Finsupp.linearCombination_single, one_smul, he]
        simp [coneCoverPath, pathChain_cons, germSrc, germTgt, orderCx]
        abel

/-- The radial terms cancel for a loop, giving a concrete finite universal-cover filling. -/
theorem coneCoverFan_loop_boundary {a : P} {p}
    (hp : IsPathX (orderCx P) p a a) :
    bdry2 _ (coneCoverFan f hf c hc k hk (pathChain p)) =
      pathChain (coneCoverPath f hf c hc k hk p) := by
  rw [coneCoverFan_path_boundary f hf c hc k hk hp]
  abel

theorem coneCoverSurfaceGerm_src eb :
    gSrcX (uCover (orderCx Q) o)
      (coneCoverSurfaceEdge f hf c hc k hk eb.1, eb.2) =
      coneCoverReference f c hc k (gSrcX (orderCx P) eb) := by
  cases' eb with e d
  cases d
  · exact coneCoverReference_edge f hf c hc k hk e
  · rfl

theorem coneCoverSurfaceGerm_tgt eb :
    gTgtX (uCover (orderCx Q) o)
      (coneCoverSurfaceEdge f hf c hc k hk eb.1, eb.2) =
      coneCoverReference f c hc k (gTgtX (orderCx P) eb) := by
  cases' eb with e d
  cases d
  · rfl
  · exact coneCoverReference_edge f hf c hc k hk e

/-- The fan's surface path is an actual path between the lifted reference vertices. -/
theorem coneCoverPath_isPath {a b : P} {p}
    (hp : IsPathX (orderCx P) p a b) :
    IsPathX (uCover (orderCx Q) o)
      (coneCoverPath f hf c hc k hk p)
      (coneCoverReference f c hc k a) (coneCoverReference f c hc k b) := by
  induction p generalizing a with
  | nil => tauto
  | cons eb p ih =>
      cases' hp with ha hp
      subst a
      constructor
      · exact (coneCoverSurfaceGerm_src f hf c hc k hk eb).symm
      · rw [coneCoverSurfaceGerm_tgt]
        exact ih hp

/-- The fan follows the canonical actual lift of the included surface path. -/
theorem coneCoverPath_eq_lift {a b : P} {p}
    (hp : IsPathX (orderCx P) p a b) :
    coneCoverPath f hf c hc k hk p =
      uLiftPath (mapPath (orderCxMap f hf) p) (coneCoverReference f c hc k a) := by
  have h := eq_uLiftPath_of_isPath _ _ _ (coneCoverPath_isPath f hf c hc k hk hp)
  have he : mapPath (univProj (orderCx Q) o) (coneCoverPath f hf c hc k hk p) =
      mapPath (orderCxMap f hf) p := by
    simp only [mapPath, coneCoverPath, List.map_map]
    rfl
  simp_all

/-- The explicit lifted fan fills the canonical universal-cover lift of any surface loop. -/
theorem coneCoverFan_loop_lift_boundary {a : P} {p}
    (hp : IsPathX (orderCx P) p a a) :
    bdry2 _ (coneCoverFan f hf c hc k hk (pathChain p)) =
      pathChain (uLiftPath (mapPath (orderCxMap f hf) p) (coneCoverReference f c hc k a)) := by
  rw [coneCoverFan_loop_boundary f hf c hc k hk hp, coneCoverPath_eq_lift f hf c hc k hk hp]

/-- Forgetting the deck coordinate gives exactly the explicit ordinary cone fan. -/
theorem coneCoverFan_hurewicz z :
    hurewicz (orderCx Q) o (coneCoverFan f hf c hc k hk z) = coneEdgeChain f hf c hc z := by
  lin_ind z e n =>
      rw [coneCoverFan, coneEdgeChain, Finsupp.linearCombination_single,
        Finsupp.linearCombination_single, map_smul]
      congr 1
      change Finsupp.mapDomain (univProj (orderCx Q) o).onF
        (Finsupp.single (coneCoverFace f hf c hc k hk e) (1)) =
          Finsupp.single (coneEdgeTriangle f hf c hc e) (1)
      aesop
