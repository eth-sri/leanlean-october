import RequestProject.OrderConeChains
import RequestProject.CombUniversalCover
import RequestProject.Tac
noncomputable section


/-! Actual reference vertices for lifting the explicit cone fan. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P Q : Type u} [Preorder P] [Preorder Q]
  (f : P → Q) (hf : Monotone f) (c : Q) (hc : ∀ x, c ≤ f x)
  {o : Q} (k : UV (orderCx Q) o) (hk : endV k = c)

def coneCoverReference (a : P) :=
  extend (coneRadial f c hc a, true) k

include hk
omit [Preorder P] in
theorem coneCoverReference_end (a : P) :
    endV (coneCoverReference f c hc k a) = f a :=
  endV_extend hk

/-- The actual surface edge connects the reference vertices in the lifted cone fan. -/
theorem coneCoverReference_edge e :
    extend ((orderCxMap f hf).onE e, true) (coneCoverReference f c hc k e.1.1) =
      coneCoverReference f c hc k e.1.2 := by
  let t := coneEdgeTriangle f hf c hc e
  have ht := hk
  have hloop := extendList_att (c := k) (f := t) ht
  change extend (coneRadial f c hc e.1.2, false)
    (extend ((orderCxMap f hf).onE e, true)
      (coneCoverReference f c hc k e.1.1)) = k at hloop
  have hsrc : endV (coneCoverReference f c hc k e.1.1) =
      gSrcX (orderCx Q) ((orderCxMap f hf).onE e, true) := by
    rw [coneCoverReference_end f c hc k hk]
    rfl
  have hend :=
    endV_extend hsrc
  have h := congrArg (extend (coneRadial f c hc e.1.2, true)) hloop
  have hcancel := extend_revGerm (eb := (coneRadial f c hc e.1.2, false)) hend
  change extend (coneRadial f c hc e.1.2, true)
    (extend (coneRadial f c hc e.1.2, false) _) = _ at hcancel
  rwa [hcancel] at h

def coneCoverRadialEdge (a : P) : (uCover (orderCx Q) o).E :=
  ⟨(k, coneRadial f c hc a), hk⟩

def coneCoverSurfaceEdge (e : (orderCx P).E) : (uCover (orderCx Q) o).E :=
  ⟨(coneCoverReference f c hc k e.1.1, (orderCxMap f hf).onE e), by
    rw [coneCoverReference_end f c hc k hk]
    rfl⟩

def coneCoverFace (e : (orderCx P).E) : (uCover (orderCx Q) o).F :=
  ⟨(k, coneEdgeTriangle f hf c hc e), hk⟩

/-- The lifted cone triangle has the two radial edges and the actual surface edge as boundary. -/
theorem coneCoverFace_att e :
    uAtt (coneCoverFace f hf c hc k hk e) =
      [(coneCoverRadialEdge f c hc k hk e.1.1, true),
       (coneCoverSurfaceEdge f hf c hc k hk e, true),
       (coneCoverRadialEdge f c hc k hk e.1.2, false)] := by
  have hs : endV (coneCoverReference f c hc k e.1.1) =
      gSrcX (orderCx Q) ((orderCxMap f hf).onE e, true) := by
    rw [coneCoverReference_end f c hc k hk]
    rfl
  have hb : endV (coneCoverReference f c hc k e.1.2) =
      gSrcX (orderCx Q) (coneRadial f c hc e.1.2, false) :=
    coneCoverReference_end f c hc k hk _
  have he := coneCoverReference_edge f hf c hc k hk e
  have hcancel := extend_revGerm (eb := (coneRadial f c hc e.1.2, true)) hk
  change extend (coneRadial f c hc e.1.2, false)
    (coneCoverReference f c hc k e.1.2) = k at hcancel
  change uLiftPath [(coneRadial f c hc e.1.1, true),
    ((orderCxMap f hf).onE e, true), (coneRadial f c hc e.1.2, false)] k = _
  rw [uLiftPath_cons hk]
  change (Comb.liftGerm k (coneRadial f c hc e.1.1, true) hk) ::
    uLiftPath [((orderCxMap f hf).onE e, true), (coneRadial f c hc e.1.2, false)]
      (coneCoverReference f c hc k e.1.1) = _
  rw [uLiftPath_cons hs, he, uLiftPath_cons hb, uLiftPath_nil]
  aesop

/-- Exact cellular boundary of the actual lifted cone triangle. -/
theorem coneCoverFace_boundary e :
    bdry2 (uCover (orderCx Q) o) (Finsupp.single (coneCoverFace f hf c hc k hk e) 1) =
      Finsupp.single (coneCoverSurfaceEdge f hf c hc k hk e) 1 +
      Finsupp.single (coneCoverRadialEdge f c hc k hk e.1.1) 1 -
      Finsupp.single (coneCoverRadialEdge f c hc k hk e.1.2) 1 := by
  rw [bdry2_single, one_smul]
  change pathChain (uAtt (coneCoverFace f hf c hc k hk e)) = _
  rw [coneCoverFace_att]
  simp [pathChain_cons]
  abel
