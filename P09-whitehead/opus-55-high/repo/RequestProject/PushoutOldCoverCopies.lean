import RequestProject.PushoutOldCoverAcyclic
import RequestProject.Tac


/-! The actual old copies cover every old cell. Two copies meeting at a
vertex agree after a genuine deck transformation of D, on all cells.
These facts supply the component partition for supported descent chains.
Unverified source. -/

noncomputable section
open scoped Classical

bwd

namespace FiniteChains.Comb.PushoutOldCover
universe u v
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hconn : IsConnected D) (d₀ : D.V) (ht : Pi1Trivial i)

theorem translated_projection_V
    g d :
    endV ((translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d) = Sum.inl (p.onV d) := by
  change endV (deckV g (liftV (oldMap p i hiV hiE) hconn d₀ d)) = _
  aesop


include hp in
theorem old_vertices_covered
    (v : UV (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (k : K.V)
    (hv : endV v = Sum.inl k) :
    ∃ g d, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d = v := by
  cases' hp.surjV k with d hd
  have hend : endV ((oldLift p i hiV hiE hiF hconn d₀ ht).onV d) = endV v := by
    rwd [hv]
    change endV (liftV (oldMap p i hiV hiE) hconn d₀ d) = Sum.inl k
    aesop
  obtain ⟨g, hg, _⟩ := (isRegular_univProj (X := pushoutComplex p i hiV hiE)
    (x₀ := Sum.inl (p.onV d₀))).simply_transitive
      ((oldLift p i hiV hiE hiF hconn d₀ ht).onV d) v hend
  tauto

include hp in
theorem old_faces_covered
    (f : UF (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (k : K.F)
    (hf' : f.val.2 = Sum.inl k) :
    ∃ g d, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF d = f := by
  have hv : endV f.val.1 = Sum.inl (K.base k) := by rwd [f.property, hf']; rfl
  obtain ⟨g, d, hd⟩ := old_vertices_covered p hp i hiV hiE hiF hconn d₀ ht f.val.1 _ hv
  have hbase : K.base k = p.onV d := by
    have h := translated_projection_V p i hiV hiE hiF hconn d₀ ht g d
    grind
  obtain ⟨l, ⟨hlp, hl⟩, _⟩ := exists_unique_liftCell hp k hbase
  refine ⟨g, l, Subtype.ext (Prod.ext ?_ ?_)⟩
  · aesop
  aesop

include hr he hf in
/-- Overlap is an actual deck identification of D, not an arbitrary
identification of chains. -/
theorem copies_identified_of_meet
    (hEconn : IsConnected (pushoutComplex p i hiV hiE))
    (g h : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)))
    (d e : D.V)
    (hmeet : (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d =
      (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onV e) :
    ∃ q : Q,
      (∀ v, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV v =
        (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onV (a.smulV q v)) ∧
      (∀ l, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onE l =
        (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onE (a.smulE q l)) ∧
      (∀ f, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF f =
        (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onF (a.smulF q f)) := by
  have hpde : p.onV d = p.onV e := by
    grind [translated_projection_V]
  obtain ⟨q, hq, _⟩ := hr.simply_transitive d e hpde
  let F := translatedOldLift p i hiV hiE hiF hconn d₀ ht g
  let G := (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).comp (a.cellHom q)
  have hE : ∀ l, (univProj _ _).onE (F.onE l) =
      (univProj _ _).onE (G.onE l) := by
    intro l
    change Sum.inl (p.onE l) = Sum.inl (p.onE (a.smulE q l))
    simp_all
  have hF : ∀ l, (univProj _ _).onF (F.onF l) =
      (univProj _ _).onF (G.onF l) := by
    intro l
    change Sum.inl (p.onF l) = Sum.inl (p.onF (a.smulF q l))
    simp_all
  have hb : F.onV d = G.onV d := by
    aesop
  have hV := lift_onV_eq (isCovering_univProj (X := pushoutComplex p i hiV hiE)
    (x₀ := Sum.inl (p.onV d₀)) hEconn) hconn hE hb
  exact ⟨q, hV, lift_onE_eq (isCovering_univProj (X := pushoutComplex p i hiV hiE)
    (x₀ := Sum.inl (p.onV d₀)) hEconn) hE hV,
    lift_onF_eq (isCovering_univProj (X := pushoutComplex p i hiV hiE)
      (x₀ := Sum.inl (p.onV d₀)) hEconn) hF hV⟩
