module

public import RequestProject.PushoutOldCoverAcyclic

@[expose] public section

/-! The actual old copies cover every old cell. Two copies meeting at a
vertex agree after a genuine deck transformation of D, on all cells.
These facts supply the component partition for supported descent chains.
Unverified source. -/

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.PushoutOldCover
universe u v
variable {D K L : Complex2.{u}} {Q : Type v} [Group Q]
  (p : Hom D K) (hp : IsCovering p) (a : DeckAction D Q) (hr : IsRegular p a)
  (he : ∀ q e, p.onE (a.smulE q e) = p.onE e)
  (hf : ∀ q f, p.onF (a.smulF q f) = p.onF f)
  (i : Hom D L) (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hconn : IsConnected D) (d₀ : D.V) (ht : Pi1Trivial i)

theorem translated_projection_V
    (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (d : D.V) :
    endV ((translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d) = Sum.inl (p.onV d) := by
  change endV (deckV g (liftV (oldMap p i hiV hiE) hconn d₀ d)) = _
  erw [endV_deckV, endV_liftV]
  rfl

theorem translated_projection_F
    (g : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (d : D.F) :
    ((translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF d).val.2 = Sum.inl (p.onF d) := rfl

include hp in
theorem old_vertices_covered
    (v : UV (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (k : K.V)
    (hv : endV v = Sum.inl k) :
    ∃ g d, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d = v := by
  obtain ⟨d, hd⟩ := hp.surjV k
  have hend : endV ((oldLift p i hiV hiE hiF hconn d₀ ht).onV d) = endV v := by
    erw [hv]
    change endV (liftV (oldMap p i hiV hiE) hconn d₀ d) = Sum.inl k
    erw [endV_liftV]
    exact congrArg Sum.inl hd
  obtain ⟨g, hg, _⟩ := (isRegular_univProj (X := pushoutComplex p i hiV hiE)
    (x₀ := Sum.inl (p.onV d₀))).simply_transitive
      ((oldLift p i hiV hiE hiF hconn d₀ ht).onV d) v hend
  exact ⟨g, d, hg⟩

include hp in
theorem old_faces_covered
    (f : UF (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀))) (k : K.F)
    (hf' : f.val.2 = Sum.inl k) :
    ∃ g d, (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onF d = f := by
  have hv : endV f.val.1 = Sum.inl (K.base k) := by erw [f.property, hf']; rfl
  obtain ⟨g, d, hd⟩ := old_vertices_covered p hp i hiV hiE hiF hconn d₀ ht f.val.1 (K.base k) hv
  have hbase : K.base k = p.onV d := by
    have h := translated_projection_V p i hiV hiE hiF hconn d₀ ht g d
    erw [hd, hv] at h
    exact Sum.inl.inj h
  obtain ⟨l, ⟨hlp, hl⟩, _⟩ := exists_unique_liftCell hp.uniqueLifts k hbase
  refine ⟨g, l, Subtype.ext (Prod.ext ?_ ?_)⟩
  · have h := (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).base_onF l
    exact h.trans ((congrArg _ hl).trans hd)
  · erw [translated_projection_F, hf']
    exact congrArg Sum.inl hlp

include hr he hf in
/-- Overlap is an actual deck identification of D, not an arbitrary
identification of chains. -/
theorem copies_identified_of_meet
    (hEconn : IsConnected (pushoutComplex p i hiV hiE))
    (g h : Pi1 (pushoutComplex p i hiV hiE) (Sum.inl (p.onV d₀)))
    (d e : D.V)
    (hmeet : (translatedOldLift p i hiV hiE hiF hconn d₀ ht g).onV d =
      (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).onV e) :
    ∃ q : Q, translatedOldLift p i hiV hiE hiF hconn d₀ ht g =
      (translatedOldLift p i hiV hiE hiF hconn d₀ ht h).comp (a.cellHom q) := by
  apply lifts_identified hr (isCovering_univProj hEconn) hconn ?_ ?_ ?_ hmeet
  · intro q l
    exact congrArg Sum.inl (he q l).symm
  · intro q t
    exact congrArg Sum.inl (hf q t).symm
  · have h' := congrArg endV hmeet
    erw [translated_projection_V, translated_projection_V] at h'
    exact Sum.inl.inj h'

end FiniteChains.Comb.PushoutOldCover
