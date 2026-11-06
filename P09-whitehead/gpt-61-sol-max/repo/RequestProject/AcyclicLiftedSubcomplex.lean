import Mathlib.Tactic

import RequestProject.EmbeddedAcyclicUnion

/-! The inverse image of an acyclic subcomplex whose fundamental group is
killed has vanishing H1 and H2 in an actual universal cover.  The proof
constructs all its deck translates and decomposes finite-support chains.
Unverified source. -/

noncomputable section

namespace FiniteChains.Comb.AcyclicLiftedSubcomplex
variable {D X : Complex2.{u}} (i : Hom D X)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hconn : IsConnected D) (d₀ : D.V) (ht : Pi1Trivial i)
  (hX : IsConnected X)

def lift  := liftHom (f := i) (d₀ := d₀) hconn ht
variable (g : Pi1 X (i.onV d₀))
def copy   :=
  ((univDeck X (i.onV d₀)).cellHom g).comp (lift i hconn d₀ ht)

theorem projection_V  (d : D.V) :
    endV ((copy i hconn d₀ ht g).onV d) = i.onV d := by
  change endV (deckV g (liftV i hconn d₀ d)) = _
  rw [endV_deckV, endV_liftV]

include hiV in
theorem copy_injective_V  :
    Function.Injective (copy i hconn d₀ ht g).onV := by
  intro d e h
  apply hiV
  have h' := congrArg endV h
  simpa [projection_V] using h'

include hiE in
theorem copy_injective_E  :
    Function.Injective (copy i hconn d₀ ht g).onE := by
  intro d e h
  exact hiE (congrArg (fun e : UE X (i.onV d₀) => e.val.2) h)

include hiV hX in
theorem copy_ranges_eq_of_meet (g h : Pi1 X (i.onV d₀)) (d e : D.V)
    (hm : (copy i hconn d₀ ht g).onV d = (copy i hconn d₀ ht h).onV e) :
    Set.range (copy i hconn d₀ ht g).onV = Set.range (copy i hconn d₀ ht h).onV ∧
    Set.range (copy i hconn d₀ ht g).onE = Set.range (copy i hconn d₀ ht h).onE ∧
    Set.range (copy i hconn d₀ ht g).onF = Set.range (copy i hconn d₀ ht h).onF := by
  have hde : d = e := by
    grind [projection_V]
  subst e
  have hE : ∀ e, (univProj X (i.onV d₀)).onE ((copy i hconn d₀ ht g).onE e) =
      (univProj X (i.onV d₀)).onE ((copy i hconn d₀ ht h).onE e) := fun _ => rfl
  have hF : ∀ f, (univProj X (i.onV d₀)).onF ((copy i hconn d₀ ht g).onF f) =
      (univProj X (i.onV d₀)).onF ((copy i hconn d₀ ht h).onF f) := fun _ => rfl
  have hV := lift_onV_eq (isCovering_univProj (X := X) (x₀ := i.onV d₀) hX) hconn hE hm
  exact ⟨congrArg Set.range (funext hV),
    congrArg Set.range (funext (lift_onE_eq (isCovering_univProj (X := X)
      (x₀ := i.onV d₀) hX) hE hV)),
    congrArg Set.range (funext (lift_onF_eq (isCovering_univProj (X := X)
      (x₀ := i.onV d₀) hX) hF hV))⟩

theorem vertices_covered (v : UV X (i.onV d₀)) (d : D.V) (hv : endV v = i.onV d) :
    ∃ g, (copy i hconn d₀ ht g).onV d = v := by
  have hend : endV ((lift i hconn d₀ ht).onV d) = endV v := by
    rw [hv]
    exact endV_liftV (f := i) (d₀ := d₀) hconn d
  obtain ⟨g, hg, _⟩ := (isRegular_univProj (X := X) (x₀ := i.onV d₀)).simply_transitive
    ((lift i hconn d₀ ht).onV d) v hend
  exact ⟨g, hg⟩

theorem edges_covered (e : UE X (i.onV d₀)) (d : D.E) (he : e.val.2 = i.onE d) :
    ∃ g, (copy i hconn d₀ ht g).onE d = e := by
  have hv : endV e.val.1 = i.onV (D.src d) := by
    rw [e.property, he, i.src_onE]
  obtain ⟨g, hg⟩ := vertices_covered i hconn d₀ ht e.val.1 (D.src d) hv
  refine ⟨g, Subtype.ext (Prod.ext ?_ he.symm)⟩
  exact ((copy i hconn d₀ ht g).src_onE d).trans hg

include hiV hiE hconn ht hX in
theorem one_cycle_filling (hD : IsAcyclic D) (z : UE X (i.onV d₀) →₀ ℤ)
    (hs : ∀ e ∈ z.support, e.val.2 ∈ Set.range i.onE) (hz : bdry1 (uCover X (i.onV d₀)) z = 0) :
    ∃ y : UF X (i.onV d₀) →₀ ℤ,
      (∀ f ∈ y.support, f.val.2 ∈ Set.range i.onF) ∧ bdry2 (uCover X (i.onV d₀)) y = z := by
  have hs' : ∀ e ∈ z.support, AcyclicCopies.oldEdge (copy i hconn d₀ ht) e := by
    grind [FiniteChains.Comb.AcyclicCopies.oldEdge, edges_covered]
  obtain ⟨y, hy, hb⟩ := AcyclicCopies.one_cycle_filling (copy i hconn d₀ ht)
    (copy_injective_V i hiV hconn d₀ ht) (copy_injective_E i hiE hconn d₀ ht) hD
    (copy_ranges_eq_of_meet i hiV hconn d₀ ht hX) z hs' hz
  refine ⟨y, ?_, hb⟩
  intro f hf
  obtain ⟨g, d, rfl⟩ := hy f hf
  exact ⟨d, rfl⟩

end FiniteChains.Comb.AcyclicLiftedSubcomplex
