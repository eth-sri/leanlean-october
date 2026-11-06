import RequestProject.EmbeddedAcyclicUnion


/-! The inverse image of an acyclic subcomplex whose fundamental group is
killed has vanishing H1 and H2 in an actual universal cover.  The proof
constructs all its deck translates and decomposes finite-support chains.
Unverified source. -/

noncomputable section
open scoped Classical
namespace FiniteChains.Comb.AcyclicLiftedSubcomplex
universe u
variable {D X : Complex2.{u}} (i : Hom D X)
  (hiV : Function.Injective i.onV) (hiE : Function.Injective i.onE)
  (hiF : Function.Injective i.onF) (hconn : IsConnected D) (d₀ : D.V) (ht : Pi1Trivial i)
  (hX : IsConnected X)

def lift := liftHom (f := i) (d₀ := d₀) hconn ht
def copy (g : Pi1 X (i.onV d₀)) :=
  ((univDeck X _).cellHom g).comp (lift i hconn d₀ ht)

theorem projection_V g d :
    endV ((copy i hconn d₀ ht g).onV d) = i.onV d := by
  change endV (deckV g (liftV i hconn d₀ d)) = _
  simp

include hiV in
theorem copy_injective_V (g : Pi1 X (i.onV d₀)) :
    Function.Injective (copy i hconn d₀ ht g).onV := by
  intro d e h
  grind [projection_V]

include hiE in
theorem copy_injective_E (g : Pi1 X (i.onV d₀)) :
    Function.Injective (copy i hconn d₀ ht g).onE := by
  intro d e h
  exact hiE (congrArg (·.val.2) h)

include hiV hX in
theorem copy_ranges_eq_of_meet (g h : Pi1 X (i.onV d₀)) (d e : D.V)
    (hm : (copy i hconn d₀ ht g).onV d = (copy i hconn d₀ ht h).onV e) :
    Set.range (copy i hconn d₀ ht g).onV = Set.range (copy i hconn d₀ ht h).onV ∧
    Set.range (copy i hconn d₀ ht g).onE = Set.range (copy i hconn d₀ ht h).onE ∧
    Set.range (copy i hconn d₀ ht g).onF = Set.range (copy i hconn d₀ ht h).onF := by
  have hde : d = e := by
    grind [projection_V]
  subst e
  have hE : ∀ e, (univProj X _).onE ((copy i hconn d₀ ht g).onE e) =
      (univProj X _).onE ((copy i hconn d₀ ht h).onE e) := by tauto
  have hF : ∀ f, (univProj X _).onF ((copy i hconn d₀ ht g).onF f) =
      (univProj X _).onF ((copy i hconn d₀ ht h).onF f) := by tauto
  have hV := lift_onV_eq (isCovering_univProj (X := X) (x₀ := i.onV d₀) hX) hconn hE hm
  exact ⟨congrArg Set.range (funext hV),
    congrArg Set.range (funext (lift_onE_eq (isCovering_univProj (X := X)
      (x₀ := i.onV d₀) hX) hE hV)),
    congrArg Set.range (funext (lift_onF_eq (isCovering_univProj (X := X)
      (x₀ := i.onV d₀) hX) hF hV))⟩

theorem vertices_covered v d (hv : endV v = i.onV d) :
    ∃ g, (copy i hconn d₀ ht g).onV d = v := by
  have hend : endV ((lift i hconn d₀ ht).onV d) = endV v := by
    rw [hv]
    exact endV_liftV (f := i) (d₀ := d₀) hconn d
  obtain ⟨g, hg, _⟩ := (isRegular_univProj (X := X) (x₀ := i.onV d₀)).simply_transitive
    ((lift i hconn d₀ ht).onV d) v hend
  tauto

theorem edges_covered (e : UE X (i.onV d₀)) d (he : e.val.2 = i.onE d) :
    ∃ g, (copy i hconn d₀ ht g).onE d = e := by
  have hv : endV e.val.1 = i.onV (D.src d) := by
    rw [e.property, he, i.src_onE]
  cases' vertices_covered i hconn d₀ ht e.val.1 _ hv with g hg
  refine ⟨g, Subtype.ext (Prod.ext ?_ he.symm)⟩
  tauto

include hiV hiE hconn ht hX in
theorem one_cycle_filling (hD : IsAcyclic D) (z : UE X (i.onV d₀) →₀ ℤ)
    (hs : ∀ e ∈ z.support, e.val.2 ∈ Set.range i.onE) (hz : bdry1 (uCover X (i.onV d₀)) z = 0) :
    ∃ y : UF X (i.onV d₀) →₀ ℤ,
      (∀ f ∈ y.support, f.val.2 ∈ Set.range i.onF) ∧ bdry2 (uCover X (i.onV d₀)) y = z := by
  have hs' : ∀ e ∈ z.support, AcyclicCopies.oldEdge (copy i hconn d₀ ht) e := by
    intro e he
    cases' hs e he with d hd
    cases' edges_covered i hconn d₀ ht e d hd.symm with g hg
    tauto
  obtain ⟨y, hy, hb⟩ := AcyclicCopies.one_cycle_filling _
    (copy_injective_V i hiV hconn d₀ ht) (copy_injective_E i hiE hconn d₀ ht) hD
    (copy_ranges_eq_of_meet i hiV hconn d₀ ht hX) z hs' hz
  refine ⟨y, ?_, hb⟩
  intro f hf
  obtain ⟨g, d, rfl⟩ := hy f hf
  tauto
