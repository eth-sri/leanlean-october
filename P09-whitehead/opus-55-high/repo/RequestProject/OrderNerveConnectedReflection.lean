import RequestProject.OrderNerveRealizationSubtypeHomeomorph
import RequestProject.OrderNerveRealizationOpenStars


/-! Connectedness of the actual realization reflects combinatorial
connectedness. Components give clopen induced subcomplexes; the argument
works with arbitrarily many vertices and cells. Unverified source. -/

noncomputable section
namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical
variable {P : Type} [PartialOrder P]

def orderReach (a : P) : Set P :=
  {b | ∃ p, IsPathX (orderCx P) p a b}

theorem orderReach_le_iff a {b c : P} (h : b ≤ c) :
    b ∈ orderReach a ↔ c ∈ orderReach a := by
  let e : (orderCx P).E := by tauto
  constructor
  · rintro ⟨p, hp⟩
    have hs : IsPathX (orderCx P) [(e, true)] b c := by tauto
    exact ⟨p ++ [(e, true)], hp.append hs⟩
  · rintro ⟨p, hp⟩
    have hs : IsPathX (orderCx P) [(e, false)] c b := by tauto
    exact ⟨p ++ [(e, false)], hp.append hs⟩

theorem orderNerveRealizationSubcomplex_isClosed A :
    IsClosed (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) := by
  rw [← orderNerveRealizationSubtype_range A]
  exact (orderNerveRealizationSubtype_isClosedEmbedding A).isClosed_range

theorem orderReach_realization_compl a :
    (orderNerveRealizationSubcomplex P (orderReach a) : Set (orderNerveRealization P))ᶜ =
      orderNerveRealizationSubcomplex P (orderReach a)ᶜ := by
  let A := orderReach a
  have hcover : ∀ x,
      x ∈ orderNerveRealizationSubcomplex P A ∨
        x ∈ orderNerveRealizationSubcomplex P Aᶜ := by
    intro x
    obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
    have hm : ∀ i, s.obj 0 ∈ A ↔ s.obj i ∈ A := fun i =>
      orderReach_le_iff a (leOfHom (s.map (homOfLE i.zero_le)))
    by_cases h : s.obj 0 ∈ A
    · exact Or.inl (orderNerveRealizationSimplex_supported A s
        (fun i => (hm i).mp h) ⟨z, rfl⟩)
    · exact Or.inr (orderNerveRealizationSimplex_supported Aᶜ s
        (by simp_all) ⟨z, rfl⟩)
  have hdisjoint : ∀ x,
      x ∈ orderNerveRealizationSubcomplex P A →
      x ∈ orderNerveRealizationSubcomplex P Aᶜ → False := by
    intro x hx hy
    cases' orderNerveRealizationOpenStar_cover P x with v hv
    have hzero : orderNerveRealizationCoordinates P x v = 0 := by
      by_cases h : v ∈ A
      · tauto
      tauto
    change 0 < orderNerveRealizationCoordinates P x v at hv
    simp_all
  ext x
  constructor
  · intro hx
    exact (hcover x).resolve_left hx
  tauto

theorem orderCx_isConnected_of_realization [PreconnectedSpace (orderNerveRealization P)] :
    IsConnected (orderCx P) := by
  intro a b
  change P at a b
  let A := orderNerveRealizationSubcomplex P (orderReach a)
  have ha :=
    (orderNerveRealizationVertex_mem_subcomplex (orderReach a) a).mpr ⟨[], rfl⟩
  have hopen : IsOpen (A : Set (orderNerveRealization P)) := by
    apply isClosed_compl_iff.mp
    rw [orderReach_realization_compl]
    exact orderNerveRealizationSubcomplex_isClosed _
  have hall :=
    (show IsClopen (A : Set (orderNerveRealization P)) from
      ⟨orderNerveRealizationSubcomplex_isClosed _, hopen⟩).eq_univ ⟨_, ha⟩
  have hb : orderNerveRealizationVertex b ∈ (A : Set (orderNerveRealization P)) := by
    simp_all
  exact (orderNerveRealizationVertex_mem_subcomplex _ b).mp hb
