module


public import RequestProject.OrderNerveRealizationOpenStars

@[expose] public section

/-! Connectedness of the actual realization reflects combinatorial
connectedness. Components give clopen induced subcomplexes; the argument
works with arbitrarily many vertices and cells. Unverified source. -/

noncomputable section
namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical
variable {P : Type} [PartialOrder P]

variable (a : P)

def orderReach : Set P :=
  {b | ∃ p, IsPath (orderCx P).src (orderCx P).tgt p a b}

theorem orderReach_le_iff {b c : P} (h : b ≤ c) :
    b ∈ orderReach a ↔ c ∈ orderReach a := by
  let e : (orderCx P).E := ⟨(b, c), h⟩
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p ++ [(e, true)], hp.append (⟨rfl, rfl⟩)⟩
  · rintro ⟨p, hp⟩
    exact ⟨p ++ [(e, false)], hp.append (⟨rfl, rfl⟩)⟩

theorem orderNerveRealizationSubcomplex_isClosed (A : Set P) :
    IsClosed (orderNerveRealizationSubcomplex P A : Set (orderNerveRealization P)) := by
  rw [← orderNerveRealizationSubtype_range A]
  exact (orderNerveRealizationSubtype_isClosedEmbedding A).isClosed_range

theorem orderReach_realization_compl (a : P) :
    (orderNerveRealizationSubcomplex P (orderReach a) : Set (orderNerveRealization P))ᶜ =
      orderNerveRealizationSubcomplex P (orderReach a)ᶜ := by
  let A := orderReach a
  have hcover : ∀ x : orderNerveRealization P,
      x ∈ orderNerveRealizationSubcomplex P A ∨
        x ∈ orderNerveRealizationSubcomplex P Aᶜ := by
    intro x
    obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
    have hm := fun i =>
      orderReach_le_iff a (leOfHom (s.map (homOfLE (Fin.zero_le i))))
    by_cases h : s.obj 0 ∈ A
    · exact Or.inl (orderNerveRealizationSimplex_supported A s
        (fun i => (hm i).mp h) ⟨z, rfl⟩)
    · exact Or.inr (orderNerveRealizationSimplex_supported Aᶜ s
        (fun i hi => h ((hm i).mpr hi)) ⟨z, rfl⟩)
  have hdisjoint : ∀ x : orderNerveRealization P,
      x ∈ orderNerveRealizationSubcomplex P A →
      x ∈ orderNerveRealizationSubcomplex P Aᶜ → False := by
    intro x hx hy
    obtain ⟨v, hv⟩ := orderNerveRealizationOpenStar_cover P x
    have hzero : orderNerveRealizationCoordinates P x v = 0 := by
      by_cases h : v ∈ A
      · solve_by_elim
      · exact hx v h
    change 0 < orderNerveRealizationCoordinates P x v at hv
    simp_all
  ext x
  constructor
  · intro hx
    exact (hcover x).resolve_left hx
  · solve_by_elim

theorem orderCx_isConnected_of_realization [PreconnectedSpace (orderNerveRealization P)] :
    IsConnected (orderCx P) := by
  intro a b
  change P at a b
  let A := orderNerveRealizationSubcomplex P (orderReach a)
  have hopen : IsOpen (A : Set (orderNerveRealization P)) := by
    apply isClosed_compl_iff.mp
    rw [orderReach_realization_compl]
    exact orderNerveRealizationSubcomplex_isClosed _
  have hall :=
    (show IsClopen (A : Set (orderNerveRealization P)) from
      ⟨orderNerveRealizationSubcomplex_isClosed _, hopen⟩).eq_univ ⟨_, ((orderNerveRealizationVertex_mem_subcomplex (orderReach a) a).mpr ⟨[], rfl⟩)⟩
  have hb : orderNerveRealizationVertex b ∈ (A : Set _) := by
    rw [hall]
    exact Set.mem_univ _
  exact (orderNerveRealizationVertex_mem_subcomplex _ b).mp hb

end FiniteChains.Comb
