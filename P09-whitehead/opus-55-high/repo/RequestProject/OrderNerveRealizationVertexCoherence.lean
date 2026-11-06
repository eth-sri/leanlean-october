import RequestProject.OrderNerveRealizationFundamental
import RequestProject.OrderFunctorTrivialization


namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- A combinatorially connected simply connected poset admits topological path
classes to its vertices which commute with every realized comparable edge. -/
theorem orderNerveRealization_exists_vertex_coherence P [PartialOrder P]
    a (hconn : IsConnected (orderCx P)) (hsc : SimplyConnected (orderCx P)) :
    ∃ k : ∀ p, FundamentalGroupoid.mk (orderNerveRealizationVertex a) ⟶
        FundamentalGroupoid.mk (orderNerveRealizationVertex p),
      ∀ {p q : P} h,
        k p ≫ Path.Homotopic.Quotient.mk (orderNerveRealizationEdgePath h) = k q := by
  letI : Nonempty P := ⟨a⟩
  letI := orderNerveRealization_pathConnectedSpace P hconn
  let F := orderNerveRealizationFundamentalFunctor P
  let d : ∀ p, F.obj a ⟶ F.obj p := fun p =>
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath
      _ _)
  cases' orderFunctor_exists_coherent_arrows F a d hconn hsc with k hk
  exact ⟨k, by tauto⟩

/-- Each point has a radial path from a supporting vertex. The radial path
stays inside every closed star whose corresponding open star contains the point. -/
theorem orderNerveRealization_exists_radial {P} [PartialOrder P]
    x :
    ∃ (p : P) (r : Path (orderNerveRealizationVertex p) x),
      ∀ v, x ∈ orderNerveRealizationOpenStar P v →
        (p ≤ v ∨ v ≤ p) ∧
        Set.range r ⊆ (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v)) := by
  obtain ⟨n, s, z, hz, hx⟩ := orderNerveRealization_interior_cover P x
  cases' orderNerveRealizationVertex_mem_simplex s.val 0 with w hw
  let r₀ := (PathConnectedSpace.joined w z).somePath.map
    (orderNerveRealizationSimplex P s.val).hom.continuous
  let r := r₀.cast hw.symm hx.symm
  refine ⟨s.val.obj 0, r, ?_⟩
  intro v hv
  rw [← hx] at hv
  cases' (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz v).mp hv with j hj
  have hall : ∀ i, s.val.obj i ≤ v ∨ v ≤ s.val.obj i := by
    intro i
    rcases le_total i j with h | h
    · exact Or.inl (hj ▸ leOfHom (s.val.map (homOfLE h)))
    · exact Or.inr (hj ▸ leOfHom (s.val.map (homOfLE h)))
  refine ⟨hall 0, ?_⟩
  have hr : Set.range r ⊆ Set.range (orderNerveRealizationSimplex P s.val) := by
    rintro y ⟨t, rfl⟩
    aesop
  exact hr.trans (orderNerveRealizationSimplex_supported _ s.val hall)
