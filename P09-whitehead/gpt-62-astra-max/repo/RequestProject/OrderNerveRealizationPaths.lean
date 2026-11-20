module

public import RequestProject.OrderNerveRealizationCW

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial

section

variable {P : Type} [PartialOrder P]

/-- The canonical actual realization point of a poset vertex. -/
noncomputable def orderNerveRealizationVertex (p : P) :=
  orderNerveRealizationSimplex P (ComposableArrows.mk₀ p) default

variable {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))

/-- Every vertex of a simplex belongs to its actual canonical image. -/
theorem orderNerveRealizationVertex_mem_simplex (i : Fin _) :
    ∃ z : SimplexCategory.toTop.obj n,
      orderNerveRealizationSimplex P s z = orderNerveRealizationVertex (s.obj i) := by
  let a : ⦋0⦌ ⟶ n := SimplexCategory.mkHom (OrderHom.const _ i)
  refine ⟨SimplexCategory.toTop.map a default, ?_⟩
  have h := congrArg (fun k => k default) (orderNerveRealizationSimplex_operator P a s)
  assumption

/-- Every actual simplex point is joined by a continuous path to each of its vertices. -/
theorem orderNerveRealizationSimplex_joined_vertex
    (z : SimplexCategory.toTop.obj n) (i : Fin _) :
    Joined (orderNerveRealizationSimplex P s z) (orderNerveRealizationVertex (s.obj i)) := by
  obtain ⟨w, hw⟩ := orderNerveRealizationVertex_mem_simplex s i
  have h : Joined _ (orderNerveRealizationSimplex P s w) :=
    ⟨(PathConnectedSpace.joined z w).somePath.map
      (orderNerveRealizationSimplex P s).hom.continuous⟩
  simp_all

/-- Comparable poset vertices are joined in the actual realization. -/
theorem orderNerveRealizationVertex_joined_of_le
    {p q : P} (h : p ≤ q) : Joined (orderNerveRealizationVertex p) (orderNerveRealizationVertex q) := by
  let s := ComposableArrows.mk₁ (homOfLE h)
  let z : SimplexCategory.toTop.obj ⦋1⦌ := Classical.choice inferInstance
  exact (orderNerveRealizationSimplex_joined_vertex s z 0).symm.trans (orderNerveRealizationSimplex_joined_vertex s z 1)

/-- Actual realization vertices joined by a combinatorial edge path are topologically joined. -/
theorem orderNerveRealizationVertex_joined_of_isPath
    {a b : P} {p : List (OrdEdge P × Bool)}
    (hp : IsPath (orderCx P).src (orderCx P).tgt p a b) :
    Joined (orderNerveRealizationVertex a) (orderNerveRealizationVertex b) := by
  induction p generalizing a with
  | nil =>
    subst b; exact Joined.refl _
  | cons e p ih =>
    rcases hp with ⟨rfl, hp⟩
    have he : Joined
        (orderNerveRealizationVertex (P := P) (germSrc (orderCx P).src (orderCx P).tgt e))
        (orderNerveRealizationVertex (germTgt (orderCx P).src (orderCx P).tgt e)) := by
      rcases e with ⟨e, o⟩
      cases o
      · exact (orderNerveRealizationVertex_joined_of_le e.property).symm
      · exact orderNerveRealizationVertex_joined_of_le e.property
    exact he.trans (ih hp)

end

/-- A nonempty combinatorially connected poset has path-connected actual realization. -/
theorem orderNerveRealization_pathConnectedSpace (P : Type) [PartialOrder P] [Nonempty P]
    (hP : IsConnected (orderCx P)) : PathConnectedSpace (orderNerveRealization P) where
  nonempty := ⟨orderNerveRealizationVertex (Classical.choice inferInstance)⟩
  joined x y := by
    obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective P x
    obtain ⟨m, t, w, hy⟩ := orderNerveRealizationSimplex_jointly_surjective P y
    have hs := orderNerveRealizationSimplex_joined_vertex s z 0
    have ht := orderNerveRealizationSimplex_joined_vertex t w 0
    rw [hx] at hs
    rw [hy] at ht
    obtain ⟨p, hp⟩ := hP _ _
    exact hs.trans ((orderNerveRealizationVertex_joined_of_isPath hp).trans ht.symm)

end FiniteChains.Comb
