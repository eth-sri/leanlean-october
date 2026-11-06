import RequestProject.OrderNerveRealizationCW


namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- The canonical actual realization point of a poset vertex. -/
noncomputable def orderNerveRealizationVertex {P} [PartialOrder P] (p : P) :=
  orderNerveRealizationSimplex P (n := ⦋0⦌) (ComposableArrows.mk₀ p) default

/-- Every vertex of a simplex belongs to its actual canonical image. -/
theorem orderNerveRealizationVertex_mem_simplex {P} [PartialOrder P]
    {n} s (i : Fin (n.len + 1)) :
    ∃ z : SimplexCategory.toTop.obj n,
      orderNerveRealizationSimplex P s z = orderNerveRealizationVertex (s.obj i) := by
  let a : ⦋0⦌ ⟶ n := SimplexCategory.mkHom (OrderHom.const _ i)
  have h := congrArg (· default) (orderNerveRealizationSimplex_operator P a s)
  tauto

/-- Every actual simplex point is joined by a continuous path to each of its vertices. -/
theorem orderNerveRealizationSimplex_joined_vertex {P} [PartialOrder P]
    {n} s
    (z : SimplexCategory.toTop.obj n) (i : Fin (n.len + 1)) :
    Joined (orderNerveRealizationSimplex P s z) (orderNerveRealizationVertex (s.obj i)) := by
  cases' orderNerveRealizationVertex_mem_simplex s i with w hw
  have h : Joined (orderNerveRealizationSimplex P s z) (orderNerveRealizationSimplex P s w) :=
    ⟨(PathConnectedSpace.joined z w).somePath.map
      (orderNerveRealizationSimplex P s).hom.continuous⟩
  simp_all

/-- Comparable poset vertices are joined in the actual realization. -/
theorem orderNerveRealizationVertex_joined_of_le {P} [PartialOrder P]
    {p q : P} (h : p ≤ q) : Joined (orderNerveRealizationVertex p) (orderNerveRealizationVertex q) := by
  let s := ComposableArrows.mk₁ (homOfLE h)
  let z : SimplexCategory.toTop.obj ⦋1⦌ := Classical.choice inferInstance
  have hp := orderNerveRealizationSimplex_joined_vertex s z (0 : Fin 2)
  have hq := orderNerveRealizationSimplex_joined_vertex s z (1 : Fin 2)
  exact hp.symm.trans hq

/-- Actual realization vertices joined by a combinatorial edge path are topologically joined. -/
theorem orderNerveRealizationVertex_joined_of_isPath {P} [PartialOrder P]
    {a b : P} {p : List (OrdEdge P × Bool)}
    (hp : IsPathX (orderCx P) p a b) :
    Joined (orderNerveRealizationVertex a) (orderNerveRealizationVertex b) := by
  induction p generalizing a with
  | nil =>
    change a = b at hp
    aesop
  | cons e p ih =>
    rcases hp with ⟨rfl, hp⟩
    have he : Joined
        (orderNerveRealizationVertex (P := P) (gSrcX (orderCx P) e))
        (orderNerveRealizationVertex (P := P) (gTgtX (orderCx P) e)) := by
      cases' e with e o
      cases o
      · exact (orderNerveRealizationVertex_joined_of_le e.property).symm
      · exact orderNerveRealizationVertex_joined_of_le e.property
    exact he.trans (ih hp)

/-- A nonempty combinatorially connected poset has path-connected actual realization. -/
theorem orderNerveRealization_pathConnectedSpace P [PartialOrder P] [Nonempty P]
    (hP : IsConnected (orderCx P)) : PathConnectedSpace (orderNerveRealization P) where
  nonempty := ⟨orderNerveRealizationVertex (Classical.choice (inferInstance : Nonempty P))⟩
  joined x y := by
    obtain ⟨n, s, z, hx⟩ := orderNerveRealizationSimplex_jointly_surjective P x
    obtain ⟨m, t, w, hy⟩ := orderNerveRealizationSimplex_jointly_surjective P y
    have hs := orderNerveRealizationSimplex_joined_vertex s z (0 : Fin (n.len + 1))
    have ht := orderNerveRealizationSimplex_joined_vertex t w (0 : Fin (m.len + 1))
    rw [hx] at hs
    rw [hy] at ht
    cases' hP (s.obj 0) (t.obj 0) with p hp
    exact hs.trans ((orderNerveRealizationVertex_joined_of_isPath hp).trans ht.symm)
