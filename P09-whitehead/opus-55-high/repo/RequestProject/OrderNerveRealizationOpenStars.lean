import RequestProject.OrderNervePosetCoverVertexStars


namespace FiniteChains.Comb
open CategoryTheory Simplicial Topology
open scoped Classical

/-- The actual open vertex star, defined by positivity of its global coordinate. -/
def orderNerveRealizationOpenStar P [PartialOrder P] (v : P) := {x | 0 < orderNerveRealizationCoordinates P x v}

/-- Coordinate positivity defines an open subset of the actual realization. -/
theorem orderNerveRealizationOpenStar_isOpen P [PartialOrder P] v :
    IsOpen (orderNerveRealizationOpenStar P v) := isOpen_Ioi.preimage ((continuous_apply v).comp
    (orderNerveRealizationCoordinates P).continuous)

/-- On simplex interiors, open-star membership is exactly vertex membership. -/
theorem orderNerveRealizationSimplex_mem_openStar_iff {P} [PartialOrder P]
    {n} s
    (z : SimplexCategory.toTop.obj n) (hz : ∀ i, 0 < z.down.weights i) v :
    orderNerveRealizationSimplex P s z ∈ orderNerveRealizationOpenStar P v ↔
      v ∈ Set.range s.obj := by
  have he := congrArg (· z)
    (orderNerveAffineRealization_simplex (if · = v then 1 else 0) s)
  change orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) v =
    orderNerveAffineSimplex (if · = v then 1 else 0) s z at he
  change 0 < orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) v ↔ _
  rw [he]
  exact orderNerveAffineSimplex_indicator_pos_iff s z hz v

/-- Actual open vertex stars cover the whole realization. -/
theorem orderNerveRealizationOpenStar_cover P [PartialOrder P]
    x : ∃ v, x ∈ orderNerveRealizationOpenStar P v := by
  obtain ⟨n, s, z, hz, he⟩ := orderNerveRealization_interior_cover P x
  refine ⟨s.val.obj 0, ?_⟩
  rw [← he]
  exact (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz _).mpr ⟨0, rfl⟩

/-- Every point of an open star lies in the genuine comparable-vertex CW carrier. -/
theorem orderNerveRealizationOpenStar_subset_subcomplex {P} [PartialOrder P]
    v : orderNerveRealizationOpenStar P v ⊆
      (orderNerveRealizationSubcomplex P (orderNerveVertexStar P v)) := by
  intro x hx
  obtain ⟨n, s, z, hz, he⟩ := orderNerveRealization_interior_cover P x
  rw [← he] at hx ⊢
  cases' (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz v).mp hx with i hi
  apply orderNerveRealizationSimplex_supported (orderNerveVertexStar P v) s.val _ ⟨z, rfl⟩
  intro j
  rcases le_total j i with h | h
  · exact Or.inl (hi ▸ leOfHom (s.val.map (homOfLE h)))
  · exact Or.inr (hi ▸ leOfHom (s.val.map (homOfLE h)))

/-- Open stars over distinct lifts of one vertex are disjoint. -/
theorem IsPosetCover.realizationOpenStar_disjoint {P Q}
    [PartialOrder P] [PartialOrder Q] {f : P → Q} (hf : IsPosetCover f)
    {a b} (hab : a ≠ b) (he : f a = f b) :
    Disjoint (orderNerveRealizationOpenStar P a) (orderNerveRealizationOpenStar P b) := by
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  obtain ⟨n, s, z, hz, hx⟩ := orderNerveRealization_interior_cover P x
  rw [← hx] at hxa hxb
  cases' (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz a).mp hxa with i hi
  cases' (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz b).mp hxb with j hj
  have hij : f (s.val.obj i) = f (s.val.obj j) := by simp_all
  rcases le_total i j with h | h
  · have hs := hf.up_inj (by simp)
      (leOfHom (s.val.map (homOfLE h))) hij
    simp_all
  · have hs := hf.up_inj (by simp)
      (leOfHom (s.val.map (homOfLE h))) hij.symm
    simp_all

/-- The preimage of an open star is exactly the union of stars at its lifted vertices. -/
theorem orderNerveRealizationMap_mem_openStar_iff {P Q}
    [PartialOrder P] [PartialOrder Q] f hf
    x q :
    orderNerveRealizationMap f hf x ∈ orderNerveRealizationOpenStar Q q ↔
      ∃ p, f p = q ∧ x ∈ orderNerveRealizationOpenStar P p := by
  obtain ⟨n, s, z, hz, hx⟩ := orderNerveRealization_interior_cover P x
  rw [← hx]
  have hn := congrArg (· z) (orderNerveRealizationSimplex_natural f hf s.val)
  change orderNerveRealizationMap f hf (orderNerveRealizationSimplex P s.val z) =
    orderNerveRealizationSimplex Q ((nerveMap hf.functor).app _ s.val) z at hn
  rw [hn, orderNerveRealizationSimplex_mem_openStar_iff _ z hz]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨s.val.obj i, hi, ?_⟩
    exact (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz _).mpr ⟨i, rfl⟩
  · rintro ⟨p, hp, hxp⟩
    cases' (orderNerveRealizationSimplex_mem_openStar_iff s.val z hz p).mp hxp with i hi
    aesop
