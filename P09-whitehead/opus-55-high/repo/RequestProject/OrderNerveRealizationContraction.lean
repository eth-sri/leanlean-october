import RequestProject.TopologicalSingular.SimplexCoordinates
import RequestProject.OrderNerveRealizationOpenStars
import RequestProject.OrderNerveRealizationPaths
import Mathlib.Topology.Homotopy.Contractible
noncomputable section


namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped unitInterval Classical

/-- Compact parameter families are continuous on a realization exactly when they
are continuous on each of its simplices. -/
theorem orderNerveRealization_continuous_prod_iff P [PartialOrder P]
    {T X} [TopologicalSpace T] [LocallyCompactSpace T] [TopologicalSpace X]
    (f : T × orderNerveRealization P → X) :
    Continuous f ↔ ∀ n s,
      Continuous (fun p : T × SimplexCategory.toTop.obj n =>
        f (p.1, orderNerveRealizationSimplex P s p.2)) := by
  constructor
  · fun_prop
  · intro h
    have ht : ∀ x, Continuous (fun t => f (t, x)) := by
      intro x
      obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
      exact (h n s).comp (continuous_id.prodMk continuous_const)
    let g : orderNerveRealization P → C(T, X) := fun x => ⟨_, ht x⟩
    have hg : Continuous g := by
      apply (orderNerveRealization_continuous_iff P g).mpr
      intro n s
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (h n s).comp continuous_swap
    exact (ContinuousMap.continuous_uncurry_of_continuous ⟨g, hg⟩).comp continuous_swap

/-- Adjoining a vertex comparable with every vertex of a simplex gives a larger
simplex, together with a simplex operator containing the original one. -/
theorem orderNerveSimplex_extend_vertex {P : Type} [PartialOrder P]
    {n} (s : (nerve P).obj (Opposite.op n)) v
    (hv : ∀ i, s.obj i ≤ v ∨ v ≤ s.obj i) :
    ∃ (m : SimplexCategory) (u : (nerve P).obj (Opposite.op m))
      (a : n ⟶ m) (j : Fin (m.len + 1)),
      (nerve P).map a.op u = s ∧ u.obj j = v := by
  classical
  let A := insert v (Set.range s.obj)
  have hA : IsChain (· ≤ ·) A := by
    intro x hx y hy _
    rcases hx with rfl | ⟨i, rfl⟩
    · grind
    · rcases hy with rfl | ⟨j, rfl⟩
      · exact hv i
      · rcases le_total i j with h | h
        · exact Or.inl (leOfHom (s.map (homOfLE h)))
        · exact Or.inr (leOfHom (s.map (homOfLE h)))
  letI : LinearOrder A :=
    { Subtype.partialOrder _ with
      le_total := fun x y => hA.total x.property y.property
      toDecidableLE := Subtype.decidableLE
      toDecidableLT := Subtype.decidableLT
      toDecidableEq := Subtype.instDecidableEq }
  let av : A := by tauto
  cases' Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := A))) with k hk
  let e := (Fintype.orderIsoFinOfCardEq A hk).symm
  let u :=
    (show Monotone (fun i => (e.symm i).val) from
      fun _ _ h => e.symm.monotone h).functor
  let a := SimplexCategory.mkHom
    ⟨fun i => e ⟨s.obj i, Set.mem_insert_of_mem _ ⟨i, rfl⟩⟩,
      fun _ _ h => e.monotone (leOfHom (s.map (homOfLE h)))⟩
  refine ⟨⦋k⦌, u, a, e av, ?_, ?_⟩
  · exact CategoryTheory.Functor.ext (fun i =>
      congrArg Subtype.val (e.symm_apply_apply
        _))
  aesop

/-- Straight-line interpolation inside a topological simplex. -/
def topologicalSimplexBlend
    (t : I) (z w : SimplexCategory.toTop.obj n) : SimplexCategory.toTop.obj n :=
  ULift.up ((TopologicalSingular.simplexCoordinates n.len).symm
    ⟨(1 - (t : ℝ)) • (TopologicalSingular.simplexCoordinates n.len z.down).val +
      (t : ℝ) • (TopologicalSingular.simplexCoordinates n.len w.down).val,
      convex_stdSimplex ℝ _ (TopologicalSingular.simplexCoordinates n.len z.down).property
        (TopologicalSingular.simplexCoordinates n.len w.down).property
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩)

theorem topologicalSimplexBlend_continuous :
    Continuous (fun p : I × (SimplexCategory.toTop.obj n × SimplexCategory.toTop.obj n) =>
      topologicalSimplexBlend p.1 p.2.1 p.2.2) := by
  unfold topologicalSimplexBlend
  fun_prop

theorem orderNerveAffineSimplex_blend {P} [PartialOrder P] v
    {n} (s : (nerve P).obj (Opposite.op n))
    t z w :
    orderNerveAffineSimplex v s (topologicalSimplexBlend t z w) =
      (1 - t) * orderNerveAffineSimplex v s z +
        t * orderNerveAffineSimplex v s w := by
  simp [orderNerveAffineSimplex, ContinuousMap.coe_mk, topologicalSimplexBlend,
    TopologicalSingular.simplexCoordinates_symm_weights_apply,
    TopologicalSingular.simplexCoordinates_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]

/-- The affine interpolation formula in global coordinates. -/
theorem orderNerveRealizationCoordinates_blend {P} [PartialOrder P]
    {n} s
    t (z w : SimplexCategory.toTop.obj n) p :
    orderNerveRealizationCoordinates P
        (orderNerveRealizationSimplex P s (topologicalSimplexBlend t z w)) p =
      (1 - t) * orderNerveRealizationCoordinates P
        (orderNerveRealizationSimplex P s z) p +
      t * orderNerveRealizationCoordinates P
        (orderNerveRealizationSimplex P s w) p := by
  have h (z : SimplexCategory.toTop.obj n) := congrArg (· z)
    (orderNerveAffineRealization_simplex (if · = p then 1 else 0) s)
  change ∀ z, orderNerveAffineRealization (if · = p then 1 else 0)
    (orderNerveRealizationSimplex P s z) =
    orderNerveAffineSimplex (if · = p then 1 else 0) s z at h
  change orderNerveAffineRealization _ (orderNerveRealizationSimplex P s _) =
    (1 - t) * orderNerveAffineRealization _ (orderNerveRealizationSimplex P s z) +
    t * orderNerveAffineRealization _ (orderNerveRealizationSimplex P s w)
  simp [h, orderNerveAffineSimplex_blend]

/-- A vertex comparable with the whole poset can be joined affinely to every
realization point, with a uniquely prescribed global coordinate vector. -/
theorem orderNerveRealization_cone_exists {P} [PartialOrder P]
    v (hv : ∀ p, p ≤ v ∨ v ≤ p) (t : I) x :
    ∃ y, ∀ p,
      orderNerveRealizationCoordinates P y p =
        (1 - t) * orderNerveRealizationCoordinates P x p +
        t * (if v = p then 1 else 0) := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  obtain ⟨m, u, a, j, hs, hj⟩ := orderNerveSimplex_extend_vertex s v (by simp_all)
  cases' orderNerveRealizationVertex_mem_simplex u j with w hw
  rw [hj] at hw
  have hz := congrArg (· z) (orderNerveRealizationSimplex_operator P a u)
  change orderNerveRealizationSimplex P u (SimplexCategory.toTop.map a z) =
    orderNerveRealizationSimplex P ((nerve P).map a.op u) z at hz
  rw [hs] at hz
  refine ⟨orderNerveRealizationSimplex P u
    (topologicalSimplexBlend t (SimplexCategory.toTop.map a z) w), fun p => ?_⟩
  rw [orderNerveRealizationCoordinates_blend, hz, hw,
    orderNerveRealizationCoordinates_vertex]

/-- The affine cone towards a universally comparable vertex. -/
def orderNerveRealizationCone {P} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) (t : I) (x : orderNerveRealization P) := (orderNerveRealization_cone_exists v hv t x).choose

theorem orderNerveRealizationCone_coordinates {P} [PartialOrder P]
    v hv t x p :
    orderNerveRealizationCoordinates P (orderNerveRealizationCone v hv t x) p =
      (1 - t) * orderNerveRealizationCoordinates P x p +
      t * (if v = p then 1 else 0) :=
  (orderNerveRealization_cone_exists v hv t x).choose_spec p

/-- The affine cone is jointly continuous in the weak CW topology, without any
local finiteness hypothesis on the poset. -/
theorem orderNerveRealizationCone_continuous {P} [PartialOrder P]
    v hv :
    Continuous (fun tx : I × orderNerveRealization P =>
      orderNerveRealizationCone v hv tx.1 tx.2) := by
  apply (orderNerveRealization_continuous_prod_iff P _).mpr
  intro n s
  obtain ⟨m, u, a, j, hs, hj⟩ := orderNerveSimplex_extend_vertex s v (by simp_all)
  obtain ⟨w, hw⟩ := orderNerveRealizationVertex_mem_simplex u j
  rw [hj] at hw
  have hz (z : SimplexCategory.toTop.obj n) := congrArg (· z)
    (orderNerveRealizationSimplex_operator P a u)
  have he : (fun tx : I × SimplexCategory.toTop.obj n =>
      orderNerveRealizationCone v hv tx.1 (orderNerveRealizationSimplex P s tx.2)) =
      (fun tx => orderNerveRealizationSimplex P u
        (topologicalSimplexBlend tx.1 (SimplexCategory.toTop.map a tx.2) w)) := by
    funext tx
    apply orderNerveRealizationCoordinates_injective P
    funext p
    rw [orderNerveRealizationCone_coordinates, orderNerveRealizationCoordinates_blend, hw,
      orderNerveRealizationCoordinates_vertex]
    have hz' := hz tx.2
    change orderNerveRealizationSimplex P u (SimplexCategory.toTop.map a tx.2) =
      orderNerveRealizationSimplex P ((nerve P).map a.op u) tx.2 at hz'
    simp_all
  rw [he]
  exact (orderNerveRealizationSimplex P u).hom.continuous.comp
    (topologicalSimplexBlend_continuous.comp
      (continuous_fst.prodMk (((SimplexCategory.toTop.map a).hom.continuous.comp
        continuous_snd).prodMk continuous_const)))

@[simp] theorem orderNerveRealizationCone_zero {P} [PartialOrder P]
    v hv (x : orderNerveRealization P) :
    orderNerveRealizationCone v hv 0 x = x := by
  apply orderNerveRealizationCoordinates_injective P
  funext p
  simp [orderNerveRealizationCone_coordinates]

@[simp] theorem orderNerveRealizationCone_one {P} [PartialOrder P]
    v hv (x : orderNerveRealization P) :
    orderNerveRealizationCone v hv 1 x = orderNerveRealizationVertex v := by
  apply orderNerveRealizationCoordinates_injective P
  funext p
  simp [orderNerveRealizationCone_coordinates, orderNerveRealizationCoordinates_vertex]

/-- A poset with a universally comparable vertex has contractible realization. -/
theorem orderNerveRealization_contractible_of_comparable {P} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) : ContractibleSpace (orderNerveRealization P) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨orderNerveRealizationVertex v, ⟨?_⟩⟩
  exact
    { toFun := fun tx => orderNerveRealizationCone v hv tx.1 tx.2
      continuous_toFun := orderNerveRealizationCone_continuous v hv
      map_zero_left := by simp
      map_one_left := by simp }
