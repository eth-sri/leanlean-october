module

public import RequestProject.TopologicalSingular.SimplexCoordinates
public import RequestProject.OrderNerveRealizationOpenStars
public import RequestProject.OrderNerveRealizationPaths
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped unitInterval Classical

theorem orderNerveRealization_continuous_prod_iff (P : Type) [PartialOrder P]
    {T X : Type*} [TopologicalSpace T] [LocallyCompactSpace T] [TopologicalSpace X]
    (f : T × orderNerveRealization P → X) :
    Continuous f ↔ ∀ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n)),
      Continuous (fun p : T × SimplexCategory.toTop.obj n =>
        f (p.1, orderNerveRealizationSimplex P s p.2)) :=
  ⟨fun h n s => h.comp (continuous_fst.prodMk
    ((orderNerveRealizationSimplex P s).hom.continuous.comp continuous_snd)), fun h => by
    have ht (x : orderNerveRealization P) : Continuous (fun t : T => f (t, x)) := by
      obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
      exact (h n s).comp (continuous_id.prodMk continuous_const)
    exact (ContinuousMap.continuous_uncurry_of_continuous ⟨fun x => ⟨_, ht x⟩,
      (orderNerveRealization_continuous_iff P _).mpr fun n s =>
        ContinuousMap.continuous_of_continuous_uncurry _ ((h n s).comp continuous_swap)⟩).comp
      continuous_swap⟩

theorem orderNerveSimplex_extend_vertex {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n)) (v : P)
    (hv : ∀ i, s.obj i ≤ v ∨ v ≤ s.obj i) :
    ∃ (m : SimplexCategory) (u : (nerve P).obj (Opposite.op m))
      (a : n ⟶ m) (j : Fin (m.len + 1)),
      (nerve P).map a.op u = s ∧ u.obj j = v := by
  classical
  let A : Set P := insert v (Set.range s.obj)
  have hA : IsChain (· ≤ ·) A := by
    rintro x (rfl | ⟨i, rfl⟩) y (rfl | ⟨j, rfl⟩) _
    · exact .inl le_rfl
    · exact (hv j).symm
    · exact hv i
    · exact (le_total i j).imp (fun h => leOfHom (s.map (homOfLE h)))
        fun h => leOfHom (s.map (homOfLE h))
  letI : Fintype A := (Set.finite_range s.obj |>.insert v).fintype
  letI : LinearOrder A :=
    { Subtype.partialOrder _ with
      le_total := fun x y => hA.total x.property y.property
      toDecidableLE := Subtype.decidableLE
      toDecidableLT := Subtype.decidableLT
      toDecidableEq := Subtype.instDecidableEq }
  let av : A := ⟨v, Set.mem_insert v _⟩
  letI : Nonempty A := ⟨av⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := A)))
  let e : A ≃o Fin (k + 1) := (Fintype.orderIsoFinOfCardEq A hk).symm
  refine ⟨⦋k⦌, (show Monotone (fun i : Fin (k + 1) => (e.symm i).val) from
      fun _ _ h => e.symm.monotone h).functor,
    SimplexCategory.mkHom ⟨fun i => e ⟨s.obj i, Set.mem_insert_of_mem _ ⟨i, rfl⟩⟩,
      fun _ _ h => e.monotone (leOfHom (s.map (homOfLE h)))⟩, e av,
    CategoryTheory.Functor.ext fun i => congrArg Subtype.val
      (e.symm_apply_apply ⟨s.obj i, Set.mem_insert_of_mem _ ⟨i, rfl⟩⟩),
    congrArg Subtype.val (e.symm_apply_apply av)⟩

noncomputable def topologicalSimplexBlend {n : SimplexCategory}
    (t : I) (z w : SimplexCategory.toTop.obj n) : SimplexCategory.toTop.obj n :=
  ULift.up ((TopologicalSingular.simplexCoordinates n.len).symm
    ⟨(1 - (t : ℝ)) • (TopologicalSingular.simplexCoordinates n.len z.down).val +
      (t : ℝ) • (TopologicalSingular.simplexCoordinates n.len w.down).val,
      convex_stdSimplex ℝ _ (TopologicalSingular.simplexCoordinates n.len z.down).property
        (TopologicalSingular.simplexCoordinates n.len w.down).property
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩)

theorem topologicalSimplexBlend_continuous {n : SimplexCategory} :
    Continuous (fun p : I × (SimplexCategory.toTop.obj n × SimplexCategory.toTop.obj n) =>
      topologicalSimplexBlend p.1 p.2.1 p.2.2) := by
  unfold topologicalSimplexBlend; fun_prop

theorem orderNerveAffineSimplex_blend {P : Type} [PartialOrder P] (v : P → ℝ)
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (t : I) (z w : SimplexCategory.toTop.obj n) :
    orderNerveAffineSimplex v s (topologicalSimplexBlend t z w) =
      (1 - (t : ℝ)) * orderNerveAffineSimplex v s z +
        (t : ℝ) * orderNerveAffineSimplex v s w := by
  simp only [orderNerveAffineSimplex, ContinuousMap.coe_mk, topologicalSimplexBlend,
    TopologicalSingular.simplexCoordinates_symm_weights_apply,
    TopologicalSingular.simplexCoordinates_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]

theorem orderNerveRealizationCoordinates_blend {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (t : I) (z w : SimplexCategory.toTop.obj n) (p : P) :
    orderNerveRealizationCoordinates P
        (orderNerveRealizationSimplex P s (topologicalSimplexBlend t z w)) p =
      (1 - (t : ℝ)) * orderNerveRealizationCoordinates P
        (orderNerveRealizationSimplex P s z) p +
      (t : ℝ) * orderNerveRealizationCoordinates P
        (orderNerveRealizationSimplex P s w) p := by
  have h (z : SimplexCategory.toTop.obj n) :
      orderNerveAffineRealization (fun q => if q = p then 1 else 0)
        (orderNerveRealizationSimplex P s z) =
        orderNerveAffineSimplex (fun q => if q = p then 1 else 0) s z :=
    congrArg (· z) (orderNerveAffineRealization_simplex (fun q => if q = p then 1 else 0) s)
  change orderNerveAffineRealization _ (orderNerveRealizationSimplex P s _) =
    (1 - (t : ℝ)) * orderNerveAffineRealization _ (orderNerveRealizationSimplex P s z) +
    (t : ℝ) * orderNerveAffineRealization _ (orderNerveRealizationSimplex P s w)
  rw [h, h, h, orderNerveAffineSimplex_blend]

theorem orderNerveRealization_cone_exists {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) (t : I) (x : orderNerveRealization P) :
    ∃ y : orderNerveRealization P, ∀ p,
      orderNerveRealizationCoordinates P y p =
        (1 - (t : ℝ)) * orderNerveRealizationCoordinates P x p +
        (t : ℝ) * (if v = p then 1 else 0) := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  obtain ⟨m, u, a, j, hs, hj⟩ := orderNerveSimplex_extend_vertex s v fun i => hv (s.obj i)
  obtain ⟨w, hw⟩ := orderNerveRealizationVertex_mem_simplex u j
  have hz : orderNerveRealizationSimplex P u (SimplexCategory.toTop.map a z) =
      orderNerveRealizationSimplex P ((nerve P).map a.op u) z :=
    congrArg (· z) (orderNerveRealizationSimplex_operator P a u)
  refine ⟨orderNerveRealizationSimplex P u
    (topologicalSimplexBlend t (SimplexCategory.toTop.map a z) w), fun p => ?_⟩
  rw [orderNerveRealizationCoordinates_blend, hz, hs, hw, hj,
    orderNerveRealizationCoordinates_vertex]

noncomputable def orderNerveRealizationCone {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) (t : I) (x : orderNerveRealization P) :
    orderNerveRealization P := (orderNerveRealization_cone_exists v hv t x).choose

theorem orderNerveRealizationCone_coordinates {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) (t : I) (x : orderNerveRealization P) (p : P) :
    orderNerveRealizationCoordinates P (orderNerveRealizationCone v hv t x) p =
      (1 - (t : ℝ)) * orderNerveRealizationCoordinates P x p +
      (t : ℝ) * (if v = p then 1 else 0) :=
  (orderNerveRealization_cone_exists v hv t x).choose_spec p

theorem orderNerveRealizationCone_continuous {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) :
    Continuous (fun tx : I × orderNerveRealization P =>
      orderNerveRealizationCone v hv tx.1 tx.2) := by
  refine (orderNerveRealization_continuous_prod_iff P _).mpr fun n s => ?_
  obtain ⟨m, u, a, j, hs, hj⟩ := orderNerveSimplex_extend_vertex s v fun i => hv (s.obj i)
  obtain ⟨w, hw⟩ := orderNerveRealizationVertex_mem_simplex u j
  rw [show (fun tx : I × SimplexCategory.toTop.obj n =>
      orderNerveRealizationCone v hv tx.1 (orderNerveRealizationSimplex P s tx.2)) =
      fun tx => orderNerveRealizationSimplex P u
        (topologicalSimplexBlend tx.1 (SimplexCategory.toTop.map a tx.2) w) by
    funext tx; apply orderNerveRealizationCoordinates_injective P; funext p
    have hz : orderNerveRealizationSimplex P u (SimplexCategory.toTop.map a tx.2) =
        orderNerveRealizationSimplex P ((nerve P).map a.op u) tx.2 :=
      congrArg (· tx.2) (orderNerveRealizationSimplex_operator P a u)
    rw [orderNerveRealizationCone_coordinates, orderNerveRealizationCoordinates_blend,
      hz, hs, hw, hj, orderNerveRealizationCoordinates_vertex]]
  exact (orderNerveRealizationSimplex P u).hom.continuous.comp
    (topologicalSimplexBlend_continuous.comp
      (continuous_fst.prodMk (((SimplexCategory.toTop.map a).hom.continuous.comp
        continuous_snd).prodMk continuous_const)))

@[simp] theorem orderNerveRealizationCone_zero {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) (x : orderNerveRealization P) :
    orderNerveRealizationCone v hv 0 x = x := by
  apply orderNerveRealizationCoordinates_injective P; funext p
  simp [orderNerveRealizationCone_coordinates]

@[simp] theorem orderNerveRealizationCone_one {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) (x : orderNerveRealization P) :
    orderNerveRealizationCone v hv 1 x = orderNerveRealizationVertex v := by
  apply orderNerveRealizationCoordinates_injective P; funext p
  simp [orderNerveRealizationCone_coordinates, orderNerveRealizationCoordinates_vertex]

theorem orderNerveRealization_contractible_of_comparable {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) : ContractibleSpace (orderNerveRealization P) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨orderNerveRealizationVertex v, ⟨{
    toFun := fun tx => orderNerveRealizationCone v hv tx.1 tx.2
    continuous_toFun := orderNerveRealizationCone_continuous v hv
    map_zero_left := orderNerveRealizationCone_zero v hv
    map_one_left := orderNerveRealizationCone_one v hv }⟩⟩

end FiniteChains.Comb
