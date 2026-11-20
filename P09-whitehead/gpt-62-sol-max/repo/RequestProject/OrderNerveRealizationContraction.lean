module

public import RequestProject.TopologicalSingular.SimplexCoordinates
public import RequestProject.OrderNerveRealizationOpenStars
public import RequestProject.OrderNerveRealizationPaths
public import Mathlib.Topology.Homotopy.Contractible

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped unitInterval Classical

/-- Compact parameter families are continuous on a realization exactly when they
are continuous on each of its simplices. -/
theorem orderNerveRealization_continuous_prod_iff (P : Type) [PartialOrder P]
    {T X : Type*} [TopologicalSpace T] [LocallyCompactSpace T] [TopologicalSpace X]
    (f : T × orderNerveRealization P → X) :
    Continuous f ↔ ∀ (n : SimplexCategory) (s : (nerve P).obj (Opposite.op n)),
      Continuous (fun p : T × SimplexCategory.toTop.obj n =>
        f (p.1, orderNerveRealizationSimplex P s p.2)) := by
  constructor
  · fun_prop
  · intro h
    have ht : ∀ x, Continuous (fun t  => f (t, x)) := by
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

/-- Two simplices whose vertices are pairwise cross-comparable lie in an actual
common simplex, with explicit simplex operators for both inclusions. -/
theorem orderNerveSimplex_common {P : Type} [PartialOrder P] {n k : SimplexCategory}
    (s : (nerve P).obj (Opposite.op n)) (t : (nerve P).obj (Opposite.op k))
    (hc : ∀ i j, s.obj i ≤ t.obj j ∨ t.obj j ≤ s.obj i) :
    ∃ (m : SimplexCategory) (u : (nerve P).obj (Opposite.op m))
      (a : n ⟶ m) (b : k ⟶ m),
      (nerve P).map a.op u = s ∧ (nerve P).map b.op u = t := by
  classical
  let A := Set.range s.obj ∪ Set.range t.obj
  have mono {d : SimplexCategory} (r : (nerve P).obj (Opposite.op d)) : Monotone r.obj :=
    fun _ _ h => leOfHom (r.map (homOfLE h))
  have hA : IsChain (· ≤ ·) A := isChain_union.mpr
    ⟨(mono s).isChain_range, (mono t).isChain_range, by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j⟩
  letI := ((Set.finite_range s.obj).union (Set.finite_range t.obj)).fintype
  letI := hA.lt_of_le.linearOrder
  letI : Nonempty A := ⟨⟨s.obj 0, Or.inl ⟨0, rfl⟩⟩⟩
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fintype.card_pos (α := A)))
  let e := Fintype.orderIsoFinOfCardEq A hr
  let u := (monotone_subtypeVal.comp e.monotone).functor
  have factor {d : SimplexCategory} (v : (nerve P).obj (Opposite.op d)) (h : ∀ i, v.obj i ∈ A) :
      ∃ a : d ⟶ ⦋r⦌, (nerve P).map a.op u = v :=
    ⟨SimplexCategory.mkHom ⟨fun i => e.symm ⟨v.obj i, h i⟩,
      fun _ _ hle => e.symm.monotone (mono v hle)⟩,
      CategoryTheory.Functor.ext fun i => congrArg Subtype.val (e.apply_symm_apply ⟨v.obj i, h i⟩)⟩
  obtain ⟨a, ha⟩ := factor s (fun i => Or.inl ⟨i, rfl⟩)
  obtain ⟨b, hb⟩ := factor t (fun i => Or.inr ⟨i, rfl⟩)
  exact ⟨⦋r⦌, u, a, b, ha, hb⟩

/-- Straight-line interpolation inside a topological simplex. -/
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
  unfold topologicalSimplexBlend
  fun_prop

theorem orderNerveAffineSimplex_blend {P : Type} [PartialOrder P] (v : P → ℝ)
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (t : I) (z w : SimplexCategory.toTop.obj n) :
    orderNerveAffineSimplex v s (topologicalSimplexBlend t z w) =
      (1 - (t : ℝ)) * orderNerveAffineSimplex v s z +
        (t : ℝ) * orderNerveAffineSimplex v s w := by
  simp [orderNerveAffineSimplex, ContinuousMap.coe_mk, topologicalSimplexBlend, TopologicalSingular.simplexCoordinates_symm_weights_apply, TopologicalSingular.simplexCoordinates_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]

/-- The affine interpolation formula in global coordinates. -/
theorem orderNerveRealizationCoordinates_blend {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (t : I) (z w : SimplexCategory.toTop.obj n) (p : P) :
    orderNerveRealizationCoordinates P
        (orderNerveRealizationSimplex P s (topologicalSimplexBlend t z w)) p =
      (1 - (t : ℝ)) * orderNerveRealizationCoordinates P
        (orderNerveRealizationSimplex P s z) p +
      (t : ℝ) * orderNerveRealizationCoordinates P
        (orderNerveRealizationSimplex P s w) p := by
  simp only [orderNerveRealizationCoordinates_simplex, orderNerveAffineSimplex_blend]

section Contiguous

variable {P Q : Type} [PartialOrder P] [PartialOrder Q]
variable (f : P → Q) (hf : Monotone f) (g : P → Q) (hg : Monotone g)
variable (hc : ∀ p q, p ≤ q ∨ q ≤ p → f p ≤ g q ∨ g q ≤ f p)
include hc

/-- Cross-comparability gives a common target simplex for both actual maps
on each source simplex. This is stronger than pointwise comparison. -/
theorem orderNerveSimplex_common_maps {n : SimplexCategory}
    (s : (nerve P).obj (Opposite.op n)) :
    ∃ (m : SimplexCategory) (u : (nerve Q).obj (Opposite.op m))
      (a b : n ⟶ m),
      (∀ z, orderNerveRealizationSimplex Q u (SimplexCategory.toTop.map a z) =
        orderNerveRealizationMap f hf (orderNerveRealizationSimplex P s z)) ∧
      (∀ z, orderNerveRealizationSimplex Q u (SimplexCategory.toTop.map b z) =
        orderNerveRealizationMap g hg (orderNerveRealizationSimplex P s z)) := by
  have hcross : ∀ i j, f (s.obj i) ≤ g (s.obj j) ∨ g (s.obj j) ≤ f (s.obj i) := by
    intro i j
    apply hc
    rcases le_total i j with h | h
    · exact Or.inl (leOfHom (s.map (homOfLE h)))
    · exact Or.inr (leOfHom (s.map (homOfLE h)))
  obtain ⟨m, u, a, b, ha, hb⟩ := orderNerveSimplex_common
    ((nerveMap hf.functor).app _ s) ((nerveMap hg.functor).app _ s) hcross
  have factor (k : P → Q) (hk : Monotone k) (c : n ⟶ m)
      (h : (nerve Q).map c.op u = (nerveMap hk.functor).app _ s) (z : SimplexCategory.toTop.obj n) :
      orderNerveRealizationSimplex Q u (SimplexCategory.toTop.map c z) =
        orderNerveRealizationMap k hk (orderNerveRealizationSimplex P s z) := by
    rw [orderNerveRealizationSimplex_operator, h, orderNerveRealizationSimplex_natural]
  exact ⟨m, u, a, b, factor f hf a ha, factor g hg b hb⟩

theorem orderNerveRealization_blend_exists (t : I) (x : orderNerveRealization P) :
    ∃ y : orderNerveRealization Q, ∀ q,
      orderNerveRealizationCoordinates Q y q =
        (1 - (t : ℝ)) * orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) q +
        (t : ℝ) * orderNerveRealizationCoordinates Q (orderNerveRealizationMap g hg x) q := by
  obtain ⟨n, s, z, rfl⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  obtain ⟨m, u, a, b, ha, hb⟩ := orderNerveSimplex_common_maps f hf g hg hc s
  refine ⟨orderNerveRealizationSimplex Q u
    (topologicalSimplexBlend t (SimplexCategory.toTop.map a z) (SimplexCategory.toTop.map b z)),
    fun q => ?_⟩
  rw [orderNerveRealizationCoordinates_blend, ha, hb]

/-- The unique affine interpolation, defined in global barycentric coordinates. -/
noncomputable def orderNerveRealizationBlend (t : I) (x : orderNerveRealization P) :
    orderNerveRealization Q := (orderNerveRealization_blend_exists f hf g hg hc t x).choose

theorem orderNerveRealizationBlend_coordinates (t : I) (x : orderNerveRealization P) (q : Q) :
    orderNerveRealizationCoordinates Q (orderNerveRealizationBlend f hf g hg hc t x) q =
      (1 - (t : ℝ)) * orderNerveRealizationCoordinates Q (orderNerveRealizationMap f hf x) q +
      (t : ℝ) * orderNerveRealizationCoordinates Q (orderNerveRealizationMap g hg x) q :=
  (orderNerveRealization_blend_exists f hf g hg hc t x).choose_spec q

/-- Joint continuity holds in the actual weak CW topology, including infinite posets. -/
theorem orderNerveRealizationBlend_continuous :
    Continuous (fun tx : I × orderNerveRealization P =>
      orderNerveRealizationBlend f hf g hg hc tx.1 tx.2) := by
  apply (orderNerveRealization_continuous_prod_iff P _).mpr
  intro n s
  obtain ⟨m, u, a, b, ha, hb⟩ := orderNerveSimplex_common_maps f hf g hg hc s
  have he : (fun tx : I × SimplexCategory.toTop.obj n =>
      orderNerveRealizationBlend f hf g hg hc tx.1 (orderNerveRealizationSimplex P s tx.2)) =
      (fun tx => orderNerveRealizationSimplex Q u
        (topologicalSimplexBlend tx.1 (SimplexCategory.toTop.map a tx.2)
          (SimplexCategory.toTop.map b tx.2))) := by
    funext tx
    apply orderNerveRealizationCoordinates_injective Q
    funext q
    rw [orderNerveRealizationBlend_coordinates, orderNerveRealizationCoordinates_blend, ha, hb]
  rw [he]
  exact (orderNerveRealizationSimplex Q u).hom.continuous.comp
    (topologicalSimplexBlend_continuous.comp
      (continuous_fst.prodMk
        (((SimplexCategory.toTop.map a).hom.continuous.comp continuous_snd).prodMk
          ((SimplexCategory.toTop.map b).hom.continuous.comp continuous_snd))))

@[simp] theorem orderNerveRealizationBlend_zero (x : orderNerveRealization P) :
    orderNerveRealizationBlend f hf g hg hc 0 x = orderNerveRealizationMap f hf x := by
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  simp [orderNerveRealizationBlend_coordinates]

@[simp] theorem orderNerveRealizationBlend_one (x : orderNerveRealization P) :
    orderNerveRealizationBlend f hf g hg hc 1 x = orderNerveRealizationMap g hg x := by
  apply orderNerveRealizationCoordinates_injective Q
  funext q
  simp [orderNerveRealizationBlend_coordinates]

/-- A concrete topological homotopy between maps with cross-comparable images. -/
noncomputable def orderNerveRealizationContiguousHomotopy :
    ContinuousMap.Homotopy
      (⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ :
        C(orderNerveRealization P, orderNerveRealization Q))
      ⟨orderNerveRealizationMap g hg, (orderNerveRealizationMap g hg).hom.continuous⟩ where
  toFun tx := orderNerveRealizationBlend f hf g hg hc tx.1 tx.2
  continuous_toFun := orderNerveRealizationBlend_continuous f hf g hg hc
  map_zero_left := orderNerveRealizationBlend_zero f hf g hg hc
  map_one_left := orderNerveRealizationBlend_one f hf g hg hc

end Contiguous

section Cone
variable {P : Type} [PartialOrder P] (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p)

/-- The cone is the affine interpolation from the identity to a constant vertex. -/
noncomputable def orderNerveRealizationCone : I → orderNerveRealization P → orderNerveRealization P :=
  orderNerveRealizationBlend id monotone_id (fun _ => v) monotone_const (fun p _ _ => hv p)

theorem orderNerveRealizationCone_coordinates (t : I) (x : orderNerveRealization P) (p : P) :
    orderNerveRealizationCoordinates P (orderNerveRealizationCone v hv t x) p =
      (1 - (t : ℝ)) * orderNerveRealizationCoordinates P x p +
      (t : ℝ) * (if v = p then 1 else 0) := by
  simp [orderNerveRealizationCone, orderNerveRealizationBlend_coordinates,
    orderNerveRealizationMap_id, orderNerveRealizationCoordinates_vertex]

theorem orderNerveRealizationCone_continuous :
    Continuous (fun tx : I × orderNerveRealization P => orderNerveRealizationCone v hv tx.1 tx.2) :=
  orderNerveRealizationBlend_continuous _ _ _ _ _

@[simp] theorem orderNerveRealizationCone_zero (x : orderNerveRealization P) :
    orderNerveRealizationCone v hv 0 x = x := by
  simp [orderNerveRealizationCone, orderNerveRealizationMap_id]

@[simp] theorem orderNerveRealizationCone_one (x : orderNerveRealization P) :
    orderNerveRealizationCone v hv 1 x = orderNerveRealizationVertex v := by
  simp [orderNerveRealizationCone]

end Cone

/-- A poset with a universally comparable vertex has contractible realization. -/
theorem orderNerveRealization_contractible_of_comparable {P : Type} [PartialOrder P]
    (v : P) (hv : ∀ p, p ≤ v ∨ v ≤ p) : ContractibleSpace (orderNerveRealization P) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨orderNerveRealizationVertex v, ⟨?_⟩⟩
  exact
    { toFun := fun tx => orderNerveRealizationCone v hv tx.1 tx.2
      continuous_toFun := orderNerveRealizationCone_continuous v hv
      map_zero_left := (orderNerveRealizationCone_zero v hv)
      map_one_left := (orderNerveRealizationCone_one v hv) }

end FiniteChains.Comb
