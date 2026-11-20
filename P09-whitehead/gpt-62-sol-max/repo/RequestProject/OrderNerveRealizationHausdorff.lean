module

public import RequestProject.OrderNerveRealizationFaceReduction
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section


namespace FiniteChains.Comb
open CategoryTheory
open scoped Classical

/-- The actual global barycentric-coordinate map of the poset-nerve realization. -/
noncomputable def orderNerveRealizationCoordinates (P : Type) [PartialOrder P] :
    C(orderNerveRealization P, P → ℝ) where
  toFun x p := orderNerveAffineRealization (fun q => if q = p then 1 else 0) x
  continuous_toFun := continuous_pi (fun p =>
    (orderNerveAffineRealization (fun q => if q = p then 1 else 0)).hom.continuous)

theorem orderNerveRealizationCoordinates_simplex {P : Type} [PartialOrder P]
    {n : SimplexCategory} (s : (nerve P).obj (Opposite.op n))
    (z : SimplexCategory.toTop.obj n) (p : P) :
    orderNerveRealizationCoordinates P (orderNerveRealizationSimplex P s z) p =
      orderNerveAffineSimplex (fun q => if q = p then 1 else 0) s z :=
  orderNerveAffineRealization_simplex _ s z

/-- Global barycentric coordinates separate all points of the actual realization. -/
theorem orderNerveRealizationCoordinates_injective (P : Type) [PartialOrder P] :
    Function.Injective (orderNerveRealizationCoordinates P) := by
  classical
  intro x y h
  obtain ⟨n, s, z, hz, hx⟩ := orderNerveRealization_interior_cover P x
  obtain ⟨m, t, w, hw, hy⟩ := orderNerveRealization_interior_cover P y
  have hv : ∀ p, orderNerveAffineSimplex (fun q => if q = p then 1 else 0) s.val z =
      orderNerveAffineSimplex (fun q => if q = p then 1 else 0) t.val w := by
    intro p
    simpa only [← hx, ← hy, orderNerveRealizationCoordinates_simplex] using congrFun h p
  have hrange : Set.range s.val.obj = Set.range t.val.obj := by
    ext p
    rw [← orderNerveAffineSimplex_indicator_pos_iff s.val z hz p,
      ← orderNerveAffineSimplex_indicator_pos_iff t.val w hw p, hv p]
  obtain ⟨rfl, rfl⟩ := orderNerveNondegenerate_eq_of_range s t hrange
  have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property
  have hzw : z = w := by
    apply ULift.ext
    apply Convexity.StdSimplex.ext
    apply Finsupp.ext
    intro i
    exact (orderNerveAffineSimplex_indicator s.val hs i z).symm.trans
      ((hv (s.val.obj i)).trans (orderNerveAffineSimplex_indicator s.val hs i w))
  exact hx.symm.trans ((congrArg (orderNerveRealizationSimplex P s.val) hzw).trans hy)

/-- The actual geometric realization of every poset nerve is Hausdorff. -/
instance orderNerveRealization_t2Space (P : Type) [PartialOrder P] :
    T2Space (orderNerveRealization P) :=
  T2Space.of_injective_continuous (orderNerveRealizationCoordinates_injective P)
    (orderNerveRealizationCoordinates P).continuous

/-- Nondegenerate realization simplices are closed embeddings of their compact domains. -/
theorem orderNerveRealization_nonDegenerate_isClosedEmbedding {P : Type} [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    Topology.IsClosedEmbedding (orderNerveRealizationSimplex P s.val) := by
  haveI : CompactSpace (SimplexCategory.toTop.obj (SimplexCategory.mk n)) :=
    inferInstanceAs (CompactSpace (ULift.{0} (Convexity.StdSimplex ℝ (Fin (n + 1)))))
  exact (orderNerveRealizationSimplex P s.val).hom.continuous.isClosedEmbedding
    (orderNerveRealizationSimplex_injective s.val
      ((PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property))

end FiniteChains.Comb
