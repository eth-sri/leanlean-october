module

public import RequestProject.OrderNerveTightChainMap
public import RequestProject.TopologicalSingular.SmallRefinement
public import RequestProject.OrderNerveGradedBoundary

@[expose] public section

noncomputable section

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

def orderRefinementSmall (P : Type) [PartialOrder P] (n : ℕ) :=
  (smallRefinement _ (orderNerveRealizationOpenStar_isOpen P)
    (orderNerveRealizationOpenStar_cover P) n).codRestrict _
      (smallRefinement_mem_small _ _ _ n)

theorem orderRefinementSmall_boundary (n : ℕ) (c : Chain (orderNerveRealization P) _) :
    smallBoundary _ n (orderRefinementSmall P _ c) =
      orderRefinementSmall P n (boundary n c) := by
  apply Subtype.ext
  apply smallRefinement_boundary

def orderSingularToNerve (P : Type) [PartialOrder P] (n : ℕ) :=
  (orderTightToNerve P n).comp (orderRefinementSmall P n)

theorem orderSingularToNerve_boundary (n : ℕ) (c : Chain (orderNerveRealization P) _) :
    Nerve.bdry (orderSingularToNerve P (n + 1) c) =
      orderSingularToNerve P n (boundary n c) := by
  erw [orderTightToNerve_boundary, orderRefinementSmall_boundary]; rfl

theorem orderSingularToNerve_zero_boundary (c : Chain (orderNerveRealization P) 0) :
    Nerve.bdry (orderSingularToNerve P 0 c) =
      augmentation c • FreeAbelianGroup.of ([]) := by
  solve_by_elim [orderSmallToNerve0_boundary]

variable (n : ℕ)

variable (c : Chain (orderNerveRealization P) n)

theorem orderSingularToNerve_length :
    Nerve.lengthProjection (n + 1) (orderSingularToNerve P n c) = orderSingularToNerve P n c :=
  orderTightToNerve_length n _

theorem orderSingularToNerve_mem_inc :
    orderSingularToNerve P n c ∈ Nerve.Inc P := orderTightToNerve_mem_inc n _

theorem orderSingularToNerve_supported (A : Set P)
    {c : Chain (orderNerveRealization P) n}
    (hc : c ∈ subChains (orderNerveRealizationSubcomplex P A) n) :
    orderSingularToNerve P n c ∈ Nerve.IncOn A :=
  orderTightToNerve_supported n A _ (smallRefinement_support _ _ _ n _ hc)

/-- The return map on the original simplicial chains. -/
def orderNerveRoundTrip (P : Type) [PartialOrder P] (n : ℕ) :
    (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P :=
  (orderSingularToNerve P n).comp ((orderNerveExplicitSingularMap P).f n).hom

variable (n : ℕ)

theorem orderNerveRoundTrip_boundary (c : ComposableArrows P _ →₀ ℤ) :
    Nerve.bdry (orderNerveRoundTrip P (n + 1) c) =
      orderNerveRoundTrip P n
        ((AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom c) := by
  have he := congrArg (fun f => f c) ((orderNerveExplicitSingularMap P).comm _ n)
  erw [complex_d, AlternatingFaceMapComplex.obj_d_eq] at he
  erw [orderSingularToNerve_boundary]
  solve_by_elim

theorem orderNerveRoundTrip_supported (s : ComposableArrows P n) :
    orderNerveRoundTrip P n (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj) := by
  apply orderSingularToNerve_supported
  erw [orderNerveExplicitSingularMap_single]; exact single_mem_subChains _ n _ 1 (orderNerveSingularSimplex_supported _ s (fun i => ⟨i, rfl⟩))

theorem orderNerveRoundTrip_zero_boundary (c : ComposableArrows P 0 →₀ ℤ) :
    Nerve.bdry (orderNerveRoundTrip P 0 c) = Nerve.bdry (orderNerveGradedEncode 0 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single s r =>
    change Nerve.bdry (orderSingularToNerve P 0 ((orderNerveExplicitSingularMap P).f 0 _)) = _
    erw [orderNerveExplicitSingularMap_single, orderSingularToNerve_zero_boundary,
      augmentation_single, orderNerveGradedEncode_single, map_zsmul, Nerve.bdry_of]
    rfl

end FiniteChains.Comb
